import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1827893074603 : Nat.Prime 1827893074603 := by
  apply lucas_primality 1827893074603 (3 : ZMod 1827893074603)
  ·
      have fermat_0 : (3 : ZMod 1827893074603) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1827893074603) ^ 3 = 27 := by
        calc
          (3 : ZMod 1827893074603) ^ 3 = (3 : ZMod 1827893074603) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1 * (3 : ZMod 1827893074603) ^ 1) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1827893074603) ^ 6 = 729 := by
        calc
          (3 : ZMod 1827893074603) ^ 6 = (3 : ZMod 1827893074603) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3 * (3 : ZMod 1827893074603) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1827893074603) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 1827893074603) ^ 13 = (3 : ZMod 1827893074603) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 6 * (3 : ZMod 1827893074603) ^ 6) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1827893074603) ^ 26 = 713972753726 := by
        calc
          (3 : ZMod 1827893074603) ^ 26 = (3 : ZMod 1827893074603) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 13 * (3 : ZMod 1827893074603) ^ 13 := by rw [pow_add]
          _ = 713972753726 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1827893074603) ^ 53 = 333397379334 := by
        calc
          (3 : ZMod 1827893074603) ^ 53 = (3 : ZMod 1827893074603) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 26 * (3 : ZMod 1827893074603) ^ 26) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 333397379334 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1827893074603) ^ 106 = 1052657364533 := by
        calc
          (3 : ZMod 1827893074603) ^ 106 = (3 : ZMod 1827893074603) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 53 * (3 : ZMod 1827893074603) ^ 53 := by rw [pow_add]
          _ = 1052657364533 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1827893074603) ^ 212 = 116492844699 := by
        calc
          (3 : ZMod 1827893074603) ^ 212 = (3 : ZMod 1827893074603) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 106 * (3 : ZMod 1827893074603) ^ 106 := by rw [pow_add]
          _ = 116492844699 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1827893074603) ^ 425 = 878132897050 := by
        calc
          (3 : ZMod 1827893074603) ^ 425 = (3 : ZMod 1827893074603) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 212 * (3 : ZMod 1827893074603) ^ 212) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 878132897050 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1827893074603) ^ 851 = 1489095973420 := by
        calc
          (3 : ZMod 1827893074603) ^ 851 = (3 : ZMod 1827893074603) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 425 * (3 : ZMod 1827893074603) ^ 425) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1489095973420 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1827893074603) ^ 1702 = 1327040218497 := by
        calc
          (3 : ZMod 1827893074603) ^ 1702 = (3 : ZMod 1827893074603) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 851 * (3 : ZMod 1827893074603) ^ 851 := by rw [pow_add]
          _ = 1327040218497 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1827893074603) ^ 3404 = 1087994007237 := by
        calc
          (3 : ZMod 1827893074603) ^ 3404 = (3 : ZMod 1827893074603) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 1702 * (3 : ZMod 1827893074603) ^ 1702 := by rw [pow_add]
          _ = 1087994007237 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1827893074603) ^ 6809 = 286142460750 := by
        calc
          (3 : ZMod 1827893074603) ^ 6809 = (3 : ZMod 1827893074603) ^ (3404 + 3404 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 3404 * (3 : ZMod 1827893074603) ^ 3404) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 286142460750 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1827893074603) ^ 13618 = 627839301746 := by
        calc
          (3 : ZMod 1827893074603) ^ 13618 = (3 : ZMod 1827893074603) ^ (6809 + 6809) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 6809 * (3 : ZMod 1827893074603) ^ 6809 := by rw [pow_add]
          _ = 627839301746 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1827893074603) ^ 27237 = 1727751066069 := by
        calc
          (3 : ZMod 1827893074603) ^ 27237 = (3 : ZMod 1827893074603) ^ (13618 + 13618 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 13618 * (3 : ZMod 1827893074603) ^ 13618) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1727751066069 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1827893074603) ^ 54475 = 90525857953 := by
        calc
          (3 : ZMod 1827893074603) ^ 54475 = (3 : ZMod 1827893074603) ^ (27237 + 27237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 27237 * (3 : ZMod 1827893074603) ^ 27237) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 90525857953 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1827893074603) ^ 108950 = 1040558520471 := by
        calc
          (3 : ZMod 1827893074603) ^ 108950 = (3 : ZMod 1827893074603) ^ (54475 + 54475) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 54475 * (3 : ZMod 1827893074603) ^ 54475 := by rw [pow_add]
          _ = 1040558520471 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1827893074603) ^ 217901 = 896694745918 := by
        calc
          (3 : ZMod 1827893074603) ^ 217901 = (3 : ZMod 1827893074603) ^ (108950 + 108950 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 108950 * (3 : ZMod 1827893074603) ^ 108950) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 896694745918 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1827893074603) ^ 435803 = 291341760105 := by
        calc
          (3 : ZMod 1827893074603) ^ 435803 = (3 : ZMod 1827893074603) ^ (217901 + 217901 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 217901 * (3 : ZMod 1827893074603) ^ 217901) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 291341760105 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1827893074603) ^ 871607 = 303319388781 := by
        calc
          (3 : ZMod 1827893074603) ^ 871607 = (3 : ZMod 1827893074603) ^ (435803 + 435803 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 435803 * (3 : ZMod 1827893074603) ^ 435803) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 303319388781 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1827893074603) ^ 1743214 = 513957068256 := by
        calc
          (3 : ZMod 1827893074603) ^ 1743214 = (3 : ZMod 1827893074603) ^ (871607 + 871607) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 871607 * (3 : ZMod 1827893074603) ^ 871607 := by rw [pow_add]
          _ = 513957068256 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1827893074603) ^ 3486429 = 1334389710945 := by
        calc
          (3 : ZMod 1827893074603) ^ 3486429 = (3 : ZMod 1827893074603) ^ (1743214 + 1743214 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1743214 * (3 : ZMod 1827893074603) ^ 1743214) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1334389710945 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1827893074603) ^ 6972858 = 998376219190 := by
        calc
          (3 : ZMod 1827893074603) ^ 6972858 = (3 : ZMod 1827893074603) ^ (3486429 + 3486429) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3486429 * (3 : ZMod 1827893074603) ^ 3486429 := by rw [pow_add]
          _ = 998376219190 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1827893074603) ^ 13945717 = 1643852664065 := by
        calc
          (3 : ZMod 1827893074603) ^ 13945717 = (3 : ZMod 1827893074603) ^ (6972858 + 6972858 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 6972858 * (3 : ZMod 1827893074603) ^ 6972858) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1643852664065 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1827893074603) ^ 27891434 = 383178498404 := by
        calc
          (3 : ZMod 1827893074603) ^ 27891434 = (3 : ZMod 1827893074603) ^ (13945717 + 13945717) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 13945717 * (3 : ZMod 1827893074603) ^ 13945717 := by rw [pow_add]
          _ = 383178498404 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1827893074603) ^ 55782869 = 921104808648 := by
        calc
          (3 : ZMod 1827893074603) ^ 55782869 = (3 : ZMod 1827893074603) ^ (27891434 + 27891434 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 27891434 * (3 : ZMod 1827893074603) ^ 27891434) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 921104808648 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1827893074603) ^ 111565739 = 768421366891 := by
        calc
          (3 : ZMod 1827893074603) ^ 111565739 = (3 : ZMod 1827893074603) ^ (55782869 + 55782869 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 55782869 * (3 : ZMod 1827893074603) ^ 55782869) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 768421366891 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1827893074603) ^ 223131478 = 1315546147309 := by
        calc
          (3 : ZMod 1827893074603) ^ 223131478 = (3 : ZMod 1827893074603) ^ (111565739 + 111565739) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 111565739 * (3 : ZMod 1827893074603) ^ 111565739 := by rw [pow_add]
          _ = 1315546147309 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1827893074603) ^ 446262957 = 1469624408852 := by
        calc
          (3 : ZMod 1827893074603) ^ 446262957 = (3 : ZMod 1827893074603) ^ (223131478 + 223131478 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 223131478 * (3 : ZMod 1827893074603) ^ 223131478) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1469624408852 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1827893074603) ^ 892525915 = 1194279463408 := by
        calc
          (3 : ZMod 1827893074603) ^ 892525915 = (3 : ZMod 1827893074603) ^ (446262957 + 446262957 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 446262957 * (3 : ZMod 1827893074603) ^ 446262957) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1194279463408 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1827893074603) ^ 1785051830 = 1687138229961 := by
        calc
          (3 : ZMod 1827893074603) ^ 1785051830 = (3 : ZMod 1827893074603) ^ (892525915 + 892525915) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 892525915 * (3 : ZMod 1827893074603) ^ 892525915 := by rw [pow_add]
          _ = 1687138229961 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 1827893074603) ^ 3570103661 = 1573323887128 := by
        calc
          (3 : ZMod 1827893074603) ^ 3570103661 = (3 : ZMod 1827893074603) ^ (1785051830 + 1785051830 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1785051830 * (3 : ZMod 1827893074603) ^ 1785051830) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1573323887128 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 1827893074603) ^ 7140207322 = 908603883391 := by
        calc
          (3 : ZMod 1827893074603) ^ 7140207322 = (3 : ZMod 1827893074603) ^ (3570103661 + 3570103661) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3570103661 * (3 : ZMod 1827893074603) ^ 3570103661 := by rw [pow_add]
          _ = 908603883391 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 1827893074603) ^ 14280414645 = 387106584686 := by
        calc
          (3 : ZMod 1827893074603) ^ 14280414645 = (3 : ZMod 1827893074603) ^ (7140207322 + 7140207322 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 7140207322 * (3 : ZMod 1827893074603) ^ 7140207322) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 387106584686 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 1827893074603) ^ 28560829290 = 455029379180 := by
        calc
          (3 : ZMod 1827893074603) ^ 28560829290 = (3 : ZMod 1827893074603) ^ (14280414645 + 14280414645) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 14280414645 * (3 : ZMod 1827893074603) ^ 14280414645 := by rw [pow_add]
          _ = 455029379180 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 1827893074603) ^ 57121658581 = 1112746418934 := by
        calc
          (3 : ZMod 1827893074603) ^ 57121658581 = (3 : ZMod 1827893074603) ^ (28560829290 + 28560829290 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 28560829290 * (3 : ZMod 1827893074603) ^ 28560829290) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1112746418934 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 1827893074603) ^ 114243317162 = 598827821165 := by
        calc
          (3 : ZMod 1827893074603) ^ 114243317162 = (3 : ZMod 1827893074603) ^ (57121658581 + 57121658581) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 57121658581 * (3 : ZMod 1827893074603) ^ 57121658581 := by rw [pow_add]
          _ = 598827821165 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 1827893074603) ^ 228486634325 = 136116766256 := by
        calc
          (3 : ZMod 1827893074603) ^ 228486634325 = (3 : ZMod 1827893074603) ^ (114243317162 + 114243317162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 114243317162 * (3 : ZMod 1827893074603) ^ 114243317162) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 136116766256 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 1827893074603) ^ 456973268650 = 765950922672 := by
        calc
          (3 : ZMod 1827893074603) ^ 456973268650 = (3 : ZMod 1827893074603) ^ (228486634325 + 228486634325) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 228486634325 * (3 : ZMod 1827893074603) ^ 228486634325 := by rw [pow_add]
          _ = 765950922672 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 1827893074603) ^ 913946537301 = 1827893074602 := by
        calc
          (3 : ZMod 1827893074603) ^ 913946537301 = (3 : ZMod 1827893074603) ^ (456973268650 + 456973268650 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 456973268650 * (3 : ZMod 1827893074603) ^ 456973268650) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1827893074602 := by rw [fermat_38]; decide
      have fermat_40 : (3 : ZMod 1827893074603) ^ 1827893074602 = 1 := by
        calc
          (3 : ZMod 1827893074603) ^ 1827893074602 = (3 : ZMod 1827893074603) ^ (913946537301 + 913946537301) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 913946537301 * (3 : ZMod 1827893074603) ^ 913946537301 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (15319, 1), (405857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (15319, 1), (405857, 1)] : List FactorBlock).map factorBlockValue).prod = 1827893074603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1827893074603) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1827893074603) ^ 3 = 27 := by
        calc
          (3 : ZMod 1827893074603) ^ 3 = (3 : ZMod 1827893074603) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1 * (3 : ZMod 1827893074603) ^ 1) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1827893074603) ^ 6 = 729 := by
        calc
          (3 : ZMod 1827893074603) ^ 6 = (3 : ZMod 1827893074603) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3 * (3 : ZMod 1827893074603) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1827893074603) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 1827893074603) ^ 13 = (3 : ZMod 1827893074603) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 6 * (3 : ZMod 1827893074603) ^ 6) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1827893074603) ^ 26 = 713972753726 := by
        calc
          (3 : ZMod 1827893074603) ^ 26 = (3 : ZMod 1827893074603) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 13 * (3 : ZMod 1827893074603) ^ 13 := by rw [pow_add]
          _ = 713972753726 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1827893074603) ^ 53 = 333397379334 := by
        calc
          (3 : ZMod 1827893074603) ^ 53 = (3 : ZMod 1827893074603) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 26 * (3 : ZMod 1827893074603) ^ 26) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 333397379334 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1827893074603) ^ 106 = 1052657364533 := by
        calc
          (3 : ZMod 1827893074603) ^ 106 = (3 : ZMod 1827893074603) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 53 * (3 : ZMod 1827893074603) ^ 53 := by rw [pow_add]
          _ = 1052657364533 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1827893074603) ^ 212 = 116492844699 := by
        calc
          (3 : ZMod 1827893074603) ^ 212 = (3 : ZMod 1827893074603) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 106 * (3 : ZMod 1827893074603) ^ 106 := by rw [pow_add]
          _ = 116492844699 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1827893074603) ^ 425 = 878132897050 := by
        calc
          (3 : ZMod 1827893074603) ^ 425 = (3 : ZMod 1827893074603) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 212 * (3 : ZMod 1827893074603) ^ 212) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 878132897050 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1827893074603) ^ 851 = 1489095973420 := by
        calc
          (3 : ZMod 1827893074603) ^ 851 = (3 : ZMod 1827893074603) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 425 * (3 : ZMod 1827893074603) ^ 425) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1489095973420 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1827893074603) ^ 1702 = 1327040218497 := by
        calc
          (3 : ZMod 1827893074603) ^ 1702 = (3 : ZMod 1827893074603) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 851 * (3 : ZMod 1827893074603) ^ 851 := by rw [pow_add]
          _ = 1327040218497 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1827893074603) ^ 3404 = 1087994007237 := by
        calc
          (3 : ZMod 1827893074603) ^ 3404 = (3 : ZMod 1827893074603) ^ (1702 + 1702) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 1702 * (3 : ZMod 1827893074603) ^ 1702 := by rw [pow_add]
          _ = 1087994007237 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1827893074603) ^ 6809 = 286142460750 := by
        calc
          (3 : ZMod 1827893074603) ^ 6809 = (3 : ZMod 1827893074603) ^ (3404 + 3404 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 3404 * (3 : ZMod 1827893074603) ^ 3404) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 286142460750 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1827893074603) ^ 13618 = 627839301746 := by
        calc
          (3 : ZMod 1827893074603) ^ 13618 = (3 : ZMod 1827893074603) ^ (6809 + 6809) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 6809 * (3 : ZMod 1827893074603) ^ 6809 := by rw [pow_add]
          _ = 627839301746 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1827893074603) ^ 27237 = 1727751066069 := by
        calc
          (3 : ZMod 1827893074603) ^ 27237 = (3 : ZMod 1827893074603) ^ (13618 + 13618 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 13618 * (3 : ZMod 1827893074603) ^ 13618) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1727751066069 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1827893074603) ^ 54475 = 90525857953 := by
        calc
          (3 : ZMod 1827893074603) ^ 54475 = (3 : ZMod 1827893074603) ^ (27237 + 27237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 27237 * (3 : ZMod 1827893074603) ^ 27237) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 90525857953 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1827893074603) ^ 108950 = 1040558520471 := by
        calc
          (3 : ZMod 1827893074603) ^ 108950 = (3 : ZMod 1827893074603) ^ (54475 + 54475) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 54475 * (3 : ZMod 1827893074603) ^ 54475 := by rw [pow_add]
          _ = 1040558520471 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1827893074603) ^ 217901 = 896694745918 := by
        calc
          (3 : ZMod 1827893074603) ^ 217901 = (3 : ZMod 1827893074603) ^ (108950 + 108950 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 108950 * (3 : ZMod 1827893074603) ^ 108950) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 896694745918 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1827893074603) ^ 435803 = 291341760105 := by
        calc
          (3 : ZMod 1827893074603) ^ 435803 = (3 : ZMod 1827893074603) ^ (217901 + 217901 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 217901 * (3 : ZMod 1827893074603) ^ 217901) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 291341760105 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1827893074603) ^ 871607 = 303319388781 := by
        calc
          (3 : ZMod 1827893074603) ^ 871607 = (3 : ZMod 1827893074603) ^ (435803 + 435803 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 435803 * (3 : ZMod 1827893074603) ^ 435803) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 303319388781 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1827893074603) ^ 1743214 = 513957068256 := by
        calc
          (3 : ZMod 1827893074603) ^ 1743214 = (3 : ZMod 1827893074603) ^ (871607 + 871607) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 871607 * (3 : ZMod 1827893074603) ^ 871607 := by rw [pow_add]
          _ = 513957068256 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1827893074603) ^ 3486429 = 1334389710945 := by
        calc
          (3 : ZMod 1827893074603) ^ 3486429 = (3 : ZMod 1827893074603) ^ (1743214 + 1743214 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1743214 * (3 : ZMod 1827893074603) ^ 1743214) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1334389710945 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1827893074603) ^ 6972858 = 998376219190 := by
        calc
          (3 : ZMod 1827893074603) ^ 6972858 = (3 : ZMod 1827893074603) ^ (3486429 + 3486429) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3486429 * (3 : ZMod 1827893074603) ^ 3486429 := by rw [pow_add]
          _ = 998376219190 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1827893074603) ^ 13945717 = 1643852664065 := by
        calc
          (3 : ZMod 1827893074603) ^ 13945717 = (3 : ZMod 1827893074603) ^ (6972858 + 6972858 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 6972858 * (3 : ZMod 1827893074603) ^ 6972858) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1643852664065 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1827893074603) ^ 27891434 = 383178498404 := by
        calc
          (3 : ZMod 1827893074603) ^ 27891434 = (3 : ZMod 1827893074603) ^ (13945717 + 13945717) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 13945717 * (3 : ZMod 1827893074603) ^ 13945717 := by rw [pow_add]
          _ = 383178498404 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1827893074603) ^ 55782869 = 921104808648 := by
        calc
          (3 : ZMod 1827893074603) ^ 55782869 = (3 : ZMod 1827893074603) ^ (27891434 + 27891434 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 27891434 * (3 : ZMod 1827893074603) ^ 27891434) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 921104808648 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1827893074603) ^ 111565739 = 768421366891 := by
        calc
          (3 : ZMod 1827893074603) ^ 111565739 = (3 : ZMod 1827893074603) ^ (55782869 + 55782869 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 55782869 * (3 : ZMod 1827893074603) ^ 55782869) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 768421366891 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1827893074603) ^ 223131478 = 1315546147309 := by
        calc
          (3 : ZMod 1827893074603) ^ 223131478 = (3 : ZMod 1827893074603) ^ (111565739 + 111565739) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 111565739 * (3 : ZMod 1827893074603) ^ 111565739 := by rw [pow_add]
          _ = 1315546147309 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1827893074603) ^ 446262957 = 1469624408852 := by
        calc
          (3 : ZMod 1827893074603) ^ 446262957 = (3 : ZMod 1827893074603) ^ (223131478 + 223131478 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 223131478 * (3 : ZMod 1827893074603) ^ 223131478) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1469624408852 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1827893074603) ^ 892525915 = 1194279463408 := by
        calc
          (3 : ZMod 1827893074603) ^ 892525915 = (3 : ZMod 1827893074603) ^ (446262957 + 446262957 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 446262957 * (3 : ZMod 1827893074603) ^ 446262957) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1194279463408 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 1827893074603) ^ 1785051830 = 1687138229961 := by
        calc
          (3 : ZMod 1827893074603) ^ 1785051830 = (3 : ZMod 1827893074603) ^ (892525915 + 892525915) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 892525915 * (3 : ZMod 1827893074603) ^ 892525915 := by rw [pow_add]
          _ = 1687138229961 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 1827893074603) ^ 3570103661 = 1573323887128 := by
        calc
          (3 : ZMod 1827893074603) ^ 3570103661 = (3 : ZMod 1827893074603) ^ (1785051830 + 1785051830 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1785051830 * (3 : ZMod 1827893074603) ^ 1785051830) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1573323887128 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 1827893074603) ^ 7140207322 = 908603883391 := by
        calc
          (3 : ZMod 1827893074603) ^ 7140207322 = (3 : ZMod 1827893074603) ^ (3570103661 + 3570103661) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3570103661 * (3 : ZMod 1827893074603) ^ 3570103661 := by rw [pow_add]
          _ = 908603883391 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 1827893074603) ^ 14280414645 = 387106584686 := by
        calc
          (3 : ZMod 1827893074603) ^ 14280414645 = (3 : ZMod 1827893074603) ^ (7140207322 + 7140207322 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 7140207322 * (3 : ZMod 1827893074603) ^ 7140207322) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 387106584686 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 1827893074603) ^ 28560829290 = 455029379180 := by
        calc
          (3 : ZMod 1827893074603) ^ 28560829290 = (3 : ZMod 1827893074603) ^ (14280414645 + 14280414645) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 14280414645 * (3 : ZMod 1827893074603) ^ 14280414645 := by rw [pow_add]
          _ = 455029379180 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 1827893074603) ^ 57121658581 = 1112746418934 := by
        calc
          (3 : ZMod 1827893074603) ^ 57121658581 = (3 : ZMod 1827893074603) ^ (28560829290 + 28560829290 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 28560829290 * (3 : ZMod 1827893074603) ^ 28560829290) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1112746418934 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 1827893074603) ^ 114243317162 = 598827821165 := by
        calc
          (3 : ZMod 1827893074603) ^ 114243317162 = (3 : ZMod 1827893074603) ^ (57121658581 + 57121658581) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 57121658581 * (3 : ZMod 1827893074603) ^ 57121658581 := by rw [pow_add]
          _ = 598827821165 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 1827893074603) ^ 228486634325 = 136116766256 := by
        calc
          (3 : ZMod 1827893074603) ^ 228486634325 = (3 : ZMod 1827893074603) ^ (114243317162 + 114243317162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 114243317162 * (3 : ZMod 1827893074603) ^ 114243317162) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 136116766256 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 1827893074603) ^ 456973268650 = 765950922672 := by
        calc
          (3 : ZMod 1827893074603) ^ 456973268650 = (3 : ZMod 1827893074603) ^ (228486634325 + 228486634325) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 228486634325 * (3 : ZMod 1827893074603) ^ 228486634325 := by rw [pow_add]
          _ = 765950922672 := by rw [factor_0_37]; decide
      have factor_0_39 : (3 : ZMod 1827893074603) ^ 913946537301 = 1827893074602 := by
        calc
          (3 : ZMod 1827893074603) ^ 913946537301 = (3 : ZMod 1827893074603) ^ (456973268650 + 456973268650 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 456973268650 * (3 : ZMod 1827893074603) ^ 456973268650) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1827893074602 := by rw [factor_0_38]; decide
      change (3 : ZMod 1827893074603) ^ 913946537301 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1827893074603) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1827893074603) ^ 2 = 9 := by
        calc
          (3 : ZMod 1827893074603) ^ 2 = (3 : ZMod 1827893074603) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 1 * (3 : ZMod 1827893074603) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1827893074603) ^ 4 = 81 := by
        calc
          (3 : ZMod 1827893074603) ^ 4 = (3 : ZMod 1827893074603) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 2 * (3 : ZMod 1827893074603) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1827893074603) ^ 8 = 6561 := by
        calc
          (3 : ZMod 1827893074603) ^ 8 = (3 : ZMod 1827893074603) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 4 * (3 : ZMod 1827893074603) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1827893074603) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 1827893074603) ^ 17 = (3 : ZMod 1827893074603) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 8 * (3 : ZMod 1827893074603) ^ 8) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1827893074603) ^ 35 = 283754040994 := by
        calc
          (3 : ZMod 1827893074603) ^ 35 = (3 : ZMod 1827893074603) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 17 * (3 : ZMod 1827893074603) ^ 17) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 283754040994 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1827893074603) ^ 70 = 1470386002534 := by
        calc
          (3 : ZMod 1827893074603) ^ 70 = (3 : ZMod 1827893074603) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 35 * (3 : ZMod 1827893074603) ^ 35 := by rw [pow_add]
          _ = 1470386002534 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1827893074603) ^ 141 = 939760979101 := by
        calc
          (3 : ZMod 1827893074603) ^ 141 = (3 : ZMod 1827893074603) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 70 * (3 : ZMod 1827893074603) ^ 70) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 939760979101 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1827893074603) ^ 283 = 1034286158286 := by
        calc
          (3 : ZMod 1827893074603) ^ 283 = (3 : ZMod 1827893074603) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 141 * (3 : ZMod 1827893074603) ^ 141) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1034286158286 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1827893074603) ^ 567 = 698419722792 := by
        calc
          (3 : ZMod 1827893074603) ^ 567 = (3 : ZMod 1827893074603) ^ (283 + 283 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 283 * (3 : ZMod 1827893074603) ^ 283) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 698419722792 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1827893074603) ^ 1134 = 147358412631 := by
        calc
          (3 : ZMod 1827893074603) ^ 1134 = (3 : ZMod 1827893074603) ^ (567 + 567) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 567 * (3 : ZMod 1827893074603) ^ 567 := by rw [pow_add]
          _ = 147358412631 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1827893074603) ^ 2269 = 1636429119028 := by
        calc
          (3 : ZMod 1827893074603) ^ 2269 = (3 : ZMod 1827893074603) ^ (1134 + 1134 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1134 * (3 : ZMod 1827893074603) ^ 1134) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1636429119028 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1827893074603) ^ 4539 = 1231783308777 := by
        calc
          (3 : ZMod 1827893074603) ^ 4539 = (3 : ZMod 1827893074603) ^ (2269 + 2269 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 2269 * (3 : ZMod 1827893074603) ^ 2269) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1231783308777 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1827893074603) ^ 9079 = 455205192282 := by
        calc
          (3 : ZMod 1827893074603) ^ 9079 = (3 : ZMod 1827893074603) ^ (4539 + 4539 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 4539 * (3 : ZMod 1827893074603) ^ 4539) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 455205192282 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1827893074603) ^ 18158 = 806580452939 := by
        calc
          (3 : ZMod 1827893074603) ^ 18158 = (3 : ZMod 1827893074603) ^ (9079 + 9079) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 9079 * (3 : ZMod 1827893074603) ^ 9079 := by rw [pow_add]
          _ = 806580452939 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1827893074603) ^ 36316 = 1454206066851 := by
        calc
          (3 : ZMod 1827893074603) ^ 36316 = (3 : ZMod 1827893074603) ^ (18158 + 18158) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 18158 * (3 : ZMod 1827893074603) ^ 18158 := by rw [pow_add]
          _ = 1454206066851 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1827893074603) ^ 72633 = 866023307411 := by
        calc
          (3 : ZMod 1827893074603) ^ 72633 = (3 : ZMod 1827893074603) ^ (36316 + 36316 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 36316 * (3 : ZMod 1827893074603) ^ 36316) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 866023307411 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1827893074603) ^ 145267 = 696517036426 := by
        calc
          (3 : ZMod 1827893074603) ^ 145267 = (3 : ZMod 1827893074603) ^ (72633 + 72633 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 72633 * (3 : ZMod 1827893074603) ^ 72633) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 696517036426 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1827893074603) ^ 290535 = 193335490358 := by
        calc
          (3 : ZMod 1827893074603) ^ 290535 = (3 : ZMod 1827893074603) ^ (145267 + 145267 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 145267 * (3 : ZMod 1827893074603) ^ 145267) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 193335490358 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1827893074603) ^ 581071 = 998680697757 := by
        calc
          (3 : ZMod 1827893074603) ^ 581071 = (3 : ZMod 1827893074603) ^ (290535 + 290535 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 290535 * (3 : ZMod 1827893074603) ^ 290535) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 998680697757 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1827893074603) ^ 1162143 = 571781591671 := by
        calc
          (3 : ZMod 1827893074603) ^ 1162143 = (3 : ZMod 1827893074603) ^ (581071 + 581071 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 581071 * (3 : ZMod 1827893074603) ^ 581071) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 571781591671 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1827893074603) ^ 2324286 = 468321761925 := by
        calc
          (3 : ZMod 1827893074603) ^ 2324286 = (3 : ZMod 1827893074603) ^ (1162143 + 1162143) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 1162143 * (3 : ZMod 1827893074603) ^ 1162143 := by rw [pow_add]
          _ = 468321761925 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1827893074603) ^ 4648572 = 29219133108 := by
        calc
          (3 : ZMod 1827893074603) ^ 4648572 = (3 : ZMod 1827893074603) ^ (2324286 + 2324286) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 2324286 * (3 : ZMod 1827893074603) ^ 2324286 := by rw [pow_add]
          _ = 29219133108 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1827893074603) ^ 9297144 = 1465791712559 := by
        calc
          (3 : ZMod 1827893074603) ^ 9297144 = (3 : ZMod 1827893074603) ^ (4648572 + 4648572) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 4648572 * (3 : ZMod 1827893074603) ^ 4648572 := by rw [pow_add]
          _ = 1465791712559 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1827893074603) ^ 18594289 = 1762682945418 := by
        calc
          (3 : ZMod 1827893074603) ^ 18594289 = (3 : ZMod 1827893074603) ^ (9297144 + 9297144 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 9297144 * (3 : ZMod 1827893074603) ^ 9297144) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1762682945418 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1827893074603) ^ 37188579 = 393075589601 := by
        calc
          (3 : ZMod 1827893074603) ^ 37188579 = (3 : ZMod 1827893074603) ^ (18594289 + 18594289 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 18594289 * (3 : ZMod 1827893074603) ^ 18594289) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 393075589601 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1827893074603) ^ 74377159 = 1216705261009 := by
        calc
          (3 : ZMod 1827893074603) ^ 74377159 = (3 : ZMod 1827893074603) ^ (37188579 + 37188579 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 37188579 * (3 : ZMod 1827893074603) ^ 37188579) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1216705261009 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 1827893074603) ^ 148754319 = 715246168122 := by
        calc
          (3 : ZMod 1827893074603) ^ 148754319 = (3 : ZMod 1827893074603) ^ (74377159 + 74377159 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 74377159 * (3 : ZMod 1827893074603) ^ 74377159) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 715246168122 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 1827893074603) ^ 297508638 = 1362571669746 := by
        calc
          (3 : ZMod 1827893074603) ^ 297508638 = (3 : ZMod 1827893074603) ^ (148754319 + 148754319) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 148754319 * (3 : ZMod 1827893074603) ^ 148754319 := by rw [pow_add]
          _ = 1362571669746 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 1827893074603) ^ 595017276 = 430924257603 := by
        calc
          (3 : ZMod 1827893074603) ^ 595017276 = (3 : ZMod 1827893074603) ^ (297508638 + 297508638) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 297508638 * (3 : ZMod 1827893074603) ^ 297508638 := by rw [pow_add]
          _ = 430924257603 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 1827893074603) ^ 1190034553 = 916120530371 := by
        calc
          (3 : ZMod 1827893074603) ^ 1190034553 = (3 : ZMod 1827893074603) ^ (595017276 + 595017276 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 595017276 * (3 : ZMod 1827893074603) ^ 595017276) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 916120530371 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 1827893074603) ^ 2380069107 = 876560755818 := by
        calc
          (3 : ZMod 1827893074603) ^ 2380069107 = (3 : ZMod 1827893074603) ^ (1190034553 + 1190034553 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1190034553 * (3 : ZMod 1827893074603) ^ 1190034553) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 876560755818 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 1827893074603) ^ 4760138215 = 868645552044 := by
        calc
          (3 : ZMod 1827893074603) ^ 4760138215 = (3 : ZMod 1827893074603) ^ (2380069107 + 2380069107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 2380069107 * (3 : ZMod 1827893074603) ^ 2380069107) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 868645552044 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 1827893074603) ^ 9520276430 = 277476065867 := by
        calc
          (3 : ZMod 1827893074603) ^ 9520276430 = (3 : ZMod 1827893074603) ^ (4760138215 + 4760138215) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 4760138215 * (3 : ZMod 1827893074603) ^ 4760138215 := by rw [pow_add]
          _ = 277476065867 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 1827893074603) ^ 19040552860 = 1417313961731 := by
        calc
          (3 : ZMod 1827893074603) ^ 19040552860 = (3 : ZMod 1827893074603) ^ (9520276430 + 9520276430) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 9520276430 * (3 : ZMod 1827893074603) ^ 9520276430 := by rw [pow_add]
          _ = 1417313961731 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 1827893074603) ^ 38081105720 = 1018136438779 := by
        calc
          (3 : ZMod 1827893074603) ^ 38081105720 = (3 : ZMod 1827893074603) ^ (19040552860 + 19040552860) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 19040552860 * (3 : ZMod 1827893074603) ^ 19040552860 := by rw [pow_add]
          _ = 1018136438779 := by rw [factor_1_34]; decide
      have factor_1_36 : (3 : ZMod 1827893074603) ^ 76162211441 = 1644340415250 := by
        calc
          (3 : ZMod 1827893074603) ^ 76162211441 = (3 : ZMod 1827893074603) ^ (38081105720 + 38081105720 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 38081105720 * (3 : ZMod 1827893074603) ^ 38081105720) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1644340415250 := by rw [factor_1_35]; decide
      have factor_1_37 : (3 : ZMod 1827893074603) ^ 152324422883 = 1296921998637 := by
        calc
          (3 : ZMod 1827893074603) ^ 152324422883 = (3 : ZMod 1827893074603) ^ (76162211441 + 76162211441 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 76162211441 * (3 : ZMod 1827893074603) ^ 76162211441) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1296921998637 := by rw [factor_1_36]; decide
      have factor_1_38 : (3 : ZMod 1827893074603) ^ 304648845767 = 1592913227897 := by
        calc
          (3 : ZMod 1827893074603) ^ 304648845767 = (3 : ZMod 1827893074603) ^ (152324422883 + 152324422883 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 152324422883 * (3 : ZMod 1827893074603) ^ 152324422883) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1592913227897 := by rw [factor_1_37]; decide
      have factor_1_39 : (3 : ZMod 1827893074603) ^ 609297691534 = 1592913227896 := by
        calc
          (3 : ZMod 1827893074603) ^ 609297691534 = (3 : ZMod 1827893074603) ^ (304648845767 + 304648845767) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 304648845767 * (3 : ZMod 1827893074603) ^ 304648845767 := by rw [pow_add]
          _ = 1592913227896 := by rw [factor_1_38]; decide
      change (3 : ZMod 1827893074603) ^ 609297691534 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1827893074603) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1827893074603) ^ 3 = 27 := by
        calc
          (3 : ZMod 1827893074603) ^ 3 = (3 : ZMod 1827893074603) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1 * (3 : ZMod 1827893074603) ^ 1) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1827893074603) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1827893074603) ^ 7 = (3 : ZMod 1827893074603) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 3 * (3 : ZMod 1827893074603) ^ 3) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 1827893074603) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 1827893074603) ^ 15 = (3 : ZMod 1827893074603) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 7 * (3 : ZMod 1827893074603) ^ 7) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 1827893074603) ^ 30 = 1167107739113 := by
        calc
          (3 : ZMod 1827893074603) ^ 30 = (3 : ZMod 1827893074603) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 15 * (3 : ZMod 1827893074603) ^ 15 := by rw [pow_add]
          _ = 1167107739113 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 1827893074603) ^ 60 = 1638624911464 := by
        calc
          (3 : ZMod 1827893074603) ^ 60 = (3 : ZMod 1827893074603) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 30 * (3 : ZMod 1827893074603) ^ 30 := by rw [pow_add]
          _ = 1638624911464 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 1827893074603) ^ 121 = 774282982044 := by
        calc
          (3 : ZMod 1827893074603) ^ 121 = (3 : ZMod 1827893074603) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 60 * (3 : ZMod 1827893074603) ^ 60) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 774282982044 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 1827893074603) ^ 243 = 49363339153 := by
        calc
          (3 : ZMod 1827893074603) ^ 243 = (3 : ZMod 1827893074603) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 121 * (3 : ZMod 1827893074603) ^ 121) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 49363339153 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 1827893074603) ^ 486 = 158104026449 := by
        calc
          (3 : ZMod 1827893074603) ^ 486 = (3 : ZMod 1827893074603) ^ (243 + 243) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 243 * (3 : ZMod 1827893074603) ^ 243 := by rw [pow_add]
          _ = 158104026449 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 1827893074603) ^ 972 = 1591401857224 := by
        calc
          (3 : ZMod 1827893074603) ^ 972 = (3 : ZMod 1827893074603) ^ (486 + 486) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 486 * (3 : ZMod 1827893074603) ^ 486 := by rw [pow_add]
          _ = 1591401857224 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 1827893074603) ^ 1945 = 592907965584 := by
        calc
          (3 : ZMod 1827893074603) ^ 1945 = (3 : ZMod 1827893074603) ^ (972 + 972 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 972 * (3 : ZMod 1827893074603) ^ 972) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 592907965584 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 1827893074603) ^ 3891 = 846088214007 := by
        calc
          (3 : ZMod 1827893074603) ^ 3891 = (3 : ZMod 1827893074603) ^ (1945 + 1945 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1945 * (3 : ZMod 1827893074603) ^ 1945) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 846088214007 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 1827893074603) ^ 7782 = 1152898753833 := by
        calc
          (3 : ZMod 1827893074603) ^ 7782 = (3 : ZMod 1827893074603) ^ (3891 + 3891) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3891 * (3 : ZMod 1827893074603) ^ 3891 := by rw [pow_add]
          _ = 1152898753833 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 1827893074603) ^ 15564 = 361122316280 := by
        calc
          (3 : ZMod 1827893074603) ^ 15564 = (3 : ZMod 1827893074603) ^ (7782 + 7782) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 7782 * (3 : ZMod 1827893074603) ^ 7782 := by rw [pow_add]
          _ = 361122316280 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 1827893074603) ^ 31128 = 1413764326416 := by
        calc
          (3 : ZMod 1827893074603) ^ 31128 = (3 : ZMod 1827893074603) ^ (15564 + 15564) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 15564 * (3 : ZMod 1827893074603) ^ 15564 := by rw [pow_add]
          _ = 1413764326416 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 1827893074603) ^ 62257 = 39264055699 := by
        calc
          (3 : ZMod 1827893074603) ^ 62257 = (3 : ZMod 1827893074603) ^ (31128 + 31128 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 31128 * (3 : ZMod 1827893074603) ^ 31128) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 39264055699 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 1827893074603) ^ 124515 = 564178076756 := by
        calc
          (3 : ZMod 1827893074603) ^ 124515 = (3 : ZMod 1827893074603) ^ (62257 + 62257 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 62257 * (3 : ZMod 1827893074603) ^ 62257) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 564178076756 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 1827893074603) ^ 249030 = 241070748493 := by
        calc
          (3 : ZMod 1827893074603) ^ 249030 = (3 : ZMod 1827893074603) ^ (124515 + 124515) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 124515 * (3 : ZMod 1827893074603) ^ 124515 := by rw [pow_add]
          _ = 241070748493 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 1827893074603) ^ 498061 = 627622420622 := by
        calc
          (3 : ZMod 1827893074603) ^ 498061 = (3 : ZMod 1827893074603) ^ (249030 + 249030 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 249030 * (3 : ZMod 1827893074603) ^ 249030) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 627622420622 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 1827893074603) ^ 996122 = 1227274469311 := by
        calc
          (3 : ZMod 1827893074603) ^ 996122 = (3 : ZMod 1827893074603) ^ (498061 + 498061) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 498061 * (3 : ZMod 1827893074603) ^ 498061 := by rw [pow_add]
          _ = 1227274469311 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 1827893074603) ^ 1992245 = 226875228850 := by
        calc
          (3 : ZMod 1827893074603) ^ 1992245 = (3 : ZMod 1827893074603) ^ (996122 + 996122 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 996122 * (3 : ZMod 1827893074603) ^ 996122) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 226875228850 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 1827893074603) ^ 3984490 = 989520593663 := by
        calc
          (3 : ZMod 1827893074603) ^ 3984490 = (3 : ZMod 1827893074603) ^ (1992245 + 1992245) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 1992245 * (3 : ZMod 1827893074603) ^ 1992245 := by rw [pow_add]
          _ = 989520593663 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 1827893074603) ^ 7968981 = 32999883578 := by
        calc
          (3 : ZMod 1827893074603) ^ 7968981 = (3 : ZMod 1827893074603) ^ (3984490 + 3984490 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 3984490 * (3 : ZMod 1827893074603) ^ 3984490) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 32999883578 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 1827893074603) ^ 15937962 = 422197815426 := by
        calc
          (3 : ZMod 1827893074603) ^ 15937962 = (3 : ZMod 1827893074603) ^ (7968981 + 7968981) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 7968981 * (3 : ZMod 1827893074603) ^ 7968981 := by rw [pow_add]
          _ = 422197815426 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 1827893074603) ^ 31875925 = 474622834486 := by
        calc
          (3 : ZMod 1827893074603) ^ 31875925 = (3 : ZMod 1827893074603) ^ (15937962 + 15937962 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 15937962 * (3 : ZMod 1827893074603) ^ 15937962) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 474622834486 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 1827893074603) ^ 63751851 = 1307828452905 := by
        calc
          (3 : ZMod 1827893074603) ^ 63751851 = (3 : ZMod 1827893074603) ^ (31875925 + 31875925 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 31875925 * (3 : ZMod 1827893074603) ^ 31875925) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1307828452905 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 1827893074603) ^ 127503702 = 1739953444879 := by
        calc
          (3 : ZMod 1827893074603) ^ 127503702 = (3 : ZMod 1827893074603) ^ (63751851 + 63751851) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 63751851 * (3 : ZMod 1827893074603) ^ 63751851 := by rw [pow_add]
          _ = 1739953444879 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 1827893074603) ^ 255007404 = 1526684952199 := by
        calc
          (3 : ZMod 1827893074603) ^ 255007404 = (3 : ZMod 1827893074603) ^ (127503702 + 127503702) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 127503702 * (3 : ZMod 1827893074603) ^ 127503702 := by rw [pow_add]
          _ = 1526684952199 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 1827893074603) ^ 510014808 = 1359307395424 := by
        calc
          (3 : ZMod 1827893074603) ^ 510014808 = (3 : ZMod 1827893074603) ^ (255007404 + 255007404) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 255007404 * (3 : ZMod 1827893074603) ^ 255007404 := by rw [pow_add]
          _ = 1359307395424 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 1827893074603) ^ 1020029617 = 1794325167990 := by
        calc
          (3 : ZMod 1827893074603) ^ 1020029617 = (3 : ZMod 1827893074603) ^ (510014808 + 510014808 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 510014808 * (3 : ZMod 1827893074603) ^ 510014808) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1794325167990 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 1827893074603) ^ 2040059235 = 1821935003942 := by
        calc
          (3 : ZMod 1827893074603) ^ 2040059235 = (3 : ZMod 1827893074603) ^ (1020029617 + 1020029617 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1020029617 * (3 : ZMod 1827893074603) ^ 1020029617) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1821935003942 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 1827893074603) ^ 4080118470 = 1234569117009 := by
        calc
          (3 : ZMod 1827893074603) ^ 4080118470 = (3 : ZMod 1827893074603) ^ (2040059235 + 2040059235) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 2040059235 * (3 : ZMod 1827893074603) ^ 2040059235 := by rw [pow_add]
          _ = 1234569117009 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 1827893074603) ^ 8160236940 = 1418877815465 := by
        calc
          (3 : ZMod 1827893074603) ^ 8160236940 = (3 : ZMod 1827893074603) ^ (4080118470 + 4080118470) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 4080118470 * (3 : ZMod 1827893074603) ^ 4080118470 := by rw [pow_add]
          _ = 1418877815465 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 1827893074603) ^ 16320473880 = 1777452062285 := by
        calc
          (3 : ZMod 1827893074603) ^ 16320473880 = (3 : ZMod 1827893074603) ^ (8160236940 + 8160236940) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 8160236940 * (3 : ZMod 1827893074603) ^ 8160236940 := by rw [pow_add]
          _ = 1777452062285 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 1827893074603) ^ 32640947760 = 296674136442 := by
        calc
          (3 : ZMod 1827893074603) ^ 32640947760 = (3 : ZMod 1827893074603) ^ (16320473880 + 16320473880) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 16320473880 * (3 : ZMod 1827893074603) ^ 16320473880 := by rw [pow_add]
          _ = 296674136442 := by rw [factor_2_33]; decide
      have factor_2_35 : (3 : ZMod 1827893074603) ^ 65281895521 = 737798168948 := by
        calc
          (3 : ZMod 1827893074603) ^ 65281895521 = (3 : ZMod 1827893074603) ^ (32640947760 + 32640947760 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 32640947760 * (3 : ZMod 1827893074603) ^ 32640947760) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 737798168948 := by rw [factor_2_34]; decide
      have factor_2_36 : (3 : ZMod 1827893074603) ^ 130563791043 = 1512073012275 := by
        calc
          (3 : ZMod 1827893074603) ^ 130563791043 = (3 : ZMod 1827893074603) ^ (65281895521 + 65281895521 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 65281895521 * (3 : ZMod 1827893074603) ^ 65281895521) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1512073012275 := by rw [factor_2_35]; decide
      have factor_2_37 : (3 : ZMod 1827893074603) ^ 261127582086 = 97512311589 := by
        calc
          (3 : ZMod 1827893074603) ^ 261127582086 = (3 : ZMod 1827893074603) ^ (130563791043 + 130563791043) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 130563791043 * (3 : ZMod 1827893074603) ^ 130563791043 := by rw [pow_add]
          _ = 97512311589 := by rw [factor_2_36]; decide
      change (3 : ZMod 1827893074603) ^ 261127582086 ≠ 1
      rw [factor_2_37]
      decide
    ·
      have factor_3_0 : (3 : ZMod 1827893074603) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 1827893074603) ^ 3 = 27 := by
        calc
          (3 : ZMod 1827893074603) ^ 3 = (3 : ZMod 1827893074603) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1 * (3 : ZMod 1827893074603) ^ 1) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 1827893074603) ^ 7 = 2187 := by
        calc
          (3 : ZMod 1827893074603) ^ 7 = (3 : ZMod 1827893074603) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 3 * (3 : ZMod 1827893074603) ^ 3) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 1827893074603) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 1827893074603) ^ 14 = (3 : ZMod 1827893074603) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 7 * (3 : ZMod 1827893074603) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 1827893074603) ^ 28 = 942075559725 := by
        calc
          (3 : ZMod 1827893074603) ^ 28 = (3 : ZMod 1827893074603) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 14 * (3 : ZMod 1827893074603) ^ 14 := by rw [pow_add]
          _ = 942075559725 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 1827893074603) ^ 56 = 1690156943606 := by
        calc
          (3 : ZMod 1827893074603) ^ 56 = (3 : ZMod 1827893074603) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 28 * (3 : ZMod 1827893074603) ^ 28 := by rw [pow_add]
          _ = 1690156943606 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 1827893074603) ^ 113 = 844275308494 := by
        calc
          (3 : ZMod 1827893074603) ^ 113 = (3 : ZMod 1827893074603) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 56 * (3 : ZMod 1827893074603) ^ 56) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 844275308494 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 1827893074603) ^ 227 = 754284561598 := by
        calc
          (3 : ZMod 1827893074603) ^ 227 = (3 : ZMod 1827893074603) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 113 * (3 : ZMod 1827893074603) ^ 113) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 754284561598 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 1827893074603) ^ 455 = 938726359372 := by
        calc
          (3 : ZMod 1827893074603) ^ 455 = (3 : ZMod 1827893074603) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 227 * (3 : ZMod 1827893074603) ^ 227) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 938726359372 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 1827893074603) ^ 910 = 409730624870 := by
        calc
          (3 : ZMod 1827893074603) ^ 910 = (3 : ZMod 1827893074603) ^ (455 + 455) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 455 * (3 : ZMod 1827893074603) ^ 455 := by rw [pow_add]
          _ = 409730624870 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 1827893074603) ^ 1820 = 481678250358 := by
        calc
          (3 : ZMod 1827893074603) ^ 1820 = (3 : ZMod 1827893074603) ^ (910 + 910) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 910 * (3 : ZMod 1827893074603) ^ 910 := by rw [pow_add]
          _ = 481678250358 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 1827893074603) ^ 3641 = 1442916791030 := by
        calc
          (3 : ZMod 1827893074603) ^ 3641 = (3 : ZMod 1827893074603) ^ (1820 + 1820 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1820 * (3 : ZMod 1827893074603) ^ 1820) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1442916791030 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 1827893074603) ^ 7282 = 884414991272 := by
        calc
          (3 : ZMod 1827893074603) ^ 7282 = (3 : ZMod 1827893074603) ^ (3641 + 3641) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3641 * (3 : ZMod 1827893074603) ^ 3641 := by rw [pow_add]
          _ = 884414991272 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 1827893074603) ^ 14565 = 1619395940102 := by
        calc
          (3 : ZMod 1827893074603) ^ 14565 = (3 : ZMod 1827893074603) ^ (7282 + 7282 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 7282 * (3 : ZMod 1827893074603) ^ 7282) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1619395940102 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 1827893074603) ^ 29131 = 941606238612 := by
        calc
          (3 : ZMod 1827893074603) ^ 29131 = (3 : ZMod 1827893074603) ^ (14565 + 14565 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 14565 * (3 : ZMod 1827893074603) ^ 14565) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 941606238612 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 1827893074603) ^ 58262 = 258161351402 := by
        calc
          (3 : ZMod 1827893074603) ^ 58262 = (3 : ZMod 1827893074603) ^ (29131 + 29131) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 29131 * (3 : ZMod 1827893074603) ^ 29131 := by rw [pow_add]
          _ = 258161351402 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 1827893074603) ^ 116525 = 1388602467554 := by
        calc
          (3 : ZMod 1827893074603) ^ 116525 = (3 : ZMod 1827893074603) ^ (58262 + 58262 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 58262 * (3 : ZMod 1827893074603) ^ 58262) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1388602467554 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 1827893074603) ^ 233050 = 1429811870825 := by
        calc
          (3 : ZMod 1827893074603) ^ 233050 = (3 : ZMod 1827893074603) ^ (116525 + 116525) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 116525 * (3 : ZMod 1827893074603) ^ 116525 := by rw [pow_add]
          _ = 1429811870825 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 1827893074603) ^ 466101 = 1712620717556 := by
        calc
          (3 : ZMod 1827893074603) ^ 466101 = (3 : ZMod 1827893074603) ^ (233050 + 233050 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 233050 * (3 : ZMod 1827893074603) ^ 233050) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1712620717556 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 1827893074603) ^ 932202 = 1241209383746 := by
        calc
          (3 : ZMod 1827893074603) ^ 932202 = (3 : ZMod 1827893074603) ^ (466101 + 466101) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 466101 * (3 : ZMod 1827893074603) ^ 466101 := by rw [pow_add]
          _ = 1241209383746 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 1827893074603) ^ 1864405 = 1698177857363 := by
        calc
          (3 : ZMod 1827893074603) ^ 1864405 = (3 : ZMod 1827893074603) ^ (932202 + 932202 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 932202 * (3 : ZMod 1827893074603) ^ 932202) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1698177857363 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 1827893074603) ^ 3728811 = 101890885944 := by
        calc
          (3 : ZMod 1827893074603) ^ 3728811 = (3 : ZMod 1827893074603) ^ (1864405 + 1864405 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1864405 * (3 : ZMod 1827893074603) ^ 1864405) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 101890885944 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 1827893074603) ^ 7457622 = 285042101417 := by
        calc
          (3 : ZMod 1827893074603) ^ 7457622 = (3 : ZMod 1827893074603) ^ (3728811 + 3728811) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 3728811 * (3 : ZMod 1827893074603) ^ 3728811 := by rw [pow_add]
          _ = 285042101417 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 1827893074603) ^ 14915244 = 823084520577 := by
        calc
          (3 : ZMod 1827893074603) ^ 14915244 = (3 : ZMod 1827893074603) ^ (7457622 + 7457622) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 7457622 * (3 : ZMod 1827893074603) ^ 7457622 := by rw [pow_add]
          _ = 823084520577 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 1827893074603) ^ 29830489 = 365788846913 := by
        calc
          (3 : ZMod 1827893074603) ^ 29830489 = (3 : ZMod 1827893074603) ^ (14915244 + 14915244 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 14915244 * (3 : ZMod 1827893074603) ^ 14915244) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 365788846913 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 1827893074603) ^ 59660979 = 1202734206464 := by
        calc
          (3 : ZMod 1827893074603) ^ 59660979 = (3 : ZMod 1827893074603) ^ (29830489 + 29830489 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 29830489 * (3 : ZMod 1827893074603) ^ 29830489) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1202734206464 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 1827893074603) ^ 119321958 = 1621560931016 := by
        calc
          (3 : ZMod 1827893074603) ^ 119321958 = (3 : ZMod 1827893074603) ^ (59660979 + 59660979) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 59660979 * (3 : ZMod 1827893074603) ^ 59660979 := by rw [pow_add]
          _ = 1621560931016 := by rw [factor_3_25]; decide
      change (3 : ZMod 1827893074603) ^ 119321958 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (3 : ZMod 1827893074603) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 1827893074603) ^ 2 = 9 := by
        calc
          (3 : ZMod 1827893074603) ^ 2 = (3 : ZMod 1827893074603) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 1 * (3 : ZMod 1827893074603) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 1827893074603) ^ 4 = 81 := by
        calc
          (3 : ZMod 1827893074603) ^ 4 = (3 : ZMod 1827893074603) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 2 * (3 : ZMod 1827893074603) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 1827893074603) ^ 8 = 6561 := by
        calc
          (3 : ZMod 1827893074603) ^ 8 = (3 : ZMod 1827893074603) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 4 * (3 : ZMod 1827893074603) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 1827893074603) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 1827893074603) ^ 17 = (3 : ZMod 1827893074603) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 8 * (3 : ZMod 1827893074603) ^ 8) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 1827893074603) ^ 34 = 1313180063400 := by
        calc
          (3 : ZMod 1827893074603) ^ 34 = (3 : ZMod 1827893074603) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 17 * (3 : ZMod 1827893074603) ^ 17 := by rw [pow_add]
          _ = 1313180063400 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 1827893074603) ^ 68 = 1178872375061 := by
        calc
          (3 : ZMod 1827893074603) ^ 68 = (3 : ZMod 1827893074603) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 34 * (3 : ZMod 1827893074603) ^ 34 := by rw [pow_add]
          _ = 1178872375061 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 1827893074603) ^ 137 = 124434893236 := by
        calc
          (3 : ZMod 1827893074603) ^ 137 = (3 : ZMod 1827893074603) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 68 * (3 : ZMod 1827893074603) ^ 68) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 124434893236 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 1827893074603) ^ 274 = 889343005058 := by
        calc
          (3 : ZMod 1827893074603) ^ 274 = (3 : ZMod 1827893074603) ^ (137 + 137) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 137 * (3 : ZMod 1827893074603) ^ 137 := by rw [pow_add]
          _ = 889343005058 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 1827893074603) ^ 549 = 1616870107854 := by
        calc
          (3 : ZMod 1827893074603) ^ 549 = (3 : ZMod 1827893074603) ^ (274 + 274 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 274 * (3 : ZMod 1827893074603) ^ 274) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1616870107854 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 1827893074603) ^ 1099 = 1174140066081 := by
        calc
          (3 : ZMod 1827893074603) ^ 1099 = (3 : ZMod 1827893074603) ^ (549 + 549 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 549 * (3 : ZMod 1827893074603) ^ 549) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1174140066081 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 1827893074603) ^ 2199 = 853990598979 := by
        calc
          (3 : ZMod 1827893074603) ^ 2199 = (3 : ZMod 1827893074603) ^ (1099 + 1099 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1099 * (3 : ZMod 1827893074603) ^ 1099) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 853990598979 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 1827893074603) ^ 4398 = 773336068050 := by
        calc
          (3 : ZMod 1827893074603) ^ 4398 = (3 : ZMod 1827893074603) ^ (2199 + 2199) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 2199 * (3 : ZMod 1827893074603) ^ 2199 := by rw [pow_add]
          _ = 773336068050 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 1827893074603) ^ 8796 = 746354370489 := by
        calc
          (3 : ZMod 1827893074603) ^ 8796 = (3 : ZMod 1827893074603) ^ (4398 + 4398) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 4398 * (3 : ZMod 1827893074603) ^ 4398 := by rw [pow_add]
          _ = 746354370489 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 1827893074603) ^ 17592 = 1618438205339 := by
        calc
          (3 : ZMod 1827893074603) ^ 17592 = (3 : ZMod 1827893074603) ^ (8796 + 8796) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 8796 * (3 : ZMod 1827893074603) ^ 8796 := by rw [pow_add]
          _ = 1618438205339 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 1827893074603) ^ 35185 = 322215055162 := by
        calc
          (3 : ZMod 1827893074603) ^ 35185 = (3 : ZMod 1827893074603) ^ (17592 + 17592 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 17592 * (3 : ZMod 1827893074603) ^ 17592) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 322215055162 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 1827893074603) ^ 70371 = 215789074872 := by
        calc
          (3 : ZMod 1827893074603) ^ 70371 = (3 : ZMod 1827893074603) ^ (35185 + 35185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 35185 * (3 : ZMod 1827893074603) ^ 35185) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 215789074872 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 1827893074603) ^ 140743 = 1040449119672 := by
        calc
          (3 : ZMod 1827893074603) ^ 140743 = (3 : ZMod 1827893074603) ^ (70371 + 70371 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 70371 * (3 : ZMod 1827893074603) ^ 70371) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1040449119672 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 1827893074603) ^ 281486 = 785348072548 := by
        calc
          (3 : ZMod 1827893074603) ^ 281486 = (3 : ZMod 1827893074603) ^ (140743 + 140743) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 140743 * (3 : ZMod 1827893074603) ^ 140743 := by rw [pow_add]
          _ = 785348072548 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 1827893074603) ^ 562973 = 1262200490221 := by
        calc
          (3 : ZMod 1827893074603) ^ 562973 = (3 : ZMod 1827893074603) ^ (281486 + 281486 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 281486 * (3 : ZMod 1827893074603) ^ 281486) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 1262200490221 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 1827893074603) ^ 1125946 = 824954206628 := by
        calc
          (3 : ZMod 1827893074603) ^ 1125946 = (3 : ZMod 1827893074603) ^ (562973 + 562973) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 562973 * (3 : ZMod 1827893074603) ^ 562973 := by rw [pow_add]
          _ = 824954206628 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 1827893074603) ^ 2251893 = 14569961879 := by
        calc
          (3 : ZMod 1827893074603) ^ 2251893 = (3 : ZMod 1827893074603) ^ (1125946 + 1125946 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = ((3 : ZMod 1827893074603) ^ 1125946 * (3 : ZMod 1827893074603) ^ 1125946) * (3 : ZMod 1827893074603) := by rw [pow_succ, pow_add]
          _ = 14569961879 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 1827893074603) ^ 4503786 = 1179895615301 := by
        calc
          (3 : ZMod 1827893074603) ^ 4503786 = (3 : ZMod 1827893074603) ^ (2251893 + 2251893) :=
            congrArg (fun n : ℕ => (3 : ZMod 1827893074603) ^ n) (by norm_num)
          _ = (3 : ZMod 1827893074603) ^ 2251893 * (3 : ZMod 1827893074603) ^ 2251893 := by rw [pow_add]
          _ = 1179895615301 := by rw [factor_4_21]; decide
      change (3 : ZMod 1827893074603) ^ 4503786 ≠ 1
      rw [factor_4_22]
      decide

#print axioms prime_lucas_1827893074603

end TotientTailPeriodKiller
end Erdos249257
