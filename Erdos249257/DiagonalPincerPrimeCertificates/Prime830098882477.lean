import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_830098882477 : Nat.Prime 830098882477 := by
  apply lucas_primality 830098882477 (5 : ZMod 830098882477)
  ·
      have fermat_0 : (5 : ZMod 830098882477) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 830098882477) ^ 3 = 125 := by
        calc
          (5 : ZMod 830098882477) ^ 3 = (5 : ZMod 830098882477) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1 * (5 : ZMod 830098882477) ^ 1) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 830098882477) ^ 6 = 15625 := by
        calc
          (5 : ZMod 830098882477) ^ 6 = (5 : ZMod 830098882477) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 3 * (5 : ZMod 830098882477) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 830098882477) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 830098882477) ^ 12 = (5 : ZMod 830098882477) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 6 * (5 : ZMod 830098882477) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 830098882477) ^ 24 = 224618012117 := by
        calc
          (5 : ZMod 830098882477) ^ 24 = (5 : ZMod 830098882477) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 12 * (5 : ZMod 830098882477) ^ 12 := by rw [pow_add]
          _ = 224618012117 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 830098882477) ^ 48 = 366435129227 := by
        calc
          (5 : ZMod 830098882477) ^ 48 = (5 : ZMod 830098882477) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 24 * (5 : ZMod 830098882477) ^ 24 := by rw [pow_add]
          _ = 366435129227 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 830098882477) ^ 96 = 126853692801 := by
        calc
          (5 : ZMod 830098882477) ^ 96 = (5 : ZMod 830098882477) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 48 * (5 : ZMod 830098882477) ^ 48 := by rw [pow_add]
          _ = 126853692801 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 830098882477) ^ 193 = 599563742142 := by
        calc
          (5 : ZMod 830098882477) ^ 193 = (5 : ZMod 830098882477) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 96 * (5 : ZMod 830098882477) ^ 96) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 599563742142 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 830098882477) ^ 386 = 497250245869 := by
        calc
          (5 : ZMod 830098882477) ^ 386 = (5 : ZMod 830098882477) ^ (193 + 193) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 193 * (5 : ZMod 830098882477) ^ 193 := by rw [pow_add]
          _ = 497250245869 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 830098882477) ^ 773 = 276342157716 := by
        calc
          (5 : ZMod 830098882477) ^ 773 = (5 : ZMod 830098882477) ^ (386 + 386 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 386 * (5 : ZMod 830098882477) ^ 386) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 276342157716 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 830098882477) ^ 1546 = 786987849770 := by
        calc
          (5 : ZMod 830098882477) ^ 1546 = (5 : ZMod 830098882477) ^ (773 + 773) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 773 * (5 : ZMod 830098882477) ^ 773 := by rw [pow_add]
          _ = 786987849770 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 830098882477) ^ 3092 = 302287034499 := by
        calc
          (5 : ZMod 830098882477) ^ 3092 = (5 : ZMod 830098882477) ^ (1546 + 1546) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1546 * (5 : ZMod 830098882477) ^ 1546 := by rw [pow_add]
          _ = 302287034499 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 830098882477) ^ 6184 = 58361394688 := by
        calc
          (5 : ZMod 830098882477) ^ 6184 = (5 : ZMod 830098882477) ^ (3092 + 3092) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 3092 * (5 : ZMod 830098882477) ^ 3092 := by rw [pow_add]
          _ = 58361394688 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 830098882477) ^ 12369 = 520239069619 := by
        calc
          (5 : ZMod 830098882477) ^ 12369 = (5 : ZMod 830098882477) ^ (6184 + 6184 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 6184 * (5 : ZMod 830098882477) ^ 6184) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 520239069619 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 830098882477) ^ 24738 = 87456397323 := by
        calc
          (5 : ZMod 830098882477) ^ 24738 = (5 : ZMod 830098882477) ^ (12369 + 12369) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 12369 * (5 : ZMod 830098882477) ^ 12369 := by rw [pow_add]
          _ = 87456397323 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 830098882477) ^ 49477 = 205949803192 := by
        calc
          (5 : ZMod 830098882477) ^ 49477 = (5 : ZMod 830098882477) ^ (24738 + 24738 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 24738 * (5 : ZMod 830098882477) ^ 24738) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 205949803192 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 830098882477) ^ 98955 = 229689036629 := by
        calc
          (5 : ZMod 830098882477) ^ 98955 = (5 : ZMod 830098882477) ^ (49477 + 49477 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 49477 * (5 : ZMod 830098882477) ^ 49477) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 229689036629 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 830098882477) ^ 197910 = 688468417807 := by
        calc
          (5 : ZMod 830098882477) ^ 197910 = (5 : ZMod 830098882477) ^ (98955 + 98955) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 98955 * (5 : ZMod 830098882477) ^ 98955 := by rw [pow_add]
          _ = 688468417807 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 830098882477) ^ 395821 = 787329741605 := by
        calc
          (5 : ZMod 830098882477) ^ 395821 = (5 : ZMod 830098882477) ^ (197910 + 197910 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 197910 * (5 : ZMod 830098882477) ^ 197910) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 787329741605 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 830098882477) ^ 791643 = 306755860787 := by
        calc
          (5 : ZMod 830098882477) ^ 791643 = (5 : ZMod 830098882477) ^ (395821 + 395821 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 395821 * (5 : ZMod 830098882477) ^ 395821) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 306755860787 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 830098882477) ^ 1583287 = 567732822356 := by
        calc
          (5 : ZMod 830098882477) ^ 1583287 = (5 : ZMod 830098882477) ^ (791643 + 791643 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 791643 * (5 : ZMod 830098882477) ^ 791643) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 567732822356 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 830098882477) ^ 3166575 = 369012858033 := by
        calc
          (5 : ZMod 830098882477) ^ 3166575 = (5 : ZMod 830098882477) ^ (1583287 + 1583287 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1583287 * (5 : ZMod 830098882477) ^ 1583287) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 369012858033 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 830098882477) ^ 6333151 = 107647017379 := by
        calc
          (5 : ZMod 830098882477) ^ 6333151 = (5 : ZMod 830098882477) ^ (3166575 + 3166575 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 3166575 * (5 : ZMod 830098882477) ^ 3166575) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 107647017379 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 830098882477) ^ 12666303 = 430131890121 := by
        calc
          (5 : ZMod 830098882477) ^ 12666303 = (5 : ZMod 830098882477) ^ (6333151 + 6333151 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 6333151 * (5 : ZMod 830098882477) ^ 6333151) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 430131890121 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 830098882477) ^ 25332607 = 168591633766 := by
        calc
          (5 : ZMod 830098882477) ^ 25332607 = (5 : ZMod 830098882477) ^ (12666303 + 12666303 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 12666303 * (5 : ZMod 830098882477) ^ 12666303) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 168591633766 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 830098882477) ^ 50665214 = 553991366658 := by
        calc
          (5 : ZMod 830098882477) ^ 50665214 = (5 : ZMod 830098882477) ^ (25332607 + 25332607) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 25332607 * (5 : ZMod 830098882477) ^ 25332607 := by rw [pow_add]
          _ = 553991366658 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 830098882477) ^ 101330429 = 576676480173 := by
        calc
          (5 : ZMod 830098882477) ^ 101330429 = (5 : ZMod 830098882477) ^ (50665214 + 50665214 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 50665214 * (5 : ZMod 830098882477) ^ 50665214) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 576676480173 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 830098882477) ^ 202660859 = 374683908451 := by
        calc
          (5 : ZMod 830098882477) ^ 202660859 = (5 : ZMod 830098882477) ^ (101330429 + 101330429 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 101330429 * (5 : ZMod 830098882477) ^ 101330429) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 374683908451 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 830098882477) ^ 405321719 = 332011838711 := by
        calc
          (5 : ZMod 830098882477) ^ 405321719 = (5 : ZMod 830098882477) ^ (202660859 + 202660859 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 202660859 * (5 : ZMod 830098882477) ^ 202660859) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 332011838711 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 830098882477) ^ 810643439 = 701133377829 := by
        calc
          (5 : ZMod 830098882477) ^ 810643439 = (5 : ZMod 830098882477) ^ (405321719 + 405321719 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 405321719 * (5 : ZMod 830098882477) ^ 405321719) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 701133377829 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 830098882477) ^ 1621286879 = 778100720959 := by
        calc
          (5 : ZMod 830098882477) ^ 1621286879 = (5 : ZMod 830098882477) ^ (810643439 + 810643439 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 810643439 * (5 : ZMod 830098882477) ^ 810643439) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 778100720959 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 830098882477) ^ 3242573759 = 114025721914 := by
        calc
          (5 : ZMod 830098882477) ^ 3242573759 = (5 : ZMod 830098882477) ^ (1621286879 + 1621286879 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1621286879 * (5 : ZMod 830098882477) ^ 1621286879) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 114025721914 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 830098882477) ^ 6485147519 = 227264990427 := by
        calc
          (5 : ZMod 830098882477) ^ 6485147519 = (5 : ZMod 830098882477) ^ (3242573759 + 3242573759 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 3242573759 * (5 : ZMod 830098882477) ^ 3242573759) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 227264990427 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 830098882477) ^ 12970295038 = 144523650375 := by
        calc
          (5 : ZMod 830098882477) ^ 12970295038 = (5 : ZMod 830098882477) ^ (6485147519 + 6485147519) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 6485147519 * (5 : ZMod 830098882477) ^ 6485147519 := by rw [pow_add]
          _ = 144523650375 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 830098882477) ^ 25940590077 = 66541738307 := by
        calc
          (5 : ZMod 830098882477) ^ 25940590077 = (5 : ZMod 830098882477) ^ (12970295038 + 12970295038 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 12970295038 * (5 : ZMod 830098882477) ^ 12970295038) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 66541738307 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 830098882477) ^ 51881180154 = 694066343937 := by
        calc
          (5 : ZMod 830098882477) ^ 51881180154 = (5 : ZMod 830098882477) ^ (25940590077 + 25940590077) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 25940590077 * (5 : ZMod 830098882477) ^ 25940590077 := by rw [pow_add]
          _ = 694066343937 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 830098882477) ^ 103762360309 = 326485183428 := by
        calc
          (5 : ZMod 830098882477) ^ 103762360309 = (5 : ZMod 830098882477) ^ (51881180154 + 51881180154 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 51881180154 * (5 : ZMod 830098882477) ^ 51881180154) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 326485183428 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 830098882477) ^ 207524720619 = 250513871111 := by
        calc
          (5 : ZMod 830098882477) ^ 207524720619 = (5 : ZMod 830098882477) ^ (103762360309 + 103762360309 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 103762360309 * (5 : ZMod 830098882477) ^ 103762360309) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 250513871111 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 830098882477) ^ 415049441238 = 830098882476 := by
        calc
          (5 : ZMod 830098882477) ^ 415049441238 = (5 : ZMod 830098882477) ^ (207524720619 + 207524720619) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 207524720619 * (5 : ZMod 830098882477) ^ 207524720619 := by rw [pow_add]
          _ = 830098882476 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 830098882477) ^ 830098882476 = 1 := by
        calc
          (5 : ZMod 830098882477) ^ 830098882476 = (5 : ZMod 830098882477) ^ (415049441238 + 415049441238) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 415049441238 * (5 : ZMod 830098882477) ^ 415049441238 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (17, 1), (71, 1), (19103813, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (17, 1), (71, 1), (19103813, 1)] : List FactorBlock).map factorBlockValue).prod = 830098882477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 830098882477) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 830098882477) ^ 3 = 125 := by
        calc
          (5 : ZMod 830098882477) ^ 3 = (5 : ZMod 830098882477) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1 * (5 : ZMod 830098882477) ^ 1) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 830098882477) ^ 6 = 15625 := by
        calc
          (5 : ZMod 830098882477) ^ 6 = (5 : ZMod 830098882477) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 3 * (5 : ZMod 830098882477) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 830098882477) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 830098882477) ^ 12 = (5 : ZMod 830098882477) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 6 * (5 : ZMod 830098882477) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 830098882477) ^ 24 = 224618012117 := by
        calc
          (5 : ZMod 830098882477) ^ 24 = (5 : ZMod 830098882477) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 12 * (5 : ZMod 830098882477) ^ 12 := by rw [pow_add]
          _ = 224618012117 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 830098882477) ^ 48 = 366435129227 := by
        calc
          (5 : ZMod 830098882477) ^ 48 = (5 : ZMod 830098882477) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 24 * (5 : ZMod 830098882477) ^ 24 := by rw [pow_add]
          _ = 366435129227 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 830098882477) ^ 96 = 126853692801 := by
        calc
          (5 : ZMod 830098882477) ^ 96 = (5 : ZMod 830098882477) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 48 * (5 : ZMod 830098882477) ^ 48 := by rw [pow_add]
          _ = 126853692801 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 830098882477) ^ 193 = 599563742142 := by
        calc
          (5 : ZMod 830098882477) ^ 193 = (5 : ZMod 830098882477) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 96 * (5 : ZMod 830098882477) ^ 96) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 599563742142 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 830098882477) ^ 386 = 497250245869 := by
        calc
          (5 : ZMod 830098882477) ^ 386 = (5 : ZMod 830098882477) ^ (193 + 193) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 193 * (5 : ZMod 830098882477) ^ 193 := by rw [pow_add]
          _ = 497250245869 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 830098882477) ^ 773 = 276342157716 := by
        calc
          (5 : ZMod 830098882477) ^ 773 = (5 : ZMod 830098882477) ^ (386 + 386 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 386 * (5 : ZMod 830098882477) ^ 386) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 276342157716 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 830098882477) ^ 1546 = 786987849770 := by
        calc
          (5 : ZMod 830098882477) ^ 1546 = (5 : ZMod 830098882477) ^ (773 + 773) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 773 * (5 : ZMod 830098882477) ^ 773 := by rw [pow_add]
          _ = 786987849770 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 830098882477) ^ 3092 = 302287034499 := by
        calc
          (5 : ZMod 830098882477) ^ 3092 = (5 : ZMod 830098882477) ^ (1546 + 1546) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1546 * (5 : ZMod 830098882477) ^ 1546 := by rw [pow_add]
          _ = 302287034499 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 830098882477) ^ 6184 = 58361394688 := by
        calc
          (5 : ZMod 830098882477) ^ 6184 = (5 : ZMod 830098882477) ^ (3092 + 3092) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 3092 * (5 : ZMod 830098882477) ^ 3092 := by rw [pow_add]
          _ = 58361394688 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 830098882477) ^ 12369 = 520239069619 := by
        calc
          (5 : ZMod 830098882477) ^ 12369 = (5 : ZMod 830098882477) ^ (6184 + 6184 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 6184 * (5 : ZMod 830098882477) ^ 6184) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 520239069619 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 830098882477) ^ 24738 = 87456397323 := by
        calc
          (5 : ZMod 830098882477) ^ 24738 = (5 : ZMod 830098882477) ^ (12369 + 12369) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 12369 * (5 : ZMod 830098882477) ^ 12369 := by rw [pow_add]
          _ = 87456397323 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 830098882477) ^ 49477 = 205949803192 := by
        calc
          (5 : ZMod 830098882477) ^ 49477 = (5 : ZMod 830098882477) ^ (24738 + 24738 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 24738 * (5 : ZMod 830098882477) ^ 24738) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 205949803192 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 830098882477) ^ 98955 = 229689036629 := by
        calc
          (5 : ZMod 830098882477) ^ 98955 = (5 : ZMod 830098882477) ^ (49477 + 49477 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 49477 * (5 : ZMod 830098882477) ^ 49477) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 229689036629 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 830098882477) ^ 197910 = 688468417807 := by
        calc
          (5 : ZMod 830098882477) ^ 197910 = (5 : ZMod 830098882477) ^ (98955 + 98955) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 98955 * (5 : ZMod 830098882477) ^ 98955 := by rw [pow_add]
          _ = 688468417807 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 830098882477) ^ 395821 = 787329741605 := by
        calc
          (5 : ZMod 830098882477) ^ 395821 = (5 : ZMod 830098882477) ^ (197910 + 197910 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 197910 * (5 : ZMod 830098882477) ^ 197910) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 787329741605 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 830098882477) ^ 791643 = 306755860787 := by
        calc
          (5 : ZMod 830098882477) ^ 791643 = (5 : ZMod 830098882477) ^ (395821 + 395821 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 395821 * (5 : ZMod 830098882477) ^ 395821) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 306755860787 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 830098882477) ^ 1583287 = 567732822356 := by
        calc
          (5 : ZMod 830098882477) ^ 1583287 = (5 : ZMod 830098882477) ^ (791643 + 791643 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 791643 * (5 : ZMod 830098882477) ^ 791643) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 567732822356 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 830098882477) ^ 3166575 = 369012858033 := by
        calc
          (5 : ZMod 830098882477) ^ 3166575 = (5 : ZMod 830098882477) ^ (1583287 + 1583287 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1583287 * (5 : ZMod 830098882477) ^ 1583287) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 369012858033 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 830098882477) ^ 6333151 = 107647017379 := by
        calc
          (5 : ZMod 830098882477) ^ 6333151 = (5 : ZMod 830098882477) ^ (3166575 + 3166575 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 3166575 * (5 : ZMod 830098882477) ^ 3166575) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 107647017379 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 830098882477) ^ 12666303 = 430131890121 := by
        calc
          (5 : ZMod 830098882477) ^ 12666303 = (5 : ZMod 830098882477) ^ (6333151 + 6333151 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 6333151 * (5 : ZMod 830098882477) ^ 6333151) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 430131890121 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 830098882477) ^ 25332607 = 168591633766 := by
        calc
          (5 : ZMod 830098882477) ^ 25332607 = (5 : ZMod 830098882477) ^ (12666303 + 12666303 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 12666303 * (5 : ZMod 830098882477) ^ 12666303) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 168591633766 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 830098882477) ^ 50665214 = 553991366658 := by
        calc
          (5 : ZMod 830098882477) ^ 50665214 = (5 : ZMod 830098882477) ^ (25332607 + 25332607) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 25332607 * (5 : ZMod 830098882477) ^ 25332607 := by rw [pow_add]
          _ = 553991366658 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 830098882477) ^ 101330429 = 576676480173 := by
        calc
          (5 : ZMod 830098882477) ^ 101330429 = (5 : ZMod 830098882477) ^ (50665214 + 50665214 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 50665214 * (5 : ZMod 830098882477) ^ 50665214) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 576676480173 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 830098882477) ^ 202660859 = 374683908451 := by
        calc
          (5 : ZMod 830098882477) ^ 202660859 = (5 : ZMod 830098882477) ^ (101330429 + 101330429 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 101330429 * (5 : ZMod 830098882477) ^ 101330429) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 374683908451 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 830098882477) ^ 405321719 = 332011838711 := by
        calc
          (5 : ZMod 830098882477) ^ 405321719 = (5 : ZMod 830098882477) ^ (202660859 + 202660859 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 202660859 * (5 : ZMod 830098882477) ^ 202660859) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 332011838711 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 830098882477) ^ 810643439 = 701133377829 := by
        calc
          (5 : ZMod 830098882477) ^ 810643439 = (5 : ZMod 830098882477) ^ (405321719 + 405321719 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 405321719 * (5 : ZMod 830098882477) ^ 405321719) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 701133377829 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 830098882477) ^ 1621286879 = 778100720959 := by
        calc
          (5 : ZMod 830098882477) ^ 1621286879 = (5 : ZMod 830098882477) ^ (810643439 + 810643439 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 810643439 * (5 : ZMod 830098882477) ^ 810643439) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 778100720959 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 830098882477) ^ 3242573759 = 114025721914 := by
        calc
          (5 : ZMod 830098882477) ^ 3242573759 = (5 : ZMod 830098882477) ^ (1621286879 + 1621286879 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1621286879 * (5 : ZMod 830098882477) ^ 1621286879) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 114025721914 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 830098882477) ^ 6485147519 = 227264990427 := by
        calc
          (5 : ZMod 830098882477) ^ 6485147519 = (5 : ZMod 830098882477) ^ (3242573759 + 3242573759 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 3242573759 * (5 : ZMod 830098882477) ^ 3242573759) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 227264990427 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 830098882477) ^ 12970295038 = 144523650375 := by
        calc
          (5 : ZMod 830098882477) ^ 12970295038 = (5 : ZMod 830098882477) ^ (6485147519 + 6485147519) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 6485147519 * (5 : ZMod 830098882477) ^ 6485147519 := by rw [pow_add]
          _ = 144523650375 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 830098882477) ^ 25940590077 = 66541738307 := by
        calc
          (5 : ZMod 830098882477) ^ 25940590077 = (5 : ZMod 830098882477) ^ (12970295038 + 12970295038 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 12970295038 * (5 : ZMod 830098882477) ^ 12970295038) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 66541738307 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 830098882477) ^ 51881180154 = 694066343937 := by
        calc
          (5 : ZMod 830098882477) ^ 51881180154 = (5 : ZMod 830098882477) ^ (25940590077 + 25940590077) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 25940590077 * (5 : ZMod 830098882477) ^ 25940590077 := by rw [pow_add]
          _ = 694066343937 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 830098882477) ^ 103762360309 = 326485183428 := by
        calc
          (5 : ZMod 830098882477) ^ 103762360309 = (5 : ZMod 830098882477) ^ (51881180154 + 51881180154 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 51881180154 * (5 : ZMod 830098882477) ^ 51881180154) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 326485183428 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 830098882477) ^ 207524720619 = 250513871111 := by
        calc
          (5 : ZMod 830098882477) ^ 207524720619 = (5 : ZMod 830098882477) ^ (103762360309 + 103762360309 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 103762360309 * (5 : ZMod 830098882477) ^ 103762360309) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 250513871111 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 830098882477) ^ 415049441238 = 830098882476 := by
        calc
          (5 : ZMod 830098882477) ^ 415049441238 = (5 : ZMod 830098882477) ^ (207524720619 + 207524720619) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 207524720619 * (5 : ZMod 830098882477) ^ 207524720619 := by rw [pow_add]
          _ = 830098882476 := by rw [factor_0_37]; decide
      change (5 : ZMod 830098882477) ^ 415049441238 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (5 : ZMod 830098882477) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 830098882477) ^ 2 = 25 := by
        calc
          (5 : ZMod 830098882477) ^ 2 = (5 : ZMod 830098882477) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1 * (5 : ZMod 830098882477) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 830098882477) ^ 4 = 625 := by
        calc
          (5 : ZMod 830098882477) ^ 4 = (5 : ZMod 830098882477) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 2 * (5 : ZMod 830098882477) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 830098882477) ^ 8 = 390625 := by
        calc
          (5 : ZMod 830098882477) ^ 8 = (5 : ZMod 830098882477) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 4 * (5 : ZMod 830098882477) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 830098882477) ^ 16 = 152587890625 := by
        calc
          (5 : ZMod 830098882477) ^ 16 = (5 : ZMod 830098882477) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 8 * (5 : ZMod 830098882477) ^ 8 := by rw [pow_add]
          _ = 152587890625 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 830098882477) ^ 32 = 789204266702 := by
        calc
          (5 : ZMod 830098882477) ^ 32 = (5 : ZMod 830098882477) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 16 * (5 : ZMod 830098882477) ^ 16 := by rw [pow_add]
          _ = 789204266702 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 830098882477) ^ 64 = 715944879724 := by
        calc
          (5 : ZMod 830098882477) ^ 64 = (5 : ZMod 830098882477) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 32 * (5 : ZMod 830098882477) ^ 32 := by rw [pow_add]
          _ = 715944879724 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 830098882477) ^ 128 = 151988747067 := by
        calc
          (5 : ZMod 830098882477) ^ 128 = (5 : ZMod 830098882477) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 64 * (5 : ZMod 830098882477) ^ 64 := by rw [pow_add]
          _ = 151988747067 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 830098882477) ^ 257 = 313967887973 := by
        calc
          (5 : ZMod 830098882477) ^ 257 = (5 : ZMod 830098882477) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 128 * (5 : ZMod 830098882477) ^ 128) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 313967887973 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 830098882477) ^ 515 = 418197858881 := by
        calc
          (5 : ZMod 830098882477) ^ 515 = (5 : ZMod 830098882477) ^ (257 + 257 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 257 * (5 : ZMod 830098882477) ^ 257) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 418197858881 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 830098882477) ^ 1030 = 610056279111 := by
        calc
          (5 : ZMod 830098882477) ^ 1030 = (5 : ZMod 830098882477) ^ (515 + 515) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 515 * (5 : ZMod 830098882477) ^ 515 := by rw [pow_add]
          _ = 610056279111 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 830098882477) ^ 2061 = 504066628198 := by
        calc
          (5 : ZMod 830098882477) ^ 2061 = (5 : ZMod 830098882477) ^ (1030 + 1030 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1030 * (5 : ZMod 830098882477) ^ 1030) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 504066628198 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 830098882477) ^ 4123 = 400238409063 := by
        calc
          (5 : ZMod 830098882477) ^ 4123 = (5 : ZMod 830098882477) ^ (2061 + 2061 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2061 * (5 : ZMod 830098882477) ^ 2061) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 400238409063 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 830098882477) ^ 8246 = 27785048603 := by
        calc
          (5 : ZMod 830098882477) ^ 8246 = (5 : ZMod 830098882477) ^ (4123 + 4123) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 4123 * (5 : ZMod 830098882477) ^ 4123 := by rw [pow_add]
          _ = 27785048603 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 830098882477) ^ 16492 = 436601069160 := by
        calc
          (5 : ZMod 830098882477) ^ 16492 = (5 : ZMod 830098882477) ^ (8246 + 8246) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 8246 * (5 : ZMod 830098882477) ^ 8246 := by rw [pow_add]
          _ = 436601069160 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 830098882477) ^ 32985 = 644356663161 := by
        calc
          (5 : ZMod 830098882477) ^ 32985 = (5 : ZMod 830098882477) ^ (16492 + 16492 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 16492 * (5 : ZMod 830098882477) ^ 16492) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 644356663161 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 830098882477) ^ 65970 = 730640770573 := by
        calc
          (5 : ZMod 830098882477) ^ 65970 = (5 : ZMod 830098882477) ^ (32985 + 32985) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 32985 * (5 : ZMod 830098882477) ^ 32985 := by rw [pow_add]
          _ = 730640770573 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 830098882477) ^ 131940 = 146087978060 := by
        calc
          (5 : ZMod 830098882477) ^ 131940 = (5 : ZMod 830098882477) ^ (65970 + 65970) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 65970 * (5 : ZMod 830098882477) ^ 65970 := by rw [pow_add]
          _ = 146087978060 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 830098882477) ^ 263881 = 541061474046 := by
        calc
          (5 : ZMod 830098882477) ^ 263881 = (5 : ZMod 830098882477) ^ (131940 + 131940 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 131940 * (5 : ZMod 830098882477) ^ 131940) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 541061474046 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 830098882477) ^ 527762 = 384032840591 := by
        calc
          (5 : ZMod 830098882477) ^ 527762 = (5 : ZMod 830098882477) ^ (263881 + 263881) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 263881 * (5 : ZMod 830098882477) ^ 263881 := by rw [pow_add]
          _ = 384032840591 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 830098882477) ^ 1055525 = 372227541233 := by
        calc
          (5 : ZMod 830098882477) ^ 1055525 = (5 : ZMod 830098882477) ^ (527762 + 527762 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 527762 * (5 : ZMod 830098882477) ^ 527762) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 372227541233 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 830098882477) ^ 2111050 = 802751543861 := by
        calc
          (5 : ZMod 830098882477) ^ 2111050 = (5 : ZMod 830098882477) ^ (1055525 + 1055525) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1055525 * (5 : ZMod 830098882477) ^ 1055525 := by rw [pow_add]
          _ = 802751543861 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 830098882477) ^ 4222101 = 715022778493 := by
        calc
          (5 : ZMod 830098882477) ^ 4222101 = (5 : ZMod 830098882477) ^ (2111050 + 2111050 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2111050 * (5 : ZMod 830098882477) ^ 2111050) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 715022778493 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 830098882477) ^ 8444202 = 71734599255 := by
        calc
          (5 : ZMod 830098882477) ^ 8444202 = (5 : ZMod 830098882477) ^ (4222101 + 4222101) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 4222101 * (5 : ZMod 830098882477) ^ 4222101 := by rw [pow_add]
          _ = 71734599255 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 830098882477) ^ 16888404 = 440934600330 := by
        calc
          (5 : ZMod 830098882477) ^ 16888404 = (5 : ZMod 830098882477) ^ (8444202 + 8444202) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 8444202 * (5 : ZMod 830098882477) ^ 8444202 := by rw [pow_add]
          _ = 440934600330 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 830098882477) ^ 33776809 = 537688769771 := by
        calc
          (5 : ZMod 830098882477) ^ 33776809 = (5 : ZMod 830098882477) ^ (16888404 + 16888404 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 16888404 * (5 : ZMod 830098882477) ^ 16888404) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 537688769771 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 830098882477) ^ 67553619 = 801685016528 := by
        calc
          (5 : ZMod 830098882477) ^ 67553619 = (5 : ZMod 830098882477) ^ (33776809 + 33776809 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 33776809 * (5 : ZMod 830098882477) ^ 33776809) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 801685016528 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 830098882477) ^ 135107239 = 762010367045 := by
        calc
          (5 : ZMod 830098882477) ^ 135107239 = (5 : ZMod 830098882477) ^ (67553619 + 67553619 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 67553619 * (5 : ZMod 830098882477) ^ 67553619) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 762010367045 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 830098882477) ^ 270214479 = 655847057479 := by
        calc
          (5 : ZMod 830098882477) ^ 270214479 = (5 : ZMod 830098882477) ^ (135107239 + 135107239 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 135107239 * (5 : ZMod 830098882477) ^ 135107239) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 655847057479 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 830098882477) ^ 540428959 = 285203420871 := by
        calc
          (5 : ZMod 830098882477) ^ 540428959 = (5 : ZMod 830098882477) ^ (270214479 + 270214479 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 270214479 * (5 : ZMod 830098882477) ^ 270214479) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 285203420871 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 830098882477) ^ 1080857919 = 628634562560 := by
        calc
          (5 : ZMod 830098882477) ^ 1080857919 = (5 : ZMod 830098882477) ^ (540428959 + 540428959 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 540428959 * (5 : ZMod 830098882477) ^ 540428959) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 628634562560 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 830098882477) ^ 2161715839 = 200580325720 := by
        calc
          (5 : ZMod 830098882477) ^ 2161715839 = (5 : ZMod 830098882477) ^ (1080857919 + 1080857919 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1080857919 * (5 : ZMod 830098882477) ^ 1080857919) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 200580325720 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 830098882477) ^ 4323431679 = 148833666686 := by
        calc
          (5 : ZMod 830098882477) ^ 4323431679 = (5 : ZMod 830098882477) ^ (2161715839 + 2161715839 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2161715839 * (5 : ZMod 830098882477) ^ 2161715839) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 148833666686 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 830098882477) ^ 8646863359 = 740422408156 := by
        calc
          (5 : ZMod 830098882477) ^ 8646863359 = (5 : ZMod 830098882477) ^ (4323431679 + 4323431679 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 4323431679 * (5 : ZMod 830098882477) ^ 4323431679) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 740422408156 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 830098882477) ^ 17293726718 = 576673823988 := by
        calc
          (5 : ZMod 830098882477) ^ 17293726718 = (5 : ZMod 830098882477) ^ (8646863359 + 8646863359) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 8646863359 * (5 : ZMod 830098882477) ^ 8646863359 := by rw [pow_add]
          _ = 576673823988 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 830098882477) ^ 34587453436 = 98857351522 := by
        calc
          (5 : ZMod 830098882477) ^ 34587453436 = (5 : ZMod 830098882477) ^ (17293726718 + 17293726718) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 17293726718 * (5 : ZMod 830098882477) ^ 17293726718 := by rw [pow_add]
          _ = 98857351522 := by rw [factor_1_34]; decide
      have factor_1_36 : (5 : ZMod 830098882477) ^ 69174906873 = 54659110947 := by
        calc
          (5 : ZMod 830098882477) ^ 69174906873 = (5 : ZMod 830098882477) ^ (34587453436 + 34587453436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 34587453436 * (5 : ZMod 830098882477) ^ 34587453436) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 54659110947 := by rw [factor_1_35]; decide
      have factor_1_37 : (5 : ZMod 830098882477) ^ 138349813746 = 359302525619 := by
        calc
          (5 : ZMod 830098882477) ^ 138349813746 = (5 : ZMod 830098882477) ^ (69174906873 + 69174906873) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 69174906873 * (5 : ZMod 830098882477) ^ 69174906873 := by rw [pow_add]
          _ = 359302525619 := by rw [factor_1_36]; decide
      have factor_1_38 : (5 : ZMod 830098882477) ^ 276699627492 = 359302525618 := by
        calc
          (5 : ZMod 830098882477) ^ 276699627492 = (5 : ZMod 830098882477) ^ (138349813746 + 138349813746) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 138349813746 * (5 : ZMod 830098882477) ^ 138349813746 := by rw [pow_add]
          _ = 359302525618 := by rw [factor_1_37]; decide
      change (5 : ZMod 830098882477) ^ 276699627492 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (5 : ZMod 830098882477) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 830098882477) ^ 2 = 25 := by
        calc
          (5 : ZMod 830098882477) ^ 2 = (5 : ZMod 830098882477) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1 * (5 : ZMod 830098882477) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 830098882477) ^ 5 = 3125 := by
        calc
          (5 : ZMod 830098882477) ^ 5 = (5 : ZMod 830098882477) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2 * (5 : ZMod 830098882477) ^ 2) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 830098882477) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 830098882477) ^ 11 = (5 : ZMod 830098882477) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 5 * (5 : ZMod 830098882477) ^ 5) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 830098882477) ^ 22 = 141800541681 := by
        calc
          (5 : ZMod 830098882477) ^ 22 = (5 : ZMod 830098882477) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 11 * (5 : ZMod 830098882477) ^ 11 := by rw [pow_add]
          _ = 141800541681 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 830098882477) ^ 45 = 826389572451 := by
        calc
          (5 : ZMod 830098882477) ^ 45 = (5 : ZMod 830098882477) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 22 * (5 : ZMod 830098882477) ^ 22) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 826389572451 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 830098882477) ^ 90 = 581050773206 := by
        calc
          (5 : ZMod 830098882477) ^ 90 = (5 : ZMod 830098882477) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 45 * (5 : ZMod 830098882477) ^ 45 := by rw [pow_add]
          _ = 581050773206 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 830098882477) ^ 181 = 420971682886 := by
        calc
          (5 : ZMod 830098882477) ^ 181 = (5 : ZMod 830098882477) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 90 * (5 : ZMod 830098882477) ^ 90) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 420971682886 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 830098882477) ^ 363 = 400763358859 := by
        calc
          (5 : ZMod 830098882477) ^ 363 = (5 : ZMod 830098882477) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 181 * (5 : ZMod 830098882477) ^ 181) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 400763358859 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 830098882477) ^ 727 = 177484836457 := by
        calc
          (5 : ZMod 830098882477) ^ 727 = (5 : ZMod 830098882477) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 363 * (5 : ZMod 830098882477) ^ 363) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 177484836457 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 830098882477) ^ 1455 = 503517234114 := by
        calc
          (5 : ZMod 830098882477) ^ 1455 = (5 : ZMod 830098882477) ^ (727 + 727 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 727 * (5 : ZMod 830098882477) ^ 727) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 503517234114 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 830098882477) ^ 2910 = 360521799427 := by
        calc
          (5 : ZMod 830098882477) ^ 2910 = (5 : ZMod 830098882477) ^ (1455 + 1455) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1455 * (5 : ZMod 830098882477) ^ 1455 := by rw [pow_add]
          _ = 360521799427 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 830098882477) ^ 5820 = 458025299088 := by
        calc
          (5 : ZMod 830098882477) ^ 5820 = (5 : ZMod 830098882477) ^ (2910 + 2910) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 2910 * (5 : ZMod 830098882477) ^ 2910 := by rw [pow_add]
          _ = 458025299088 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 830098882477) ^ 11641 = 590883042586 := by
        calc
          (5 : ZMod 830098882477) ^ 11641 = (5 : ZMod 830098882477) ^ (5820 + 5820 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 5820 * (5 : ZMod 830098882477) ^ 5820) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 590883042586 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 830098882477) ^ 23283 = 656176243240 := by
        calc
          (5 : ZMod 830098882477) ^ 23283 = (5 : ZMod 830098882477) ^ (11641 + 11641 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 11641 * (5 : ZMod 830098882477) ^ 11641) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 656176243240 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 830098882477) ^ 46567 = 357132964834 := by
        calc
          (5 : ZMod 830098882477) ^ 46567 = (5 : ZMod 830098882477) ^ (23283 + 23283 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 23283 * (5 : ZMod 830098882477) ^ 23283) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 357132964834 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 830098882477) ^ 93134 = 129524579396 := by
        calc
          (5 : ZMod 830098882477) ^ 93134 = (5 : ZMod 830098882477) ^ (46567 + 46567) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 46567 * (5 : ZMod 830098882477) ^ 46567 := by rw [pow_add]
          _ = 129524579396 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 830098882477) ^ 186269 = 389232161591 := by
        calc
          (5 : ZMod 830098882477) ^ 186269 = (5 : ZMod 830098882477) ^ (93134 + 93134 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 93134 * (5 : ZMod 830098882477) ^ 93134) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 389232161591 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 830098882477) ^ 372538 = 374711427802 := by
        calc
          (5 : ZMod 830098882477) ^ 372538 = (5 : ZMod 830098882477) ^ (186269 + 186269) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 186269 * (5 : ZMod 830098882477) ^ 186269 := by rw [pow_add]
          _ = 374711427802 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 830098882477) ^ 745076 = 820652974161 := by
        calc
          (5 : ZMod 830098882477) ^ 745076 = (5 : ZMod 830098882477) ^ (372538 + 372538) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 372538 * (5 : ZMod 830098882477) ^ 372538 := by rw [pow_add]
          _ = 820652974161 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 830098882477) ^ 1490153 = 61687732120 := by
        calc
          (5 : ZMod 830098882477) ^ 1490153 = (5 : ZMod 830098882477) ^ (745076 + 745076 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 745076 * (5 : ZMod 830098882477) ^ 745076) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 61687732120 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 830098882477) ^ 2980306 = 380723176987 := by
        calc
          (5 : ZMod 830098882477) ^ 2980306 = (5 : ZMod 830098882477) ^ (1490153 + 1490153) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1490153 * (5 : ZMod 830098882477) ^ 1490153 := by rw [pow_add]
          _ = 380723176987 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 830098882477) ^ 5960613 = 194031851338 := by
        calc
          (5 : ZMod 830098882477) ^ 5960613 = (5 : ZMod 830098882477) ^ (2980306 + 2980306 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2980306 * (5 : ZMod 830098882477) ^ 2980306) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 194031851338 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 830098882477) ^ 11921227 = 528718020329 := by
        calc
          (5 : ZMod 830098882477) ^ 11921227 = (5 : ZMod 830098882477) ^ (5960613 + 5960613 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 5960613 * (5 : ZMod 830098882477) ^ 5960613) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 528718020329 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 830098882477) ^ 23842454 = 179145896926 := by
        calc
          (5 : ZMod 830098882477) ^ 23842454 = (5 : ZMod 830098882477) ^ (11921227 + 11921227) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 11921227 * (5 : ZMod 830098882477) ^ 11921227 := by rw [pow_add]
          _ = 179145896926 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 830098882477) ^ 47684908 = 161434706374 := by
        calc
          (5 : ZMod 830098882477) ^ 47684908 = (5 : ZMod 830098882477) ^ (23842454 + 23842454) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 23842454 * (5 : ZMod 830098882477) ^ 23842454 := by rw [pow_add]
          _ = 161434706374 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 830098882477) ^ 95369816 = 808002254123 := by
        calc
          (5 : ZMod 830098882477) ^ 95369816 = (5 : ZMod 830098882477) ^ (47684908 + 47684908) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 47684908 * (5 : ZMod 830098882477) ^ 47684908 := by rw [pow_add]
          _ = 808002254123 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 830098882477) ^ 190739632 = 390446353749 := by
        calc
          (5 : ZMod 830098882477) ^ 190739632 = (5 : ZMod 830098882477) ^ (95369816 + 95369816) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 95369816 * (5 : ZMod 830098882477) ^ 95369816 := by rw [pow_add]
          _ = 390446353749 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 830098882477) ^ 381479265 = 232728555098 := by
        calc
          (5 : ZMod 830098882477) ^ 381479265 = (5 : ZMod 830098882477) ^ (190739632 + 190739632 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 190739632 * (5 : ZMod 830098882477) ^ 190739632) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 232728555098 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 830098882477) ^ 762958531 = 30524620067 := by
        calc
          (5 : ZMod 830098882477) ^ 762958531 = (5 : ZMod 830098882477) ^ (381479265 + 381479265 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 381479265 * (5 : ZMod 830098882477) ^ 381479265) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 30524620067 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 830098882477) ^ 1525917063 = 173095474874 := by
        calc
          (5 : ZMod 830098882477) ^ 1525917063 = (5 : ZMod 830098882477) ^ (762958531 + 762958531 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 762958531 * (5 : ZMod 830098882477) ^ 762958531) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 173095474874 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 830098882477) ^ 3051834126 = 617106882495 := by
        calc
          (5 : ZMod 830098882477) ^ 3051834126 = (5 : ZMod 830098882477) ^ (1525917063 + 1525917063) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1525917063 * (5 : ZMod 830098882477) ^ 1525917063 := by rw [pow_add]
          _ = 617106882495 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 830098882477) ^ 6103668253 = 337067500923 := by
        calc
          (5 : ZMod 830098882477) ^ 6103668253 = (5 : ZMod 830098882477) ^ (3051834126 + 3051834126 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 3051834126 * (5 : ZMod 830098882477) ^ 3051834126) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 337067500923 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 830098882477) ^ 12207336507 = 566325721407 := by
        calc
          (5 : ZMod 830098882477) ^ 12207336507 = (5 : ZMod 830098882477) ^ (6103668253 + 6103668253 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 6103668253 * (5 : ZMod 830098882477) ^ 6103668253) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 566325721407 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 830098882477) ^ 24414673014 = 326026698376 := by
        calc
          (5 : ZMod 830098882477) ^ 24414673014 = (5 : ZMod 830098882477) ^ (12207336507 + 12207336507) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 12207336507 * (5 : ZMod 830098882477) ^ 12207336507 := by rw [pow_add]
          _ = 326026698376 := by rw [factor_2_33]; decide
      have factor_2_35 : (5 : ZMod 830098882477) ^ 48829346028 = 434761465110 := by
        calc
          (5 : ZMod 830098882477) ^ 48829346028 = (5 : ZMod 830098882477) ^ (24414673014 + 24414673014) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 24414673014 * (5 : ZMod 830098882477) ^ 24414673014 := by rw [pow_add]
          _ = 434761465110 := by rw [factor_2_34]; decide
      change (5 : ZMod 830098882477) ^ 48829346028 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (5 : ZMod 830098882477) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 830098882477) ^ 2 = 25 := by
        calc
          (5 : ZMod 830098882477) ^ 2 = (5 : ZMod 830098882477) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1 * (5 : ZMod 830098882477) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 830098882477) ^ 5 = 3125 := by
        calc
          (5 : ZMod 830098882477) ^ 5 = (5 : ZMod 830098882477) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2 * (5 : ZMod 830098882477) ^ 2) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 830098882477) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 830098882477) ^ 10 = (5 : ZMod 830098882477) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 5 * (5 : ZMod 830098882477) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 830098882477) ^ 21 = 360399661327 := by
        calc
          (5 : ZMod 830098882477) ^ 21 = (5 : ZMod 830098882477) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 10 * (5 : ZMod 830098882477) ^ 10) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 360399661327 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 830098882477) ^ 43 = 431503046487 := by
        calc
          (5 : ZMod 830098882477) ^ 43 = (5 : ZMod 830098882477) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 21 * (5 : ZMod 830098882477) ^ 21) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 431503046487 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 830098882477) ^ 87 = 316765585997 := by
        calc
          (5 : ZMod 830098882477) ^ 87 = (5 : ZMod 830098882477) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 43 * (5 : ZMod 830098882477) ^ 43) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 316765585997 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 830098882477) ^ 174 = 22127191616 := by
        calc
          (5 : ZMod 830098882477) ^ 174 = (5 : ZMod 830098882477) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 87 * (5 : ZMod 830098882477) ^ 87 := by rw [pow_add]
          _ = 22127191616 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 830098882477) ^ 348 = 309558353576 := by
        calc
          (5 : ZMod 830098882477) ^ 348 = (5 : ZMod 830098882477) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 174 * (5 : ZMod 830098882477) ^ 174 := by rw [pow_add]
          _ = 309558353576 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 830098882477) ^ 696 = 64375905391 := by
        calc
          (5 : ZMod 830098882477) ^ 696 = (5 : ZMod 830098882477) ^ (348 + 348) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 348 * (5 : ZMod 830098882477) ^ 348 := by rw [pow_add]
          _ = 64375905391 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 830098882477) ^ 1393 = 477954154553 := by
        calc
          (5 : ZMod 830098882477) ^ 1393 = (5 : ZMod 830098882477) ^ (696 + 696 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 696 * (5 : ZMod 830098882477) ^ 696) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 477954154553 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 830098882477) ^ 2787 = 795310755388 := by
        calc
          (5 : ZMod 830098882477) ^ 2787 = (5 : ZMod 830098882477) ^ (1393 + 1393 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1393 * (5 : ZMod 830098882477) ^ 1393) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 795310755388 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 830098882477) ^ 5574 = 623293721228 := by
        calc
          (5 : ZMod 830098882477) ^ 5574 = (5 : ZMod 830098882477) ^ (2787 + 2787) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 2787 * (5 : ZMod 830098882477) ^ 2787 := by rw [pow_add]
          _ = 623293721228 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 830098882477) ^ 11149 = 245059006586 := by
        calc
          (5 : ZMod 830098882477) ^ 11149 = (5 : ZMod 830098882477) ^ (5574 + 5574 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 5574 * (5 : ZMod 830098882477) ^ 5574) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 245059006586 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 830098882477) ^ 22299 = 384221278319 := by
        calc
          (5 : ZMod 830098882477) ^ 22299 = (5 : ZMod 830098882477) ^ (11149 + 11149 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 11149 * (5 : ZMod 830098882477) ^ 11149) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 384221278319 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 830098882477) ^ 44599 = 247922314551 := by
        calc
          (5 : ZMod 830098882477) ^ 44599 = (5 : ZMod 830098882477) ^ (22299 + 22299 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 22299 * (5 : ZMod 830098882477) ^ 22299) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 247922314551 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 830098882477) ^ 89199 = 562894666701 := by
        calc
          (5 : ZMod 830098882477) ^ 89199 = (5 : ZMod 830098882477) ^ (44599 + 44599 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 44599 * (5 : ZMod 830098882477) ^ 44599) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 562894666701 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 830098882477) ^ 178398 = 446633135770 := by
        calc
          (5 : ZMod 830098882477) ^ 178398 = (5 : ZMod 830098882477) ^ (89199 + 89199) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 89199 * (5 : ZMod 830098882477) ^ 89199 := by rw [pow_add]
          _ = 446633135770 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 830098882477) ^ 356797 = 254785440073 := by
        calc
          (5 : ZMod 830098882477) ^ 356797 = (5 : ZMod 830098882477) ^ (178398 + 178398 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 178398 * (5 : ZMod 830098882477) ^ 178398) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 254785440073 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 830098882477) ^ 713594 = 316115455878 := by
        calc
          (5 : ZMod 830098882477) ^ 713594 = (5 : ZMod 830098882477) ^ (356797 + 356797) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 356797 * (5 : ZMod 830098882477) ^ 356797 := by rw [pow_add]
          _ = 316115455878 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 830098882477) ^ 1427189 = 171099119369 := by
        calc
          (5 : ZMod 830098882477) ^ 1427189 = (5 : ZMod 830098882477) ^ (713594 + 713594 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 713594 * (5 : ZMod 830098882477) ^ 713594) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 171099119369 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 830098882477) ^ 2854378 = 501994856411 := by
        calc
          (5 : ZMod 830098882477) ^ 2854378 = (5 : ZMod 830098882477) ^ (1427189 + 1427189) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1427189 * (5 : ZMod 830098882477) ^ 1427189 := by rw [pow_add]
          _ = 501994856411 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 830098882477) ^ 5708756 = 798938108162 := by
        calc
          (5 : ZMod 830098882477) ^ 5708756 = (5 : ZMod 830098882477) ^ (2854378 + 2854378) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 2854378 * (5 : ZMod 830098882477) ^ 2854378 := by rw [pow_add]
          _ = 798938108162 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 830098882477) ^ 11417513 = 168727658387 := by
        calc
          (5 : ZMod 830098882477) ^ 11417513 = (5 : ZMod 830098882477) ^ (5708756 + 5708756 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 5708756 * (5 : ZMod 830098882477) ^ 5708756) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 168727658387 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 830098882477) ^ 22835026 = 414593171039 := by
        calc
          (5 : ZMod 830098882477) ^ 22835026 = (5 : ZMod 830098882477) ^ (11417513 + 11417513) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 11417513 * (5 : ZMod 830098882477) ^ 11417513 := by rw [pow_add]
          _ = 414593171039 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 830098882477) ^ 45670052 = 128492877397 := by
        calc
          (5 : ZMod 830098882477) ^ 45670052 = (5 : ZMod 830098882477) ^ (22835026 + 22835026) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 22835026 * (5 : ZMod 830098882477) ^ 22835026 := by rw [pow_add]
          _ = 128492877397 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 830098882477) ^ 91340105 = 667041339750 := by
        calc
          (5 : ZMod 830098882477) ^ 91340105 = (5 : ZMod 830098882477) ^ (45670052 + 45670052 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 45670052 * (5 : ZMod 830098882477) ^ 45670052) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 667041339750 := by rw [factor_3_25]; decide
      have factor_3_27 : (5 : ZMod 830098882477) ^ 182680211 = 705198163393 := by
        calc
          (5 : ZMod 830098882477) ^ 182680211 = (5 : ZMod 830098882477) ^ (91340105 + 91340105 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 91340105 * (5 : ZMod 830098882477) ^ 91340105) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 705198163393 := by rw [factor_3_26]; decide
      have factor_3_28 : (5 : ZMod 830098882477) ^ 365360423 = 803527857197 := by
        calc
          (5 : ZMod 830098882477) ^ 365360423 = (5 : ZMod 830098882477) ^ (182680211 + 182680211 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 182680211 * (5 : ZMod 830098882477) ^ 182680211) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 803527857197 := by rw [factor_3_27]; decide
      have factor_3_29 : (5 : ZMod 830098882477) ^ 730720847 = 446795204709 := by
        calc
          (5 : ZMod 830098882477) ^ 730720847 = (5 : ZMod 830098882477) ^ (365360423 + 365360423 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 365360423 * (5 : ZMod 830098882477) ^ 365360423) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 446795204709 := by rw [factor_3_28]; decide
      have factor_3_30 : (5 : ZMod 830098882477) ^ 1461441694 = 572792377336 := by
        calc
          (5 : ZMod 830098882477) ^ 1461441694 = (5 : ZMod 830098882477) ^ (730720847 + 730720847) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 730720847 * (5 : ZMod 830098882477) ^ 730720847 := by rw [pow_add]
          _ = 572792377336 := by rw [factor_3_29]; decide
      have factor_3_31 : (5 : ZMod 830098882477) ^ 2922883389 = 343561479542 := by
        calc
          (5 : ZMod 830098882477) ^ 2922883389 = (5 : ZMod 830098882477) ^ (1461441694 + 1461441694 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1461441694 * (5 : ZMod 830098882477) ^ 1461441694) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 343561479542 := by rw [factor_3_30]; decide
      have factor_3_32 : (5 : ZMod 830098882477) ^ 5845766778 = 187293804832 := by
        calc
          (5 : ZMod 830098882477) ^ 5845766778 = (5 : ZMod 830098882477) ^ (2922883389 + 2922883389) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 2922883389 * (5 : ZMod 830098882477) ^ 2922883389 := by rw [pow_add]
          _ = 187293804832 := by rw [factor_3_31]; decide
      have factor_3_33 : (5 : ZMod 830098882477) ^ 11691533556 = 35718233982 := by
        calc
          (5 : ZMod 830098882477) ^ 11691533556 = (5 : ZMod 830098882477) ^ (5845766778 + 5845766778) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 5845766778 * (5 : ZMod 830098882477) ^ 5845766778 := by rw [pow_add]
          _ = 35718233982 := by rw [factor_3_32]; decide
      change (5 : ZMod 830098882477) ^ 11691533556 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (5 : ZMod 830098882477) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 830098882477) ^ 2 = 25 := by
        calc
          (5 : ZMod 830098882477) ^ 2 = (5 : ZMod 830098882477) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 1 * (5 : ZMod 830098882477) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 830098882477) ^ 5 = 3125 := by
        calc
          (5 : ZMod 830098882477) ^ 5 = (5 : ZMod 830098882477) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2 * (5 : ZMod 830098882477) ^ 2) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 830098882477) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 830098882477) ^ 10 = (5 : ZMod 830098882477) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 5 * (5 : ZMod 830098882477) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 830098882477) ^ 21 = 360399661327 := by
        calc
          (5 : ZMod 830098882477) ^ 21 = (5 : ZMod 830098882477) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 10 * (5 : ZMod 830098882477) ^ 10) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 360399661327 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 830098882477) ^ 42 = 750379715279 := by
        calc
          (5 : ZMod 830098882477) ^ 42 = (5 : ZMod 830098882477) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 21 * (5 : ZMod 830098882477) ^ 21 := by rw [pow_add]
          _ = 750379715279 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 830098882477) ^ 84 = 759584305507 := by
        calc
          (5 : ZMod 830098882477) ^ 84 = (5 : ZMod 830098882477) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 42 * (5 : ZMod 830098882477) ^ 42 := by rw [pow_add]
          _ = 759584305507 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 830098882477) ^ 169 = 256872878895 := by
        calc
          (5 : ZMod 830098882477) ^ 169 = (5 : ZMod 830098882477) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 84 * (5 : ZMod 830098882477) ^ 84) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 256872878895 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 830098882477) ^ 339 = 341968809772 := by
        calc
          (5 : ZMod 830098882477) ^ 339 = (5 : ZMod 830098882477) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 169 * (5 : ZMod 830098882477) ^ 169) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 341968809772 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 830098882477) ^ 678 = 111492922263 := by
        calc
          (5 : ZMod 830098882477) ^ 678 = (5 : ZMod 830098882477) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 339 * (5 : ZMod 830098882477) ^ 339 := by rw [pow_add]
          _ = 111492922263 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 830098882477) ^ 1357 = 312246272636 := by
        calc
          (5 : ZMod 830098882477) ^ 1357 = (5 : ZMod 830098882477) ^ (678 + 678 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 678 * (5 : ZMod 830098882477) ^ 678) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 312246272636 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 830098882477) ^ 2715 = 306294841215 := by
        calc
          (5 : ZMod 830098882477) ^ 2715 = (5 : ZMod 830098882477) ^ (1357 + 1357 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 1357 * (5 : ZMod 830098882477) ^ 1357) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 306294841215 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 830098882477) ^ 5431 = 499343533570 := by
        calc
          (5 : ZMod 830098882477) ^ 5431 = (5 : ZMod 830098882477) ^ (2715 + 2715 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 2715 * (5 : ZMod 830098882477) ^ 2715) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 499343533570 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 830098882477) ^ 10863 = 3650361254 := by
        calc
          (5 : ZMod 830098882477) ^ 10863 = (5 : ZMod 830098882477) ^ (5431 + 5431 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = ((5 : ZMod 830098882477) ^ 5431 * (5 : ZMod 830098882477) ^ 5431) * (5 : ZMod 830098882477) := by rw [pow_succ, pow_add]
          _ = 3650361254 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 830098882477) ^ 21726 = 706807766803 := by
        calc
          (5 : ZMod 830098882477) ^ 21726 = (5 : ZMod 830098882477) ^ (10863 + 10863) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 10863 * (5 : ZMod 830098882477) ^ 10863 := by rw [pow_add]
          _ = 706807766803 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 830098882477) ^ 43452 = 331824164797 := by
        calc
          (5 : ZMod 830098882477) ^ 43452 = (5 : ZMod 830098882477) ^ (21726 + 21726) :=
            congrArg (fun n : ℕ => (5 : ZMod 830098882477) ^ n) (by norm_num)
          _ = (5 : ZMod 830098882477) ^ 21726 * (5 : ZMod 830098882477) ^ 21726 := by rw [pow_add]
          _ = 331824164797 := by rw [factor_4_14]; decide
      change (5 : ZMod 830098882477) ^ 43452 ≠ 1
      rw [factor_4_15]
      decide

#print axioms prime_lucas_830098882477

end TotientTailPeriodKiller
end Erdos249257
