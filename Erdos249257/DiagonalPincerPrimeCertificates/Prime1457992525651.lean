import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1457992525651 : Nat.Prime 1457992525651 := by
  apply lucas_primality 1457992525651 (2 : ZMod 1457992525651)
  ·
      have fermat_0 : (2 : ZMod 1457992525651) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1457992525651) ^ 2 = 4 := by
        calc
          (2 : ZMod 1457992525651) ^ 2 = (2 : ZMod 1457992525651) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1 * (2 : ZMod 1457992525651) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1457992525651) ^ 5 = 32 := by
        calc
          (2 : ZMod 1457992525651) ^ 5 = (2 : ZMod 1457992525651) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2 * (2 : ZMod 1457992525651) ^ 2) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1457992525651) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1457992525651) ^ 10 = (2 : ZMod 1457992525651) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5 * (2 : ZMod 1457992525651) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1457992525651) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1457992525651) ^ 21 = (2 : ZMod 1457992525651) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 10 * (2 : ZMod 1457992525651) ^ 10) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1457992525651) ^ 42 = 24068934151 := by
        calc
          (2 : ZMod 1457992525651) ^ 42 = (2 : ZMod 1457992525651) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 21 * (2 : ZMod 1457992525651) ^ 21 := by rw [pow_add]
          _ = 24068934151 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1457992525651) ^ 84 = 858554029690 := by
        calc
          (2 : ZMod 1457992525651) ^ 84 = (2 : ZMod 1457992525651) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 42 * (2 : ZMod 1457992525651) ^ 42 := by rw [pow_add]
          _ = 858554029690 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1457992525651) ^ 169 = 62250263588 := by
        calc
          (2 : ZMod 1457992525651) ^ 169 = (2 : ZMod 1457992525651) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 84 * (2 : ZMod 1457992525651) ^ 84) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 62250263588 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1457992525651) ^ 339 = 451141312902 := by
        calc
          (2 : ZMod 1457992525651) ^ 339 = (2 : ZMod 1457992525651) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 169 * (2 : ZMod 1457992525651) ^ 169) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 451141312902 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1457992525651) ^ 678 = 925089733591 := by
        calc
          (2 : ZMod 1457992525651) ^ 678 = (2 : ZMod 1457992525651) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 339 * (2 : ZMod 1457992525651) ^ 339 := by rw [pow_add]
          _ = 925089733591 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1457992525651) ^ 1357 = 593403594650 := by
        calc
          (2 : ZMod 1457992525651) ^ 1357 = (2 : ZMod 1457992525651) ^ (678 + 678 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 678 * (2 : ZMod 1457992525651) ^ 678) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 593403594650 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1457992525651) ^ 2715 = 920151713123 := by
        calc
          (2 : ZMod 1457992525651) ^ 2715 = (2 : ZMod 1457992525651) ^ (1357 + 1357 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1357 * (2 : ZMod 1457992525651) ^ 1357) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 920151713123 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1457992525651) ^ 5431 = 1085216045267 := by
        calc
          (2 : ZMod 1457992525651) ^ 5431 = (2 : ZMod 1457992525651) ^ (2715 + 2715 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2715 * (2 : ZMod 1457992525651) ^ 2715) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1085216045267 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1457992525651) ^ 10862 = 642570118255 := by
        calc
          (2 : ZMod 1457992525651) ^ 10862 = (2 : ZMod 1457992525651) ^ (5431 + 5431) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5431 * (2 : ZMod 1457992525651) ^ 5431 := by rw [pow_add]
          _ = 642570118255 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1457992525651) ^ 21725 = 656572918670 := by
        calc
          (2 : ZMod 1457992525651) ^ 21725 = (2 : ZMod 1457992525651) ^ (10862 + 10862 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 10862 * (2 : ZMod 1457992525651) ^ 10862) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 656572918670 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1457992525651) ^ 43451 = 465925041759 := by
        calc
          (2 : ZMod 1457992525651) ^ 43451 = (2 : ZMod 1457992525651) ^ (21725 + 21725 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 21725 * (2 : ZMod 1457992525651) ^ 21725) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 465925041759 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1457992525651) ^ 86903 = 476821136572 := by
        calc
          (2 : ZMod 1457992525651) ^ 86903 = (2 : ZMod 1457992525651) ^ (43451 + 43451 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 43451 * (2 : ZMod 1457992525651) ^ 43451) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 476821136572 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1457992525651) ^ 173806 = 1156913337968 := by
        calc
          (2 : ZMod 1457992525651) ^ 173806 = (2 : ZMod 1457992525651) ^ (86903 + 86903) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 86903 * (2 : ZMod 1457992525651) ^ 86903 := by rw [pow_add]
          _ = 1156913337968 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1457992525651) ^ 347612 = 1000129376494 := by
        calc
          (2 : ZMod 1457992525651) ^ 347612 = (2 : ZMod 1457992525651) ^ (173806 + 173806) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 173806 * (2 : ZMod 1457992525651) ^ 173806 := by rw [pow_add]
          _ = 1000129376494 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1457992525651) ^ 695225 = 1074492117950 := by
        calc
          (2 : ZMod 1457992525651) ^ 695225 = (2 : ZMod 1457992525651) ^ (347612 + 347612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 347612 * (2 : ZMod 1457992525651) ^ 347612) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1074492117950 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1457992525651) ^ 1390450 = 1330265393153 := by
        calc
          (2 : ZMod 1457992525651) ^ 1390450 = (2 : ZMod 1457992525651) ^ (695225 + 695225) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 695225 * (2 : ZMod 1457992525651) ^ 695225 := by rw [pow_add]
          _ = 1330265393153 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1457992525651) ^ 2780900 = 722476836131 := by
        calc
          (2 : ZMod 1457992525651) ^ 2780900 = (2 : ZMod 1457992525651) ^ (1390450 + 1390450) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1390450 * (2 : ZMod 1457992525651) ^ 1390450 := by rw [pow_add]
          _ = 722476836131 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1457992525651) ^ 5561800 = 529250212318 := by
        calc
          (2 : ZMod 1457992525651) ^ 5561800 = (2 : ZMod 1457992525651) ^ (2780900 + 2780900) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 2780900 * (2 : ZMod 1457992525651) ^ 2780900 := by rw [pow_add]
          _ = 529250212318 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1457992525651) ^ 11123600 = 223434150943 := by
        calc
          (2 : ZMod 1457992525651) ^ 11123600 = (2 : ZMod 1457992525651) ^ (5561800 + 5561800) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5561800 * (2 : ZMod 1457992525651) ^ 5561800 := by rw [pow_add]
          _ = 223434150943 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1457992525651) ^ 22247200 = 523872126314 := by
        calc
          (2 : ZMod 1457992525651) ^ 22247200 = (2 : ZMod 1457992525651) ^ (11123600 + 11123600) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 11123600 * (2 : ZMod 1457992525651) ^ 11123600 := by rw [pow_add]
          _ = 523872126314 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1457992525651) ^ 44494400 = 544887628372 := by
        calc
          (2 : ZMod 1457992525651) ^ 44494400 = (2 : ZMod 1457992525651) ^ (22247200 + 22247200) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 22247200 * (2 : ZMod 1457992525651) ^ 22247200 := by rw [pow_add]
          _ = 544887628372 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1457992525651) ^ 88988801 = 887972583897 := by
        calc
          (2 : ZMod 1457992525651) ^ 88988801 = (2 : ZMod 1457992525651) ^ (44494400 + 44494400 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 44494400 * (2 : ZMod 1457992525651) ^ 44494400) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 887972583897 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1457992525651) ^ 177977603 = 304555496337 := by
        calc
          (2 : ZMod 1457992525651) ^ 177977603 = (2 : ZMod 1457992525651) ^ (88988801 + 88988801 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 88988801 * (2 : ZMod 1457992525651) ^ 88988801) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 304555496337 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1457992525651) ^ 355955206 = 884830898204 := by
        calc
          (2 : ZMod 1457992525651) ^ 355955206 = (2 : ZMod 1457992525651) ^ (177977603 + 177977603) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 177977603 * (2 : ZMod 1457992525651) ^ 177977603 := by rw [pow_add]
          _ = 884830898204 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1457992525651) ^ 711910412 = 1151784370477 := by
        calc
          (2 : ZMod 1457992525651) ^ 711910412 = (2 : ZMod 1457992525651) ^ (355955206 + 355955206) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 355955206 * (2 : ZMod 1457992525651) ^ 355955206 := by rw [pow_add]
          _ = 1151784370477 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1457992525651) ^ 1423820825 = 1120556638007 := by
        calc
          (2 : ZMod 1457992525651) ^ 1423820825 = (2 : ZMod 1457992525651) ^ (711910412 + 711910412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 711910412 * (2 : ZMod 1457992525651) ^ 711910412) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1120556638007 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 1457992525651) ^ 2847641651 = 1186560540271 := by
        calc
          (2 : ZMod 1457992525651) ^ 2847641651 = (2 : ZMod 1457992525651) ^ (1423820825 + 1423820825 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1423820825 * (2 : ZMod 1457992525651) ^ 1423820825) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1186560540271 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 1457992525651) ^ 5695283303 = 1137434381571 := by
        calc
          (2 : ZMod 1457992525651) ^ 5695283303 = (2 : ZMod 1457992525651) ^ (2847641651 + 2847641651 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2847641651 * (2 : ZMod 1457992525651) ^ 2847641651) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1137434381571 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 1457992525651) ^ 11390566606 = 1089886903854 := by
        calc
          (2 : ZMod 1457992525651) ^ 11390566606 = (2 : ZMod 1457992525651) ^ (5695283303 + 5695283303) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5695283303 * (2 : ZMod 1457992525651) ^ 5695283303 := by rw [pow_add]
          _ = 1089886903854 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 1457992525651) ^ 22781133213 = 1437675525653 := by
        calc
          (2 : ZMod 1457992525651) ^ 22781133213 = (2 : ZMod 1457992525651) ^ (11390566606 + 11390566606 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 11390566606 * (2 : ZMod 1457992525651) ^ 11390566606) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1437675525653 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 1457992525651) ^ 45562266426 = 445840192713 := by
        calc
          (2 : ZMod 1457992525651) ^ 45562266426 = (2 : ZMod 1457992525651) ^ (22781133213 + 22781133213) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 22781133213 * (2 : ZMod 1457992525651) ^ 22781133213 := by rw [pow_add]
          _ = 445840192713 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 1457992525651) ^ 91124532853 = 825264299729 := by
        calc
          (2 : ZMod 1457992525651) ^ 91124532853 = (2 : ZMod 1457992525651) ^ (45562266426 + 45562266426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 45562266426 * (2 : ZMod 1457992525651) ^ 45562266426) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 825264299729 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 1457992525651) ^ 182249065706 = 672147471769 := by
        calc
          (2 : ZMod 1457992525651) ^ 182249065706 = (2 : ZMod 1457992525651) ^ (91124532853 + 91124532853) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 91124532853 * (2 : ZMod 1457992525651) ^ 91124532853 := by rw [pow_add]
          _ = 672147471769 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 1457992525651) ^ 364498131412 = 855994323170 := by
        calc
          (2 : ZMod 1457992525651) ^ 364498131412 = (2 : ZMod 1457992525651) ^ (182249065706 + 182249065706) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 182249065706 * (2 : ZMod 1457992525651) ^ 182249065706 := by rw [pow_add]
          _ = 855994323170 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 1457992525651) ^ 728996262825 = 1457992525650 := by
        calc
          (2 : ZMod 1457992525651) ^ 728996262825 = (2 : ZMod 1457992525651) ^ (364498131412 + 364498131412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 364498131412 * (2 : ZMod 1457992525651) ^ 364498131412) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1457992525650 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 1457992525651) ^ 1457992525650 = 1 := by
        calc
          (2 : ZMod 1457992525651) ^ 1457992525650 = (2 : ZMod 1457992525651) ^ (728996262825 + 728996262825) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 728996262825 * (2 : ZMod 1457992525651) ^ 728996262825 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (593, 1), (16391147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (593, 1), (16391147, 1)] : List FactorBlock).map factorBlockValue).prod = 1457992525651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1457992525651) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1457992525651) ^ 2 = 4 := by
        calc
          (2 : ZMod 1457992525651) ^ 2 = (2 : ZMod 1457992525651) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1 * (2 : ZMod 1457992525651) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1457992525651) ^ 5 = 32 := by
        calc
          (2 : ZMod 1457992525651) ^ 5 = (2 : ZMod 1457992525651) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2 * (2 : ZMod 1457992525651) ^ 2) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1457992525651) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1457992525651) ^ 10 = (2 : ZMod 1457992525651) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5 * (2 : ZMod 1457992525651) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1457992525651) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1457992525651) ^ 21 = (2 : ZMod 1457992525651) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 10 * (2 : ZMod 1457992525651) ^ 10) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1457992525651) ^ 42 = 24068934151 := by
        calc
          (2 : ZMod 1457992525651) ^ 42 = (2 : ZMod 1457992525651) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 21 * (2 : ZMod 1457992525651) ^ 21 := by rw [pow_add]
          _ = 24068934151 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1457992525651) ^ 84 = 858554029690 := by
        calc
          (2 : ZMod 1457992525651) ^ 84 = (2 : ZMod 1457992525651) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 42 * (2 : ZMod 1457992525651) ^ 42 := by rw [pow_add]
          _ = 858554029690 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1457992525651) ^ 169 = 62250263588 := by
        calc
          (2 : ZMod 1457992525651) ^ 169 = (2 : ZMod 1457992525651) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 84 * (2 : ZMod 1457992525651) ^ 84) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 62250263588 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1457992525651) ^ 339 = 451141312902 := by
        calc
          (2 : ZMod 1457992525651) ^ 339 = (2 : ZMod 1457992525651) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 169 * (2 : ZMod 1457992525651) ^ 169) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 451141312902 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1457992525651) ^ 678 = 925089733591 := by
        calc
          (2 : ZMod 1457992525651) ^ 678 = (2 : ZMod 1457992525651) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 339 * (2 : ZMod 1457992525651) ^ 339 := by rw [pow_add]
          _ = 925089733591 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1457992525651) ^ 1357 = 593403594650 := by
        calc
          (2 : ZMod 1457992525651) ^ 1357 = (2 : ZMod 1457992525651) ^ (678 + 678 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 678 * (2 : ZMod 1457992525651) ^ 678) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 593403594650 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1457992525651) ^ 2715 = 920151713123 := by
        calc
          (2 : ZMod 1457992525651) ^ 2715 = (2 : ZMod 1457992525651) ^ (1357 + 1357 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1357 * (2 : ZMod 1457992525651) ^ 1357) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 920151713123 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1457992525651) ^ 5431 = 1085216045267 := by
        calc
          (2 : ZMod 1457992525651) ^ 5431 = (2 : ZMod 1457992525651) ^ (2715 + 2715 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2715 * (2 : ZMod 1457992525651) ^ 2715) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1085216045267 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1457992525651) ^ 10862 = 642570118255 := by
        calc
          (2 : ZMod 1457992525651) ^ 10862 = (2 : ZMod 1457992525651) ^ (5431 + 5431) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5431 * (2 : ZMod 1457992525651) ^ 5431 := by rw [pow_add]
          _ = 642570118255 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1457992525651) ^ 21725 = 656572918670 := by
        calc
          (2 : ZMod 1457992525651) ^ 21725 = (2 : ZMod 1457992525651) ^ (10862 + 10862 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 10862 * (2 : ZMod 1457992525651) ^ 10862) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 656572918670 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1457992525651) ^ 43451 = 465925041759 := by
        calc
          (2 : ZMod 1457992525651) ^ 43451 = (2 : ZMod 1457992525651) ^ (21725 + 21725 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 21725 * (2 : ZMod 1457992525651) ^ 21725) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 465925041759 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1457992525651) ^ 86903 = 476821136572 := by
        calc
          (2 : ZMod 1457992525651) ^ 86903 = (2 : ZMod 1457992525651) ^ (43451 + 43451 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 43451 * (2 : ZMod 1457992525651) ^ 43451) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 476821136572 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1457992525651) ^ 173806 = 1156913337968 := by
        calc
          (2 : ZMod 1457992525651) ^ 173806 = (2 : ZMod 1457992525651) ^ (86903 + 86903) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 86903 * (2 : ZMod 1457992525651) ^ 86903 := by rw [pow_add]
          _ = 1156913337968 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1457992525651) ^ 347612 = 1000129376494 := by
        calc
          (2 : ZMod 1457992525651) ^ 347612 = (2 : ZMod 1457992525651) ^ (173806 + 173806) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 173806 * (2 : ZMod 1457992525651) ^ 173806 := by rw [pow_add]
          _ = 1000129376494 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1457992525651) ^ 695225 = 1074492117950 := by
        calc
          (2 : ZMod 1457992525651) ^ 695225 = (2 : ZMod 1457992525651) ^ (347612 + 347612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 347612 * (2 : ZMod 1457992525651) ^ 347612) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1074492117950 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1457992525651) ^ 1390450 = 1330265393153 := by
        calc
          (2 : ZMod 1457992525651) ^ 1390450 = (2 : ZMod 1457992525651) ^ (695225 + 695225) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 695225 * (2 : ZMod 1457992525651) ^ 695225 := by rw [pow_add]
          _ = 1330265393153 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1457992525651) ^ 2780900 = 722476836131 := by
        calc
          (2 : ZMod 1457992525651) ^ 2780900 = (2 : ZMod 1457992525651) ^ (1390450 + 1390450) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1390450 * (2 : ZMod 1457992525651) ^ 1390450 := by rw [pow_add]
          _ = 722476836131 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1457992525651) ^ 5561800 = 529250212318 := by
        calc
          (2 : ZMod 1457992525651) ^ 5561800 = (2 : ZMod 1457992525651) ^ (2780900 + 2780900) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 2780900 * (2 : ZMod 1457992525651) ^ 2780900 := by rw [pow_add]
          _ = 529250212318 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1457992525651) ^ 11123600 = 223434150943 := by
        calc
          (2 : ZMod 1457992525651) ^ 11123600 = (2 : ZMod 1457992525651) ^ (5561800 + 5561800) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5561800 * (2 : ZMod 1457992525651) ^ 5561800 := by rw [pow_add]
          _ = 223434150943 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1457992525651) ^ 22247200 = 523872126314 := by
        calc
          (2 : ZMod 1457992525651) ^ 22247200 = (2 : ZMod 1457992525651) ^ (11123600 + 11123600) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 11123600 * (2 : ZMod 1457992525651) ^ 11123600 := by rw [pow_add]
          _ = 523872126314 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1457992525651) ^ 44494400 = 544887628372 := by
        calc
          (2 : ZMod 1457992525651) ^ 44494400 = (2 : ZMod 1457992525651) ^ (22247200 + 22247200) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 22247200 * (2 : ZMod 1457992525651) ^ 22247200 := by rw [pow_add]
          _ = 544887628372 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1457992525651) ^ 88988801 = 887972583897 := by
        calc
          (2 : ZMod 1457992525651) ^ 88988801 = (2 : ZMod 1457992525651) ^ (44494400 + 44494400 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 44494400 * (2 : ZMod 1457992525651) ^ 44494400) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 887972583897 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1457992525651) ^ 177977603 = 304555496337 := by
        calc
          (2 : ZMod 1457992525651) ^ 177977603 = (2 : ZMod 1457992525651) ^ (88988801 + 88988801 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 88988801 * (2 : ZMod 1457992525651) ^ 88988801) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 304555496337 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1457992525651) ^ 355955206 = 884830898204 := by
        calc
          (2 : ZMod 1457992525651) ^ 355955206 = (2 : ZMod 1457992525651) ^ (177977603 + 177977603) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 177977603 * (2 : ZMod 1457992525651) ^ 177977603 := by rw [pow_add]
          _ = 884830898204 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1457992525651) ^ 711910412 = 1151784370477 := by
        calc
          (2 : ZMod 1457992525651) ^ 711910412 = (2 : ZMod 1457992525651) ^ (355955206 + 355955206) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 355955206 * (2 : ZMod 1457992525651) ^ 355955206 := by rw [pow_add]
          _ = 1151784370477 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 1457992525651) ^ 1423820825 = 1120556638007 := by
        calc
          (2 : ZMod 1457992525651) ^ 1423820825 = (2 : ZMod 1457992525651) ^ (711910412 + 711910412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 711910412 * (2 : ZMod 1457992525651) ^ 711910412) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1120556638007 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 1457992525651) ^ 2847641651 = 1186560540271 := by
        calc
          (2 : ZMod 1457992525651) ^ 2847641651 = (2 : ZMod 1457992525651) ^ (1423820825 + 1423820825 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1423820825 * (2 : ZMod 1457992525651) ^ 1423820825) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1186560540271 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 1457992525651) ^ 5695283303 = 1137434381571 := by
        calc
          (2 : ZMod 1457992525651) ^ 5695283303 = (2 : ZMod 1457992525651) ^ (2847641651 + 2847641651 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2847641651 * (2 : ZMod 1457992525651) ^ 2847641651) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1137434381571 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 1457992525651) ^ 11390566606 = 1089886903854 := by
        calc
          (2 : ZMod 1457992525651) ^ 11390566606 = (2 : ZMod 1457992525651) ^ (5695283303 + 5695283303) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5695283303 * (2 : ZMod 1457992525651) ^ 5695283303 := by rw [pow_add]
          _ = 1089886903854 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 1457992525651) ^ 22781133213 = 1437675525653 := by
        calc
          (2 : ZMod 1457992525651) ^ 22781133213 = (2 : ZMod 1457992525651) ^ (11390566606 + 11390566606 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 11390566606 * (2 : ZMod 1457992525651) ^ 11390566606) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1437675525653 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 1457992525651) ^ 45562266426 = 445840192713 := by
        calc
          (2 : ZMod 1457992525651) ^ 45562266426 = (2 : ZMod 1457992525651) ^ (22781133213 + 22781133213) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 22781133213 * (2 : ZMod 1457992525651) ^ 22781133213 := by rw [pow_add]
          _ = 445840192713 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 1457992525651) ^ 91124532853 = 825264299729 := by
        calc
          (2 : ZMod 1457992525651) ^ 91124532853 = (2 : ZMod 1457992525651) ^ (45562266426 + 45562266426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 45562266426 * (2 : ZMod 1457992525651) ^ 45562266426) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 825264299729 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 1457992525651) ^ 182249065706 = 672147471769 := by
        calc
          (2 : ZMod 1457992525651) ^ 182249065706 = (2 : ZMod 1457992525651) ^ (91124532853 + 91124532853) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 91124532853 * (2 : ZMod 1457992525651) ^ 91124532853 := by rw [pow_add]
          _ = 672147471769 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 1457992525651) ^ 364498131412 = 855994323170 := by
        calc
          (2 : ZMod 1457992525651) ^ 364498131412 = (2 : ZMod 1457992525651) ^ (182249065706 + 182249065706) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 182249065706 * (2 : ZMod 1457992525651) ^ 182249065706 := by rw [pow_add]
          _ = 855994323170 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 1457992525651) ^ 728996262825 = 1457992525650 := by
        calc
          (2 : ZMod 1457992525651) ^ 728996262825 = (2 : ZMod 1457992525651) ^ (364498131412 + 364498131412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 364498131412 * (2 : ZMod 1457992525651) ^ 364498131412) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1457992525650 := by rw [factor_0_38]; decide
      change (2 : ZMod 1457992525651) ^ 728996262825 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1457992525651) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1457992525651) ^ 3 = 8 := by
        calc
          (2 : ZMod 1457992525651) ^ 3 = (2 : ZMod 1457992525651) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1 * (2 : ZMod 1457992525651) ^ 1) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1457992525651) ^ 7 = 128 := by
        calc
          (2 : ZMod 1457992525651) ^ 7 = (2 : ZMod 1457992525651) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 3 * (2 : ZMod 1457992525651) ^ 3) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1457992525651) ^ 14 = 16384 := by
        calc
          (2 : ZMod 1457992525651) ^ 14 = (2 : ZMod 1457992525651) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 7 * (2 : ZMod 1457992525651) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1457992525651) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 1457992525651) ^ 28 = (2 : ZMod 1457992525651) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 14 * (2 : ZMod 1457992525651) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1457992525651) ^ 56 = 687435204214 := by
        calc
          (2 : ZMod 1457992525651) ^ 56 = (2 : ZMod 1457992525651) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 28 * (2 : ZMod 1457992525651) ^ 28 := by rw [pow_add]
          _ = 687435204214 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1457992525651) ^ 113 = 212646730072 := by
        calc
          (2 : ZMod 1457992525651) ^ 113 = (2 : ZMod 1457992525651) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 56 * (2 : ZMod 1457992525651) ^ 56) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 212646730072 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1457992525651) ^ 226 = 757124625330 := by
        calc
          (2 : ZMod 1457992525651) ^ 226 = (2 : ZMod 1457992525651) ^ (113 + 113) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 113 * (2 : ZMod 1457992525651) ^ 113 := by rw [pow_add]
          _ = 757124625330 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1457992525651) ^ 452 = 629387321995 := by
        calc
          (2 : ZMod 1457992525651) ^ 452 = (2 : ZMod 1457992525651) ^ (226 + 226) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 226 * (2 : ZMod 1457992525651) ^ 226 := by rw [pow_add]
          _ = 629387321995 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1457992525651) ^ 905 = 1198921472878 := by
        calc
          (2 : ZMod 1457992525651) ^ 905 = (2 : ZMod 1457992525651) ^ (452 + 452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 452 * (2 : ZMod 1457992525651) ^ 452) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1198921472878 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1457992525651) ^ 1810 = 1284367094586 := by
        calc
          (2 : ZMod 1457992525651) ^ 1810 = (2 : ZMod 1457992525651) ^ (905 + 905) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 905 * (2 : ZMod 1457992525651) ^ 905 := by rw [pow_add]
          _ = 1284367094586 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1457992525651) ^ 3620 = 469849678487 := by
        calc
          (2 : ZMod 1457992525651) ^ 3620 = (2 : ZMod 1457992525651) ^ (1810 + 1810) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1810 * (2 : ZMod 1457992525651) ^ 1810 := by rw [pow_add]
          _ = 469849678487 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1457992525651) ^ 7241 = 573328528686 := by
        calc
          (2 : ZMod 1457992525651) ^ 7241 = (2 : ZMod 1457992525651) ^ (3620 + 3620 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 3620 * (2 : ZMod 1457992525651) ^ 3620) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 573328528686 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1457992525651) ^ 14483 = 390324238817 := by
        calc
          (2 : ZMod 1457992525651) ^ 14483 = (2 : ZMod 1457992525651) ^ (7241 + 7241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 7241 * (2 : ZMod 1457992525651) ^ 7241) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 390324238817 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1457992525651) ^ 28967 = 337660824341 := by
        calc
          (2 : ZMod 1457992525651) ^ 28967 = (2 : ZMod 1457992525651) ^ (14483 + 14483 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 14483 * (2 : ZMod 1457992525651) ^ 14483) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 337660824341 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1457992525651) ^ 57935 = 152462777882 := by
        calc
          (2 : ZMod 1457992525651) ^ 57935 = (2 : ZMod 1457992525651) ^ (28967 + 28967 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 28967 * (2 : ZMod 1457992525651) ^ 28967) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 152462777882 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1457992525651) ^ 115870 = 522844802561 := by
        calc
          (2 : ZMod 1457992525651) ^ 115870 = (2 : ZMod 1457992525651) ^ (57935 + 57935) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 57935 * (2 : ZMod 1457992525651) ^ 57935 := by rw [pow_add]
          _ = 522844802561 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1457992525651) ^ 231741 = 277187170743 := by
        calc
          (2 : ZMod 1457992525651) ^ 231741 = (2 : ZMod 1457992525651) ^ (115870 + 115870 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 115870 * (2 : ZMod 1457992525651) ^ 115870) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 277187170743 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1457992525651) ^ 463483 = 1080074130047 := by
        calc
          (2 : ZMod 1457992525651) ^ 463483 = (2 : ZMod 1457992525651) ^ (231741 + 231741 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 231741 * (2 : ZMod 1457992525651) ^ 231741) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1080074130047 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1457992525651) ^ 926966 = 951976327013 := by
        calc
          (2 : ZMod 1457992525651) ^ 926966 = (2 : ZMod 1457992525651) ^ (463483 + 463483) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 463483 * (2 : ZMod 1457992525651) ^ 463483 := by rw [pow_add]
          _ = 951976327013 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1457992525651) ^ 1853933 = 917531047910 := by
        calc
          (2 : ZMod 1457992525651) ^ 1853933 = (2 : ZMod 1457992525651) ^ (926966 + 926966 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 926966 * (2 : ZMod 1457992525651) ^ 926966) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 917531047910 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1457992525651) ^ 3707866 = 458483096507 := by
        calc
          (2 : ZMod 1457992525651) ^ 3707866 = (2 : ZMod 1457992525651) ^ (1853933 + 1853933) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1853933 * (2 : ZMod 1457992525651) ^ 1853933 := by rw [pow_add]
          _ = 458483096507 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1457992525651) ^ 7415733 = 929600831180 := by
        calc
          (2 : ZMod 1457992525651) ^ 7415733 = (2 : ZMod 1457992525651) ^ (3707866 + 3707866 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 3707866 * (2 : ZMod 1457992525651) ^ 3707866) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 929600831180 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1457992525651) ^ 14831466 = 684079272726 := by
        calc
          (2 : ZMod 1457992525651) ^ 14831466 = (2 : ZMod 1457992525651) ^ (7415733 + 7415733) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 7415733 * (2 : ZMod 1457992525651) ^ 7415733 := by rw [pow_add]
          _ = 684079272726 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1457992525651) ^ 29662933 = 429264066044 := by
        calc
          (2 : ZMod 1457992525651) ^ 29662933 = (2 : ZMod 1457992525651) ^ (14831466 + 14831466 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 14831466 * (2 : ZMod 1457992525651) ^ 14831466) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 429264066044 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1457992525651) ^ 59325867 = 455408134861 := by
        calc
          (2 : ZMod 1457992525651) ^ 59325867 = (2 : ZMod 1457992525651) ^ (29662933 + 29662933 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 29662933 * (2 : ZMod 1457992525651) ^ 29662933) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 455408134861 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1457992525651) ^ 118651735 = 1261981635451 := by
        calc
          (2 : ZMod 1457992525651) ^ 118651735 = (2 : ZMod 1457992525651) ^ (59325867 + 59325867 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 59325867 * (2 : ZMod 1457992525651) ^ 59325867) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1261981635451 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1457992525651) ^ 237303470 = 320663350078 := by
        calc
          (2 : ZMod 1457992525651) ^ 237303470 = (2 : ZMod 1457992525651) ^ (118651735 + 118651735) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 118651735 * (2 : ZMod 1457992525651) ^ 118651735 := by rw [pow_add]
          _ = 320663350078 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 1457992525651) ^ 474606941 = 160013874651 := by
        calc
          (2 : ZMod 1457992525651) ^ 474606941 = (2 : ZMod 1457992525651) ^ (237303470 + 237303470 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 237303470 * (2 : ZMod 1457992525651) ^ 237303470) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 160013874651 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 1457992525651) ^ 949213883 = 991023667822 := by
        calc
          (2 : ZMod 1457992525651) ^ 949213883 = (2 : ZMod 1457992525651) ^ (474606941 + 474606941 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 474606941 * (2 : ZMod 1457992525651) ^ 474606941) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 991023667822 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 1457992525651) ^ 1898427767 = 852456037816 := by
        calc
          (2 : ZMod 1457992525651) ^ 1898427767 = (2 : ZMod 1457992525651) ^ (949213883 + 949213883 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 949213883 * (2 : ZMod 1457992525651) ^ 949213883) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 852456037816 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 1457992525651) ^ 3796855535 = 230344284214 := by
        calc
          (2 : ZMod 1457992525651) ^ 3796855535 = (2 : ZMod 1457992525651) ^ (1898427767 + 1898427767 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1898427767 * (2 : ZMod 1457992525651) ^ 1898427767) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 230344284214 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 1457992525651) ^ 7593711071 = 1160442705869 := by
        calc
          (2 : ZMod 1457992525651) ^ 7593711071 = (2 : ZMod 1457992525651) ^ (3796855535 + 3796855535 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 3796855535 * (2 : ZMod 1457992525651) ^ 3796855535) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1160442705869 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 1457992525651) ^ 15187422142 = 814724168432 := by
        calc
          (2 : ZMod 1457992525651) ^ 15187422142 = (2 : ZMod 1457992525651) ^ (7593711071 + 7593711071) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 7593711071 * (2 : ZMod 1457992525651) ^ 7593711071 := by rw [pow_add]
          _ = 814724168432 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 1457992525651) ^ 30374844284 = 851168968631 := by
        calc
          (2 : ZMod 1457992525651) ^ 30374844284 = (2 : ZMod 1457992525651) ^ (15187422142 + 15187422142) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 15187422142 * (2 : ZMod 1457992525651) ^ 15187422142 := by rw [pow_add]
          _ = 851168968631 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 1457992525651) ^ 60749688568 = 993851857998 := by
        calc
          (2 : ZMod 1457992525651) ^ 60749688568 = (2 : ZMod 1457992525651) ^ (30374844284 + 30374844284) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 30374844284 * (2 : ZMod 1457992525651) ^ 30374844284 := by rw [pow_add]
          _ = 993851857998 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 1457992525651) ^ 121499377137 = 844601948164 := by
        calc
          (2 : ZMod 1457992525651) ^ 121499377137 = (2 : ZMod 1457992525651) ^ (60749688568 + 60749688568 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 60749688568 * (2 : ZMod 1457992525651) ^ 60749688568) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 844601948164 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 1457992525651) ^ 242998754275 = 1174178737700 := by
        calc
          (2 : ZMod 1457992525651) ^ 242998754275 = (2 : ZMod 1457992525651) ^ (121499377137 + 121499377137 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 121499377137 * (2 : ZMod 1457992525651) ^ 121499377137) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1174178737700 := by rw [factor_1_36]; decide
      have factor_1_38 : (2 : ZMod 1457992525651) ^ 485997508550 = 1174178737699 := by
        calc
          (2 : ZMod 1457992525651) ^ 485997508550 = (2 : ZMod 1457992525651) ^ (242998754275 + 242998754275) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 242998754275 * (2 : ZMod 1457992525651) ^ 242998754275 := by rw [pow_add]
          _ = 1174178737699 := by rw [factor_1_37]; decide
      change (2 : ZMod 1457992525651) ^ 485997508550 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1457992525651) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1457992525651) ^ 2 = 4 := by
        calc
          (2 : ZMod 1457992525651) ^ 2 = (2 : ZMod 1457992525651) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1 * (2 : ZMod 1457992525651) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1457992525651) ^ 4 = 16 := by
        calc
          (2 : ZMod 1457992525651) ^ 4 = (2 : ZMod 1457992525651) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 2 * (2 : ZMod 1457992525651) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1457992525651) ^ 8 = 256 := by
        calc
          (2 : ZMod 1457992525651) ^ 8 = (2 : ZMod 1457992525651) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 4 * (2 : ZMod 1457992525651) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1457992525651) ^ 16 = 65536 := by
        calc
          (2 : ZMod 1457992525651) ^ 16 = (2 : ZMod 1457992525651) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 8 * (2 : ZMod 1457992525651) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1457992525651) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 1457992525651) ^ 33 = (2 : ZMod 1457992525651) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 16 * (2 : ZMod 1457992525651) ^ 16) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1457992525651) ^ 67 = 904510977057 := by
        calc
          (2 : ZMod 1457992525651) ^ 67 = (2 : ZMod 1457992525651) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 33 * (2 : ZMod 1457992525651) ^ 33) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 904510977057 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1457992525651) ^ 135 = 1430841321054 := by
        calc
          (2 : ZMod 1457992525651) ^ 135 = (2 : ZMod 1457992525651) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 67 * (2 : ZMod 1457992525651) ^ 67) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1430841321054 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1457992525651) ^ 271 = 685715502032 := by
        calc
          (2 : ZMod 1457992525651) ^ 271 = (2 : ZMod 1457992525651) ^ (135 + 135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 135 * (2 : ZMod 1457992525651) ^ 135) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 685715502032 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1457992525651) ^ 543 = 1295947493491 := by
        calc
          (2 : ZMod 1457992525651) ^ 543 = (2 : ZMod 1457992525651) ^ (271 + 271 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 271 * (2 : ZMod 1457992525651) ^ 271) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1295947493491 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1457992525651) ^ 1086 = 344824477485 := by
        calc
          (2 : ZMod 1457992525651) ^ 1086 = (2 : ZMod 1457992525651) ^ (543 + 543) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 543 * (2 : ZMod 1457992525651) ^ 543 := by rw [pow_add]
          _ = 344824477485 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1457992525651) ^ 2172 = 270763046859 := by
        calc
          (2 : ZMod 1457992525651) ^ 2172 = (2 : ZMod 1457992525651) ^ (1086 + 1086) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1086 * (2 : ZMod 1457992525651) ^ 1086 := by rw [pow_add]
          _ = 270763046859 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1457992525651) ^ 4345 = 945845140085 := by
        calc
          (2 : ZMod 1457992525651) ^ 4345 = (2 : ZMod 1457992525651) ^ (2172 + 2172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2172 * (2 : ZMod 1457992525651) ^ 2172) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 945845140085 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1457992525651) ^ 8690 = 1030256988993 := by
        calc
          (2 : ZMod 1457992525651) ^ 8690 = (2 : ZMod 1457992525651) ^ (4345 + 4345) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 4345 * (2 : ZMod 1457992525651) ^ 4345 := by rw [pow_add]
          _ = 1030256988993 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1457992525651) ^ 17380 = 23070335346 := by
        calc
          (2 : ZMod 1457992525651) ^ 17380 = (2 : ZMod 1457992525651) ^ (8690 + 8690) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 8690 * (2 : ZMod 1457992525651) ^ 8690 := by rw [pow_add]
          _ = 23070335346 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1457992525651) ^ 34761 = 570061699756 := by
        calc
          (2 : ZMod 1457992525651) ^ 34761 = (2 : ZMod 1457992525651) ^ (17380 + 17380 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 17380 * (2 : ZMod 1457992525651) ^ 17380) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 570061699756 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1457992525651) ^ 69522 = 1295997529469 := by
        calc
          (2 : ZMod 1457992525651) ^ 69522 = (2 : ZMod 1457992525651) ^ (34761 + 34761) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 34761 * (2 : ZMod 1457992525651) ^ 34761 := by rw [pow_add]
          _ = 1295997529469 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1457992525651) ^ 139045 = 885620367192 := by
        calc
          (2 : ZMod 1457992525651) ^ 139045 = (2 : ZMod 1457992525651) ^ (69522 + 69522 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 69522 * (2 : ZMod 1457992525651) ^ 69522) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 885620367192 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1457992525651) ^ 278090 = 706622050558 := by
        calc
          (2 : ZMod 1457992525651) ^ 278090 = (2 : ZMod 1457992525651) ^ (139045 + 139045) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 139045 * (2 : ZMod 1457992525651) ^ 139045 := by rw [pow_add]
          _ = 706622050558 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1457992525651) ^ 556180 = 666038222422 := by
        calc
          (2 : ZMod 1457992525651) ^ 556180 = (2 : ZMod 1457992525651) ^ (278090 + 278090) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 278090 * (2 : ZMod 1457992525651) ^ 278090 := by rw [pow_add]
          _ = 666038222422 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1457992525651) ^ 1112360 = 1238349964797 := by
        calc
          (2 : ZMod 1457992525651) ^ 1112360 = (2 : ZMod 1457992525651) ^ (556180 + 556180) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 556180 * (2 : ZMod 1457992525651) ^ 556180 := by rw [pow_add]
          _ = 1238349964797 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1457992525651) ^ 2224720 = 1260948366492 := by
        calc
          (2 : ZMod 1457992525651) ^ 2224720 = (2 : ZMod 1457992525651) ^ (1112360 + 1112360) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1112360 * (2 : ZMod 1457992525651) ^ 1112360 := by rw [pow_add]
          _ = 1260948366492 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1457992525651) ^ 4449440 = 171245755784 := by
        calc
          (2 : ZMod 1457992525651) ^ 4449440 = (2 : ZMod 1457992525651) ^ (2224720 + 2224720) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 2224720 * (2 : ZMod 1457992525651) ^ 2224720 := by rw [pow_add]
          _ = 171245755784 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1457992525651) ^ 8898880 = 998720703599 := by
        calc
          (2 : ZMod 1457992525651) ^ 8898880 = (2 : ZMod 1457992525651) ^ (4449440 + 4449440) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 4449440 * (2 : ZMod 1457992525651) ^ 4449440 := by rw [pow_add]
          _ = 998720703599 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1457992525651) ^ 17797760 = 4634670607 := by
        calc
          (2 : ZMod 1457992525651) ^ 17797760 = (2 : ZMod 1457992525651) ^ (8898880 + 8898880) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 8898880 * (2 : ZMod 1457992525651) ^ 8898880 := by rw [pow_add]
          _ = 4634670607 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1457992525651) ^ 35595520 = 778753683796 := by
        calc
          (2 : ZMod 1457992525651) ^ 35595520 = (2 : ZMod 1457992525651) ^ (17797760 + 17797760) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 17797760 * (2 : ZMod 1457992525651) ^ 17797760 := by rw [pow_add]
          _ = 778753683796 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1457992525651) ^ 71191041 = 826425223142 := by
        calc
          (2 : ZMod 1457992525651) ^ 71191041 = (2 : ZMod 1457992525651) ^ (35595520 + 35595520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 35595520 * (2 : ZMod 1457992525651) ^ 35595520) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 826425223142 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 1457992525651) ^ 142382082 = 1361594196762 := by
        calc
          (2 : ZMod 1457992525651) ^ 142382082 = (2 : ZMod 1457992525651) ^ (71191041 + 71191041) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 71191041 * (2 : ZMod 1457992525651) ^ 71191041 := by rw [pow_add]
          _ = 1361594196762 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 1457992525651) ^ 284764165 = 247800824521 := by
        calc
          (2 : ZMod 1457992525651) ^ 284764165 = (2 : ZMod 1457992525651) ^ (142382082 + 142382082 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 142382082 * (2 : ZMod 1457992525651) ^ 142382082) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 247800824521 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 1457992525651) ^ 569528330 = 792095836546 := by
        calc
          (2 : ZMod 1457992525651) ^ 569528330 = (2 : ZMod 1457992525651) ^ (284764165 + 284764165) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 284764165 * (2 : ZMod 1457992525651) ^ 284764165 := by rw [pow_add]
          _ = 792095836546 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 1457992525651) ^ 1139056660 = 1021511242675 := by
        calc
          (2 : ZMod 1457992525651) ^ 1139056660 = (2 : ZMod 1457992525651) ^ (569528330 + 569528330) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 569528330 * (2 : ZMod 1457992525651) ^ 569528330 := by rw [pow_add]
          _ = 1021511242675 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 1457992525651) ^ 2278113321 = 977090142381 := by
        calc
          (2 : ZMod 1457992525651) ^ 2278113321 = (2 : ZMod 1457992525651) ^ (1139056660 + 1139056660 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1139056660 * (2 : ZMod 1457992525651) ^ 1139056660) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 977090142381 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 1457992525651) ^ 4556226642 = 964888522060 := by
        calc
          (2 : ZMod 1457992525651) ^ 4556226642 = (2 : ZMod 1457992525651) ^ (2278113321 + 2278113321) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 2278113321 * (2 : ZMod 1457992525651) ^ 2278113321 := by rw [pow_add]
          _ = 964888522060 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 1457992525651) ^ 9112453285 = 786386367060 := by
        calc
          (2 : ZMod 1457992525651) ^ 9112453285 = (2 : ZMod 1457992525651) ^ (4556226642 + 4556226642 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 4556226642 * (2 : ZMod 1457992525651) ^ 4556226642) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 786386367060 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 1457992525651) ^ 18224906570 = 894800602007 := by
        calc
          (2 : ZMod 1457992525651) ^ 18224906570 = (2 : ZMod 1457992525651) ^ (9112453285 + 9112453285) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 9112453285 * (2 : ZMod 1457992525651) ^ 9112453285 := by rw [pow_add]
          _ = 894800602007 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 1457992525651) ^ 36449813141 = 1325079633005 := by
        calc
          (2 : ZMod 1457992525651) ^ 36449813141 = (2 : ZMod 1457992525651) ^ (18224906570 + 18224906570 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 18224906570 * (2 : ZMod 1457992525651) ^ 18224906570) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1325079633005 := by rw [factor_2_34]; decide
      have factor_2_36 : (2 : ZMod 1457992525651) ^ 72899626282 = 1394672411198 := by
        calc
          (2 : ZMod 1457992525651) ^ 72899626282 = (2 : ZMod 1457992525651) ^ (36449813141 + 36449813141) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 36449813141 * (2 : ZMod 1457992525651) ^ 36449813141 := by rw [pow_add]
          _ = 1394672411198 := by rw [factor_2_35]; decide
      have factor_2_37 : (2 : ZMod 1457992525651) ^ 145799252565 = 625261227288 := by
        calc
          (2 : ZMod 1457992525651) ^ 145799252565 = (2 : ZMod 1457992525651) ^ (72899626282 + 72899626282 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 72899626282 * (2 : ZMod 1457992525651) ^ 72899626282) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 625261227288 := by rw [factor_2_36]; decide
      have factor_2_38 : (2 : ZMod 1457992525651) ^ 291598505130 = 993316954629 := by
        calc
          (2 : ZMod 1457992525651) ^ 291598505130 = (2 : ZMod 1457992525651) ^ (145799252565 + 145799252565) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 145799252565 * (2 : ZMod 1457992525651) ^ 145799252565 := by rw [pow_add]
          _ = 993316954629 := by rw [factor_2_37]; decide
      change (2 : ZMod 1457992525651) ^ 291598505130 ≠ 1
      rw [factor_2_38]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1457992525651) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1457992525651) ^ 2 = 4 := by
        calc
          (2 : ZMod 1457992525651) ^ 2 = (2 : ZMod 1457992525651) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1 * (2 : ZMod 1457992525651) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1457992525651) ^ 4 = 16 := by
        calc
          (2 : ZMod 1457992525651) ^ 4 = (2 : ZMod 1457992525651) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 2 * (2 : ZMod 1457992525651) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1457992525651) ^ 9 = 512 := by
        calc
          (2 : ZMod 1457992525651) ^ 9 = (2 : ZMod 1457992525651) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 4 * (2 : ZMod 1457992525651) ^ 4) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1457992525651) ^ 18 = 262144 := by
        calc
          (2 : ZMod 1457992525651) ^ 18 = (2 : ZMod 1457992525651) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 9 * (2 : ZMod 1457992525651) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1457992525651) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 1457992525651) ^ 36 = (2 : ZMod 1457992525651) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 18 * (2 : ZMod 1457992525651) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1457992525651) ^ 73 = 1026994031259 := by
        calc
          (2 : ZMod 1457992525651) ^ 73 = (2 : ZMod 1457992525651) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 36 * (2 : ZMod 1457992525651) ^ 36) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1026994031259 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1457992525651) ^ 146 = 1256041485733 := by
        calc
          (2 : ZMod 1457992525651) ^ 146 = (2 : ZMod 1457992525651) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 73 * (2 : ZMod 1457992525651) ^ 73 := by rw [pow_add]
          _ = 1256041485733 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1457992525651) ^ 293 = 523257060135 := by
        calc
          (2 : ZMod 1457992525651) ^ 293 = (2 : ZMod 1457992525651) ^ (146 + 146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 146 * (2 : ZMod 1457992525651) ^ 146) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 523257060135 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1457992525651) ^ 586 = 958730142940 := by
        calc
          (2 : ZMod 1457992525651) ^ 586 = (2 : ZMod 1457992525651) ^ (293 + 293) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 293 * (2 : ZMod 1457992525651) ^ 293 := by rw [pow_add]
          _ = 958730142940 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 1457992525651) ^ 1172 = 727301179060 := by
        calc
          (2 : ZMod 1457992525651) ^ 1172 = (2 : ZMod 1457992525651) ^ (586 + 586) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 586 * (2 : ZMod 1457992525651) ^ 586 := by rw [pow_add]
          _ = 727301179060 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 1457992525651) ^ 2344 = 1184476120824 := by
        calc
          (2 : ZMod 1457992525651) ^ 2344 = (2 : ZMod 1457992525651) ^ (1172 + 1172) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1172 * (2 : ZMod 1457992525651) ^ 1172 := by rw [pow_add]
          _ = 1184476120824 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 1457992525651) ^ 4689 = 522833804973 := by
        calc
          (2 : ZMod 1457992525651) ^ 4689 = (2 : ZMod 1457992525651) ^ (2344 + 2344 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2344 * (2 : ZMod 1457992525651) ^ 2344) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 522833804973 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 1457992525651) ^ 9379 = 1302909888846 := by
        calc
          (2 : ZMod 1457992525651) ^ 9379 = (2 : ZMod 1457992525651) ^ (4689 + 4689 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 4689 * (2 : ZMod 1457992525651) ^ 4689) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1302909888846 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 1457992525651) ^ 18758 = 1343139522962 := by
        calc
          (2 : ZMod 1457992525651) ^ 18758 = (2 : ZMod 1457992525651) ^ (9379 + 9379) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 9379 * (2 : ZMod 1457992525651) ^ 9379 := by rw [pow_add]
          _ = 1343139522962 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 1457992525651) ^ 37516 = 827411535077 := by
        calc
          (2 : ZMod 1457992525651) ^ 37516 = (2 : ZMod 1457992525651) ^ (18758 + 18758) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 18758 * (2 : ZMod 1457992525651) ^ 18758 := by rw [pow_add]
          _ = 827411535077 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 1457992525651) ^ 75032 = 902451551506 := by
        calc
          (2 : ZMod 1457992525651) ^ 75032 = (2 : ZMod 1457992525651) ^ (37516 + 37516) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 37516 * (2 : ZMod 1457992525651) ^ 37516 := by rw [pow_add]
          _ = 902451551506 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 1457992525651) ^ 150065 = 167919256355 := by
        calc
          (2 : ZMod 1457992525651) ^ 150065 = (2 : ZMod 1457992525651) ^ (75032 + 75032 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 75032 * (2 : ZMod 1457992525651) ^ 75032) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 167919256355 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 1457992525651) ^ 300130 = 1215531999909 := by
        calc
          (2 : ZMod 1457992525651) ^ 300130 = (2 : ZMod 1457992525651) ^ (150065 + 150065) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 150065 * (2 : ZMod 1457992525651) ^ 150065 := by rw [pow_add]
          _ = 1215531999909 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 1457992525651) ^ 600261 = 326999161310 := by
        calc
          (2 : ZMod 1457992525651) ^ 600261 = (2 : ZMod 1457992525651) ^ (300130 + 300130 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 300130 * (2 : ZMod 1457992525651) ^ 300130) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 326999161310 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 1457992525651) ^ 1200523 = 1056583047018 := by
        calc
          (2 : ZMod 1457992525651) ^ 1200523 = (2 : ZMod 1457992525651) ^ (600261 + 600261 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 600261 * (2 : ZMod 1457992525651) ^ 600261) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1056583047018 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 1457992525651) ^ 2401046 = 696435486693 := by
        calc
          (2 : ZMod 1457992525651) ^ 2401046 = (2 : ZMod 1457992525651) ^ (1200523 + 1200523) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1200523 * (2 : ZMod 1457992525651) ^ 1200523 := by rw [pow_add]
          _ = 696435486693 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 1457992525651) ^ 4802093 = 1381372437563 := by
        calc
          (2 : ZMod 1457992525651) ^ 4802093 = (2 : ZMod 1457992525651) ^ (2401046 + 2401046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2401046 * (2 : ZMod 1457992525651) ^ 2401046) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1381372437563 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 1457992525651) ^ 9604187 = 148035413572 := by
        calc
          (2 : ZMod 1457992525651) ^ 9604187 = (2 : ZMod 1457992525651) ^ (4802093 + 4802093 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 4802093 * (2 : ZMod 1457992525651) ^ 4802093) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 148035413572 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 1457992525651) ^ 19208375 = 317723373336 := by
        calc
          (2 : ZMod 1457992525651) ^ 19208375 = (2 : ZMod 1457992525651) ^ (9604187 + 9604187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 9604187 * (2 : ZMod 1457992525651) ^ 9604187) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 317723373336 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 1457992525651) ^ 38416750 = 991086677149 := by
        calc
          (2 : ZMod 1457992525651) ^ 38416750 = (2 : ZMod 1457992525651) ^ (19208375 + 19208375) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 19208375 * (2 : ZMod 1457992525651) ^ 19208375 := by rw [pow_add]
          _ = 991086677149 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 1457992525651) ^ 76833501 = 58592360875 := by
        calc
          (2 : ZMod 1457992525651) ^ 76833501 = (2 : ZMod 1457992525651) ^ (38416750 + 38416750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 38416750 * (2 : ZMod 1457992525651) ^ 38416750) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 58592360875 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 1457992525651) ^ 153667003 = 587398912912 := by
        calc
          (2 : ZMod 1457992525651) ^ 153667003 = (2 : ZMod 1457992525651) ^ (76833501 + 76833501 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 76833501 * (2 : ZMod 1457992525651) ^ 76833501) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 587398912912 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 1457992525651) ^ 307334006 = 311851547677 := by
        calc
          (2 : ZMod 1457992525651) ^ 307334006 = (2 : ZMod 1457992525651) ^ (153667003 + 153667003) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 153667003 * (2 : ZMod 1457992525651) ^ 153667003 := by rw [pow_add]
          _ = 311851547677 := by rw [factor_3_27]; decide
      have factor_3_29 : (2 : ZMod 1457992525651) ^ 614668012 = 801746537121 := by
        calc
          (2 : ZMod 1457992525651) ^ 614668012 = (2 : ZMod 1457992525651) ^ (307334006 + 307334006) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 307334006 * (2 : ZMod 1457992525651) ^ 307334006 := by rw [pow_add]
          _ = 801746537121 := by rw [factor_3_28]; decide
      have factor_3_30 : (2 : ZMod 1457992525651) ^ 1229336025 = 879779118787 := by
        calc
          (2 : ZMod 1457992525651) ^ 1229336025 = (2 : ZMod 1457992525651) ^ (614668012 + 614668012 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 614668012 * (2 : ZMod 1457992525651) ^ 614668012) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 879779118787 := by rw [factor_3_29]; decide
      have factor_3_31 : (2 : ZMod 1457992525651) ^ 2458672050 = 889385099771 := by
        calc
          (2 : ZMod 1457992525651) ^ 2458672050 = (2 : ZMod 1457992525651) ^ (1229336025 + 1229336025) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1229336025 * (2 : ZMod 1457992525651) ^ 1229336025 := by rw [pow_add]
          _ = 889385099771 := by rw [factor_3_30]; decide
      change (2 : ZMod 1457992525651) ^ 2458672050 ≠ 1
      rw [factor_3_31]
      decide
    ·
      have factor_4_0 : (2 : ZMod 1457992525651) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 1457992525651) ^ 2 = 4 := by
        calc
          (2 : ZMod 1457992525651) ^ 2 = (2 : ZMod 1457992525651) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 1 * (2 : ZMod 1457992525651) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 1457992525651) ^ 5 = 32 := by
        calc
          (2 : ZMod 1457992525651) ^ 5 = (2 : ZMod 1457992525651) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2 * (2 : ZMod 1457992525651) ^ 2) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 1457992525651) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1457992525651) ^ 10 = (2 : ZMod 1457992525651) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5 * (2 : ZMod 1457992525651) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 1457992525651) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1457992525651) ^ 21 = (2 : ZMod 1457992525651) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 10 * (2 : ZMod 1457992525651) ^ 10) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 1457992525651) ^ 43 = 48137868302 := by
        calc
          (2 : ZMod 1457992525651) ^ 43 = (2 : ZMod 1457992525651) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 21 * (2 : ZMod 1457992525651) ^ 21) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 48137868302 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 1457992525651) ^ 86 = 518231067458 := by
        calc
          (2 : ZMod 1457992525651) ^ 86 = (2 : ZMod 1457992525651) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 43 * (2 : ZMod 1457992525651) ^ 43 := by rw [pow_add]
          _ = 518231067458 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 1457992525651) ^ 173 = 996004217408 := by
        calc
          (2 : ZMod 1457992525651) ^ 173 = (2 : ZMod 1457992525651) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 86 * (2 : ZMod 1457992525651) ^ 86) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 996004217408 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 1457992525651) ^ 347 = 310766576483 := by
        calc
          (2 : ZMod 1457992525651) ^ 347 = (2 : ZMod 1457992525651) ^ (173 + 173 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 173 * (2 : ZMod 1457992525651) ^ 173) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 310766576483 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 1457992525651) ^ 694 = 435578999894 := by
        calc
          (2 : ZMod 1457992525651) ^ 694 = (2 : ZMod 1457992525651) ^ (347 + 347) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 347 * (2 : ZMod 1457992525651) ^ 347 := by rw [pow_add]
          _ = 435578999894 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 1457992525651) ^ 1389 = 143006070585 := by
        calc
          (2 : ZMod 1457992525651) ^ 1389 = (2 : ZMod 1457992525651) ^ (694 + 694 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 694 * (2 : ZMod 1457992525651) ^ 694) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 143006070585 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 1457992525651) ^ 2779 = 594743679577 := by
        calc
          (2 : ZMod 1457992525651) ^ 2779 = (2 : ZMod 1457992525651) ^ (1389 + 1389 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 1389 * (2 : ZMod 1457992525651) ^ 1389) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 594743679577 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 1457992525651) ^ 5559 = 954865349404 := by
        calc
          (2 : ZMod 1457992525651) ^ 5559 = (2 : ZMod 1457992525651) ^ (2779 + 2779 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 2779 * (2 : ZMod 1457992525651) ^ 2779) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 954865349404 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 1457992525651) ^ 11118 = 158130576278 := by
        calc
          (2 : ZMod 1457992525651) ^ 11118 = (2 : ZMod 1457992525651) ^ (5559 + 5559) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 5559 * (2 : ZMod 1457992525651) ^ 5559 := by rw [pow_add]
          _ = 158130576278 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 1457992525651) ^ 22237 = 1169746232127 := by
        calc
          (2 : ZMod 1457992525651) ^ 22237 = (2 : ZMod 1457992525651) ^ (11118 + 11118 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 11118 * (2 : ZMod 1457992525651) ^ 11118) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1169746232127 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 1457992525651) ^ 44475 = 1249940869498 := by
        calc
          (2 : ZMod 1457992525651) ^ 44475 = (2 : ZMod 1457992525651) ^ (22237 + 22237 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = ((2 : ZMod 1457992525651) ^ 22237 * (2 : ZMod 1457992525651) ^ 22237) * (2 : ZMod 1457992525651) := by rw [pow_succ, pow_add]
          _ = 1249940869498 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 1457992525651) ^ 88950 = 1039966153651 := by
        calc
          (2 : ZMod 1457992525651) ^ 88950 = (2 : ZMod 1457992525651) ^ (44475 + 44475) :=
            congrArg (fun n : ℕ => (2 : ZMod 1457992525651) ^ n) (by norm_num)
          _ = (2 : ZMod 1457992525651) ^ 44475 * (2 : ZMod 1457992525651) ^ 44475 := by rw [pow_add]
          _ = 1039966153651 := by rw [factor_4_15]; decide
      change (2 : ZMod 1457992525651) ^ 88950 ≠ 1
      rw [factor_4_16]
      decide

#print axioms prime_lucas_1457992525651

end TotientTailPeriodKiller
end Erdos249257
