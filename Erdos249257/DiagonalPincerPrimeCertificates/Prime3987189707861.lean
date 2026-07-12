import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3987189707861 : Nat.Prime 3987189707861 := by
  apply lucas_primality 3987189707861 (2 : ZMod 3987189707861)
  ·
      have fermat_0 : (2 : ZMod 3987189707861) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 3987189707861) ^ 3 = 8 := by
        calc
          (2 : ZMod 3987189707861) ^ 3 = (2 : ZMod 3987189707861) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1 * (2 : ZMod 3987189707861) ^ 1) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 3987189707861) ^ 7 = 128 := by
        calc
          (2 : ZMod 3987189707861) ^ 7 = (2 : ZMod 3987189707861) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 3 * (2 : ZMod 3987189707861) ^ 3) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 3987189707861) ^ 14 = 16384 := by
        calc
          (2 : ZMod 3987189707861) ^ 14 = (2 : ZMod 3987189707861) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 7 * (2 : ZMod 3987189707861) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 3987189707861) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 3987189707861) ^ 29 = (2 : ZMod 3987189707861) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 14 * (2 : ZMod 3987189707861) ^ 14) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 3987189707861) ^ 58 = 419360147915 := by
        calc
          (2 : ZMod 3987189707861) ^ 58 = (2 : ZMod 3987189707861) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 29 * (2 : ZMod 3987189707861) ^ 29 := by rw [pow_add]
          _ = 419360147915 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 3987189707861) ^ 116 = 1198306903616 := by
        calc
          (2 : ZMod 3987189707861) ^ 116 = (2 : ZMod 3987189707861) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 58 * (2 : ZMod 3987189707861) ^ 58 := by rw [pow_add]
          _ = 1198306903616 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 3987189707861) ^ 232 = 2177142218266 := by
        calc
          (2 : ZMod 3987189707861) ^ 232 = (2 : ZMod 3987189707861) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 116 * (2 : ZMod 3987189707861) ^ 116 := by rw [pow_add]
          _ = 2177142218266 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 3987189707861) ^ 464 = 990329557876 := by
        calc
          (2 : ZMod 3987189707861) ^ 464 = (2 : ZMod 3987189707861) ^ (232 + 232) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 232 * (2 : ZMod 3987189707861) ^ 232 := by rw [pow_add]
          _ = 990329557876 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 3987189707861) ^ 928 = 2036511655446 := by
        calc
          (2 : ZMod 3987189707861) ^ 928 = (2 : ZMod 3987189707861) ^ (464 + 464) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 464 * (2 : ZMod 3987189707861) ^ 464 := by rw [pow_add]
          _ = 2036511655446 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 3987189707861) ^ 1856 = 3983866530649 := by
        calc
          (2 : ZMod 3987189707861) ^ 1856 = (2 : ZMod 3987189707861) ^ (928 + 928) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 928 * (2 : ZMod 3987189707861) ^ 928 := by rw [pow_add]
          _ = 3983866530649 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 3987189707861) ^ 3713 = 101154423554 := by
        calc
          (2 : ZMod 3987189707861) ^ 3713 = (2 : ZMod 3987189707861) ^ (1856 + 1856 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1856 * (2 : ZMod 3987189707861) ^ 1856) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 101154423554 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 3987189707861) ^ 7426 = 3726335825669 := by
        calc
          (2 : ZMod 3987189707861) ^ 7426 = (2 : ZMod 3987189707861) ^ (3713 + 3713) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3713 * (2 : ZMod 3987189707861) ^ 3713 := by rw [pow_add]
          _ = 3726335825669 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 3987189707861) ^ 14853 = 1430758825493 := by
        calc
          (2 : ZMod 3987189707861) ^ 14853 = (2 : ZMod 3987189707861) ^ (7426 + 7426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 7426 * (2 : ZMod 3987189707861) ^ 7426) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1430758825493 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 3987189707861) ^ 29706 = 1060437513402 := by
        calc
          (2 : ZMod 3987189707861) ^ 29706 = (2 : ZMod 3987189707861) ^ (14853 + 14853) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 14853 * (2 : ZMod 3987189707861) ^ 14853 := by rw [pow_add]
          _ = 1060437513402 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 3987189707861) ^ 59413 = 200694269804 := by
        calc
          (2 : ZMod 3987189707861) ^ 59413 = (2 : ZMod 3987189707861) ^ (29706 + 29706 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 29706 * (2 : ZMod 3987189707861) ^ 29706) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 200694269804 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 3987189707861) ^ 118827 = 1212640008844 := by
        calc
          (2 : ZMod 3987189707861) ^ 118827 = (2 : ZMod 3987189707861) ^ (59413 + 59413 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 59413 * (2 : ZMod 3987189707861) ^ 59413) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1212640008844 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 3987189707861) ^ 237655 = 3855675714965 := by
        calc
          (2 : ZMod 3987189707861) ^ 237655 = (2 : ZMod 3987189707861) ^ (118827 + 118827 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 118827 * (2 : ZMod 3987189707861) ^ 118827) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3855675714965 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 3987189707861) ^ 475310 = 731416439893 := by
        calc
          (2 : ZMod 3987189707861) ^ 475310 = (2 : ZMod 3987189707861) ^ (237655 + 237655) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 237655 * (2 : ZMod 3987189707861) ^ 237655 := by rw [pow_add]
          _ = 731416439893 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 3987189707861) ^ 950620 = 199160521188 := by
        calc
          (2 : ZMod 3987189707861) ^ 950620 = (2 : ZMod 3987189707861) ^ (475310 + 475310) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 475310 * (2 : ZMod 3987189707861) ^ 475310 := by rw [pow_add]
          _ = 199160521188 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 3987189707861) ^ 1901240 = 2523582016347 := by
        calc
          (2 : ZMod 3987189707861) ^ 1901240 = (2 : ZMod 3987189707861) ^ (950620 + 950620) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 950620 * (2 : ZMod 3987189707861) ^ 950620 := by rw [pow_add]
          _ = 2523582016347 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 3987189707861) ^ 3802480 = 3116126704470 := by
        calc
          (2 : ZMod 3987189707861) ^ 3802480 = (2 : ZMod 3987189707861) ^ (1901240 + 1901240) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1901240 * (2 : ZMod 3987189707861) ^ 1901240 := by rw [pow_add]
          _ = 3116126704470 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 3987189707861) ^ 7604960 = 1683810296817 := by
        calc
          (2 : ZMod 3987189707861) ^ 7604960 = (2 : ZMod 3987189707861) ^ (3802480 + 3802480) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3802480 * (2 : ZMod 3987189707861) ^ 3802480 := by rw [pow_add]
          _ = 1683810296817 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 3987189707861) ^ 15209921 = 3774519681245 := by
        calc
          (2 : ZMod 3987189707861) ^ 15209921 = (2 : ZMod 3987189707861) ^ (7604960 + 7604960 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 7604960 * (2 : ZMod 3987189707861) ^ 7604960) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3774519681245 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 3987189707861) ^ 30419843 = 3810051135123 := by
        calc
          (2 : ZMod 3987189707861) ^ 30419843 = (2 : ZMod 3987189707861) ^ (15209921 + 15209921 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 15209921 * (2 : ZMod 3987189707861) ^ 15209921) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3810051135123 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 3987189707861) ^ 60839686 = 3555647185238 := by
        calc
          (2 : ZMod 3987189707861) ^ 60839686 = (2 : ZMod 3987189707861) ^ (30419843 + 30419843) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 30419843 * (2 : ZMod 3987189707861) ^ 30419843 := by rw [pow_add]
          _ = 3555647185238 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 3987189707861) ^ 121679373 = 1507996519943 := by
        calc
          (2 : ZMod 3987189707861) ^ 121679373 = (2 : ZMod 3987189707861) ^ (60839686 + 60839686 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 60839686 * (2 : ZMod 3987189707861) ^ 60839686) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1507996519943 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 3987189707861) ^ 243358746 = 2996433785285 := by
        calc
          (2 : ZMod 3987189707861) ^ 243358746 = (2 : ZMod 3987189707861) ^ (121679373 + 121679373) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 121679373 * (2 : ZMod 3987189707861) ^ 121679373 := by rw [pow_add]
          _ = 2996433785285 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 3987189707861) ^ 486717493 = 1581303480037 := by
        calc
          (2 : ZMod 3987189707861) ^ 486717493 = (2 : ZMod 3987189707861) ^ (243358746 + 243358746 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 243358746 * (2 : ZMod 3987189707861) ^ 243358746) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1581303480037 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 3987189707861) ^ 973434987 = 2529782417991 := by
        calc
          (2 : ZMod 3987189707861) ^ 973434987 = (2 : ZMod 3987189707861) ^ (486717493 + 486717493 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 486717493 * (2 : ZMod 3987189707861) ^ 486717493) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2529782417991 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 3987189707861) ^ 1946869974 = 870529152209 := by
        calc
          (2 : ZMod 3987189707861) ^ 1946869974 = (2 : ZMod 3987189707861) ^ (973434987 + 973434987) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 973434987 * (2 : ZMod 3987189707861) ^ 973434987 := by rw [pow_add]
          _ = 870529152209 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 3987189707861) ^ 3893739949 = 1345283418890 := by
        calc
          (2 : ZMod 3987189707861) ^ 3893739949 = (2 : ZMod 3987189707861) ^ (1946869974 + 1946869974 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1946869974 * (2 : ZMod 3987189707861) ^ 1946869974) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1345283418890 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 3987189707861) ^ 7787479898 = 840954275833 := by
        calc
          (2 : ZMod 3987189707861) ^ 7787479898 = (2 : ZMod 3987189707861) ^ (3893739949 + 3893739949) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3893739949 * (2 : ZMod 3987189707861) ^ 3893739949 := by rw [pow_add]
          _ = 840954275833 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 3987189707861) ^ 15574959796 = 123944850487 := by
        calc
          (2 : ZMod 3987189707861) ^ 15574959796 = (2 : ZMod 3987189707861) ^ (7787479898 + 7787479898) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 7787479898 * (2 : ZMod 3987189707861) ^ 7787479898 := by rw [pow_add]
          _ = 123944850487 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 3987189707861) ^ 31149919592 = 2640699121419 := by
        calc
          (2 : ZMod 3987189707861) ^ 31149919592 = (2 : ZMod 3987189707861) ^ (15574959796 + 15574959796) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 15574959796 * (2 : ZMod 3987189707861) ^ 15574959796 := by rw [pow_add]
          _ = 2640699121419 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 3987189707861) ^ 62299839185 = 244598611982 := by
        calc
          (2 : ZMod 3987189707861) ^ 62299839185 = (2 : ZMod 3987189707861) ^ (31149919592 + 31149919592 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 31149919592 * (2 : ZMod 3987189707861) ^ 31149919592) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 244598611982 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 3987189707861) ^ 124599678370 = 196894823148 := by
        calc
          (2 : ZMod 3987189707861) ^ 124599678370 = (2 : ZMod 3987189707861) ^ (62299839185 + 62299839185) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 62299839185 * (2 : ZMod 3987189707861) ^ 62299839185 := by rw [pow_add]
          _ = 196894823148 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 3987189707861) ^ 249199356741 = 2587509410600 := by
        calc
          (2 : ZMod 3987189707861) ^ 249199356741 = (2 : ZMod 3987189707861) ^ (124599678370 + 124599678370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 124599678370 * (2 : ZMod 3987189707861) ^ 124599678370) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2587509410600 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 3987189707861) ^ 498398713482 = 2826703228211 := by
        calc
          (2 : ZMod 3987189707861) ^ 498398713482 = (2 : ZMod 3987189707861) ^ (249199356741 + 249199356741) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 249199356741 * (2 : ZMod 3987189707861) ^ 249199356741 := by rw [pow_add]
          _ = 2826703228211 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 3987189707861) ^ 996797426965 = 1666216748560 := by
        calc
          (2 : ZMod 3987189707861) ^ 996797426965 = (2 : ZMod 3987189707861) ^ (498398713482 + 498398713482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 498398713482 * (2 : ZMod 3987189707861) ^ 498398713482) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1666216748560 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 3987189707861) ^ 1993594853930 = 3987189707860 := by
        calc
          (2 : ZMod 3987189707861) ^ 1993594853930 = (2 : ZMod 3987189707861) ^ (996797426965 + 996797426965) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 996797426965 * (2 : ZMod 3987189707861) ^ 996797426965 := by rw [pow_add]
          _ = 3987189707860 := by rw [fermat_39]; decide
      have fermat_41 : (2 : ZMod 3987189707861) ^ 3987189707860 = 1 := by
        calc
          (2 : ZMod 3987189707861) ^ 3987189707860 = (2 : ZMod 3987189707861) ^ (1993594853930 + 1993594853930) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1993594853930 * (2 : ZMod 3987189707861) ^ 1993594853930 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (41, 1), (10651, 1), (456523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (41, 1), (10651, 1), (456523, 1)] : List FactorBlock).map factorBlockValue).prod = 3987189707861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 3987189707861) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 3987189707861) ^ 3 = 8 := by
        calc
          (2 : ZMod 3987189707861) ^ 3 = (2 : ZMod 3987189707861) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1 * (2 : ZMod 3987189707861) ^ 1) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 3987189707861) ^ 7 = 128 := by
        calc
          (2 : ZMod 3987189707861) ^ 7 = (2 : ZMod 3987189707861) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 3 * (2 : ZMod 3987189707861) ^ 3) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 3987189707861) ^ 14 = 16384 := by
        calc
          (2 : ZMod 3987189707861) ^ 14 = (2 : ZMod 3987189707861) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 7 * (2 : ZMod 3987189707861) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 3987189707861) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 3987189707861) ^ 29 = (2 : ZMod 3987189707861) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 14 * (2 : ZMod 3987189707861) ^ 14) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 3987189707861) ^ 58 = 419360147915 := by
        calc
          (2 : ZMod 3987189707861) ^ 58 = (2 : ZMod 3987189707861) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 29 * (2 : ZMod 3987189707861) ^ 29 := by rw [pow_add]
          _ = 419360147915 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 3987189707861) ^ 116 = 1198306903616 := by
        calc
          (2 : ZMod 3987189707861) ^ 116 = (2 : ZMod 3987189707861) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 58 * (2 : ZMod 3987189707861) ^ 58 := by rw [pow_add]
          _ = 1198306903616 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 3987189707861) ^ 232 = 2177142218266 := by
        calc
          (2 : ZMod 3987189707861) ^ 232 = (2 : ZMod 3987189707861) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 116 * (2 : ZMod 3987189707861) ^ 116 := by rw [pow_add]
          _ = 2177142218266 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 3987189707861) ^ 464 = 990329557876 := by
        calc
          (2 : ZMod 3987189707861) ^ 464 = (2 : ZMod 3987189707861) ^ (232 + 232) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 232 * (2 : ZMod 3987189707861) ^ 232 := by rw [pow_add]
          _ = 990329557876 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 3987189707861) ^ 928 = 2036511655446 := by
        calc
          (2 : ZMod 3987189707861) ^ 928 = (2 : ZMod 3987189707861) ^ (464 + 464) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 464 * (2 : ZMod 3987189707861) ^ 464 := by rw [pow_add]
          _ = 2036511655446 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 3987189707861) ^ 1856 = 3983866530649 := by
        calc
          (2 : ZMod 3987189707861) ^ 1856 = (2 : ZMod 3987189707861) ^ (928 + 928) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 928 * (2 : ZMod 3987189707861) ^ 928 := by rw [pow_add]
          _ = 3983866530649 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 3987189707861) ^ 3713 = 101154423554 := by
        calc
          (2 : ZMod 3987189707861) ^ 3713 = (2 : ZMod 3987189707861) ^ (1856 + 1856 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1856 * (2 : ZMod 3987189707861) ^ 1856) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 101154423554 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 3987189707861) ^ 7426 = 3726335825669 := by
        calc
          (2 : ZMod 3987189707861) ^ 7426 = (2 : ZMod 3987189707861) ^ (3713 + 3713) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3713 * (2 : ZMod 3987189707861) ^ 3713 := by rw [pow_add]
          _ = 3726335825669 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 3987189707861) ^ 14853 = 1430758825493 := by
        calc
          (2 : ZMod 3987189707861) ^ 14853 = (2 : ZMod 3987189707861) ^ (7426 + 7426 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 7426 * (2 : ZMod 3987189707861) ^ 7426) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1430758825493 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 3987189707861) ^ 29706 = 1060437513402 := by
        calc
          (2 : ZMod 3987189707861) ^ 29706 = (2 : ZMod 3987189707861) ^ (14853 + 14853) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 14853 * (2 : ZMod 3987189707861) ^ 14853 := by rw [pow_add]
          _ = 1060437513402 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 3987189707861) ^ 59413 = 200694269804 := by
        calc
          (2 : ZMod 3987189707861) ^ 59413 = (2 : ZMod 3987189707861) ^ (29706 + 29706 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 29706 * (2 : ZMod 3987189707861) ^ 29706) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 200694269804 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 3987189707861) ^ 118827 = 1212640008844 := by
        calc
          (2 : ZMod 3987189707861) ^ 118827 = (2 : ZMod 3987189707861) ^ (59413 + 59413 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 59413 * (2 : ZMod 3987189707861) ^ 59413) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1212640008844 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 3987189707861) ^ 237655 = 3855675714965 := by
        calc
          (2 : ZMod 3987189707861) ^ 237655 = (2 : ZMod 3987189707861) ^ (118827 + 118827 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 118827 * (2 : ZMod 3987189707861) ^ 118827) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3855675714965 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 3987189707861) ^ 475310 = 731416439893 := by
        calc
          (2 : ZMod 3987189707861) ^ 475310 = (2 : ZMod 3987189707861) ^ (237655 + 237655) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 237655 * (2 : ZMod 3987189707861) ^ 237655 := by rw [pow_add]
          _ = 731416439893 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 3987189707861) ^ 950620 = 199160521188 := by
        calc
          (2 : ZMod 3987189707861) ^ 950620 = (2 : ZMod 3987189707861) ^ (475310 + 475310) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 475310 * (2 : ZMod 3987189707861) ^ 475310 := by rw [pow_add]
          _ = 199160521188 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 3987189707861) ^ 1901240 = 2523582016347 := by
        calc
          (2 : ZMod 3987189707861) ^ 1901240 = (2 : ZMod 3987189707861) ^ (950620 + 950620) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 950620 * (2 : ZMod 3987189707861) ^ 950620 := by rw [pow_add]
          _ = 2523582016347 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 3987189707861) ^ 3802480 = 3116126704470 := by
        calc
          (2 : ZMod 3987189707861) ^ 3802480 = (2 : ZMod 3987189707861) ^ (1901240 + 1901240) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1901240 * (2 : ZMod 3987189707861) ^ 1901240 := by rw [pow_add]
          _ = 3116126704470 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 3987189707861) ^ 7604960 = 1683810296817 := by
        calc
          (2 : ZMod 3987189707861) ^ 7604960 = (2 : ZMod 3987189707861) ^ (3802480 + 3802480) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3802480 * (2 : ZMod 3987189707861) ^ 3802480 := by rw [pow_add]
          _ = 1683810296817 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 3987189707861) ^ 15209921 = 3774519681245 := by
        calc
          (2 : ZMod 3987189707861) ^ 15209921 = (2 : ZMod 3987189707861) ^ (7604960 + 7604960 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 7604960 * (2 : ZMod 3987189707861) ^ 7604960) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3774519681245 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 3987189707861) ^ 30419843 = 3810051135123 := by
        calc
          (2 : ZMod 3987189707861) ^ 30419843 = (2 : ZMod 3987189707861) ^ (15209921 + 15209921 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 15209921 * (2 : ZMod 3987189707861) ^ 15209921) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3810051135123 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 3987189707861) ^ 60839686 = 3555647185238 := by
        calc
          (2 : ZMod 3987189707861) ^ 60839686 = (2 : ZMod 3987189707861) ^ (30419843 + 30419843) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 30419843 * (2 : ZMod 3987189707861) ^ 30419843 := by rw [pow_add]
          _ = 3555647185238 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 3987189707861) ^ 121679373 = 1507996519943 := by
        calc
          (2 : ZMod 3987189707861) ^ 121679373 = (2 : ZMod 3987189707861) ^ (60839686 + 60839686 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 60839686 * (2 : ZMod 3987189707861) ^ 60839686) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1507996519943 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 3987189707861) ^ 243358746 = 2996433785285 := by
        calc
          (2 : ZMod 3987189707861) ^ 243358746 = (2 : ZMod 3987189707861) ^ (121679373 + 121679373) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 121679373 * (2 : ZMod 3987189707861) ^ 121679373 := by rw [pow_add]
          _ = 2996433785285 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 3987189707861) ^ 486717493 = 1581303480037 := by
        calc
          (2 : ZMod 3987189707861) ^ 486717493 = (2 : ZMod 3987189707861) ^ (243358746 + 243358746 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 243358746 * (2 : ZMod 3987189707861) ^ 243358746) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1581303480037 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 3987189707861) ^ 973434987 = 2529782417991 := by
        calc
          (2 : ZMod 3987189707861) ^ 973434987 = (2 : ZMod 3987189707861) ^ (486717493 + 486717493 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 486717493 * (2 : ZMod 3987189707861) ^ 486717493) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2529782417991 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 3987189707861) ^ 1946869974 = 870529152209 := by
        calc
          (2 : ZMod 3987189707861) ^ 1946869974 = (2 : ZMod 3987189707861) ^ (973434987 + 973434987) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 973434987 * (2 : ZMod 3987189707861) ^ 973434987 := by rw [pow_add]
          _ = 870529152209 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 3987189707861) ^ 3893739949 = 1345283418890 := by
        calc
          (2 : ZMod 3987189707861) ^ 3893739949 = (2 : ZMod 3987189707861) ^ (1946869974 + 1946869974 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1946869974 * (2 : ZMod 3987189707861) ^ 1946869974) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1345283418890 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 3987189707861) ^ 7787479898 = 840954275833 := by
        calc
          (2 : ZMod 3987189707861) ^ 7787479898 = (2 : ZMod 3987189707861) ^ (3893739949 + 3893739949) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3893739949 * (2 : ZMod 3987189707861) ^ 3893739949 := by rw [pow_add]
          _ = 840954275833 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 3987189707861) ^ 15574959796 = 123944850487 := by
        calc
          (2 : ZMod 3987189707861) ^ 15574959796 = (2 : ZMod 3987189707861) ^ (7787479898 + 7787479898) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 7787479898 * (2 : ZMod 3987189707861) ^ 7787479898 := by rw [pow_add]
          _ = 123944850487 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 3987189707861) ^ 31149919592 = 2640699121419 := by
        calc
          (2 : ZMod 3987189707861) ^ 31149919592 = (2 : ZMod 3987189707861) ^ (15574959796 + 15574959796) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 15574959796 * (2 : ZMod 3987189707861) ^ 15574959796 := by rw [pow_add]
          _ = 2640699121419 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 3987189707861) ^ 62299839185 = 244598611982 := by
        calc
          (2 : ZMod 3987189707861) ^ 62299839185 = (2 : ZMod 3987189707861) ^ (31149919592 + 31149919592 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 31149919592 * (2 : ZMod 3987189707861) ^ 31149919592) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 244598611982 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 3987189707861) ^ 124599678370 = 196894823148 := by
        calc
          (2 : ZMod 3987189707861) ^ 124599678370 = (2 : ZMod 3987189707861) ^ (62299839185 + 62299839185) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 62299839185 * (2 : ZMod 3987189707861) ^ 62299839185 := by rw [pow_add]
          _ = 196894823148 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 3987189707861) ^ 249199356741 = 2587509410600 := by
        calc
          (2 : ZMod 3987189707861) ^ 249199356741 = (2 : ZMod 3987189707861) ^ (124599678370 + 124599678370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 124599678370 * (2 : ZMod 3987189707861) ^ 124599678370) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2587509410600 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 3987189707861) ^ 498398713482 = 2826703228211 := by
        calc
          (2 : ZMod 3987189707861) ^ 498398713482 = (2 : ZMod 3987189707861) ^ (249199356741 + 249199356741) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 249199356741 * (2 : ZMod 3987189707861) ^ 249199356741 := by rw [pow_add]
          _ = 2826703228211 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 3987189707861) ^ 996797426965 = 1666216748560 := by
        calc
          (2 : ZMod 3987189707861) ^ 996797426965 = (2 : ZMod 3987189707861) ^ (498398713482 + 498398713482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 498398713482 * (2 : ZMod 3987189707861) ^ 498398713482) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1666216748560 := by rw [factor_0_38]; decide
      have factor_0_40 : (2 : ZMod 3987189707861) ^ 1993594853930 = 3987189707860 := by
        calc
          (2 : ZMod 3987189707861) ^ 1993594853930 = (2 : ZMod 3987189707861) ^ (996797426965 + 996797426965) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 996797426965 * (2 : ZMod 3987189707861) ^ 996797426965 := by rw [pow_add]
          _ = 3987189707860 := by rw [factor_0_39]; decide
      change (2 : ZMod 3987189707861) ^ 1993594853930 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (2 : ZMod 3987189707861) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 3987189707861) ^ 2 = 4 := by
        calc
          (2 : ZMod 3987189707861) ^ 2 = (2 : ZMod 3987189707861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1 * (2 : ZMod 3987189707861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 3987189707861) ^ 5 = 32 := by
        calc
          (2 : ZMod 3987189707861) ^ 5 = (2 : ZMod 3987189707861) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 2 * (2 : ZMod 3987189707861) ^ 2) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 3987189707861) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3987189707861) ^ 11 = (2 : ZMod 3987189707861) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 5 * (2 : ZMod 3987189707861) ^ 5) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 3987189707861) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 3987189707861) ^ 23 = (2 : ZMod 3987189707861) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 11 * (2 : ZMod 3987189707861) ^ 11) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 3987189707861) ^ 46 = 2586519144027 := by
        calc
          (2 : ZMod 3987189707861) ^ 46 = (2 : ZMod 3987189707861) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 23 * (2 : ZMod 3987189707861) ^ 23 := by rw [pow_add]
          _ = 2586519144027 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 3987189707861) ^ 92 = 2376322184491 := by
        calc
          (2 : ZMod 3987189707861) ^ 92 = (2 : ZMod 3987189707861) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 46 * (2 : ZMod 3987189707861) ^ 46 := by rw [pow_add]
          _ = 2376322184491 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 3987189707861) ^ 185 = 3185599353769 := by
        calc
          (2 : ZMod 3987189707861) ^ 185 = (2 : ZMod 3987189707861) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 92 * (2 : ZMod 3987189707861) ^ 92) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3185599353769 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 3987189707861) ^ 371 = 2095499854440 := by
        calc
          (2 : ZMod 3987189707861) ^ 371 = (2 : ZMod 3987189707861) ^ (185 + 185 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 185 * (2 : ZMod 3987189707861) ^ 185) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2095499854440 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 3987189707861) ^ 742 = 942129483167 := by
        calc
          (2 : ZMod 3987189707861) ^ 742 = (2 : ZMod 3987189707861) ^ (371 + 371) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 371 * (2 : ZMod 3987189707861) ^ 371 := by rw [pow_add]
          _ = 942129483167 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 3987189707861) ^ 1485 = 2949105588020 := by
        calc
          (2 : ZMod 3987189707861) ^ 1485 = (2 : ZMod 3987189707861) ^ (742 + 742 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 742 * (2 : ZMod 3987189707861) ^ 742) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2949105588020 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 3987189707861) ^ 2970 = 1824325277096 := by
        calc
          (2 : ZMod 3987189707861) ^ 2970 = (2 : ZMod 3987189707861) ^ (1485 + 1485) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1485 * (2 : ZMod 3987189707861) ^ 1485 := by rw [pow_add]
          _ = 1824325277096 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 3987189707861) ^ 5941 = 2528845131138 := by
        calc
          (2 : ZMod 3987189707861) ^ 5941 = (2 : ZMod 3987189707861) ^ (2970 + 2970 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 2970 * (2 : ZMod 3987189707861) ^ 2970) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2528845131138 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 3987189707861) ^ 11882 = 2652371689741 := by
        calc
          (2 : ZMod 3987189707861) ^ 11882 = (2 : ZMod 3987189707861) ^ (5941 + 5941) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 5941 * (2 : ZMod 3987189707861) ^ 5941 := by rw [pow_add]
          _ = 2652371689741 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 3987189707861) ^ 23765 = 3168666357650 := by
        calc
          (2 : ZMod 3987189707861) ^ 23765 = (2 : ZMod 3987189707861) ^ (11882 + 11882 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 11882 * (2 : ZMod 3987189707861) ^ 11882) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3168666357650 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 3987189707861) ^ 47531 = 295316939123 := by
        calc
          (2 : ZMod 3987189707861) ^ 47531 = (2 : ZMod 3987189707861) ^ (23765 + 23765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 23765 * (2 : ZMod 3987189707861) ^ 23765) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 295316939123 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 3987189707861) ^ 95062 = 1680269968240 := by
        calc
          (2 : ZMod 3987189707861) ^ 95062 = (2 : ZMod 3987189707861) ^ (47531 + 47531) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 47531 * (2 : ZMod 3987189707861) ^ 47531 := by rw [pow_add]
          _ = 1680269968240 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 3987189707861) ^ 190124 = 529852353955 := by
        calc
          (2 : ZMod 3987189707861) ^ 190124 = (2 : ZMod 3987189707861) ^ (95062 + 95062) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 95062 * (2 : ZMod 3987189707861) ^ 95062 := by rw [pow_add]
          _ = 529852353955 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 3987189707861) ^ 380248 = 2679258128561 := by
        calc
          (2 : ZMod 3987189707861) ^ 380248 = (2 : ZMod 3987189707861) ^ (190124 + 190124) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 190124 * (2 : ZMod 3987189707861) ^ 190124 := by rw [pow_add]
          _ = 2679258128561 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 3987189707861) ^ 760496 = 1847447000050 := by
        calc
          (2 : ZMod 3987189707861) ^ 760496 = (2 : ZMod 3987189707861) ^ (380248 + 380248) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 380248 * (2 : ZMod 3987189707861) ^ 380248 := by rw [pow_add]
          _ = 1847447000050 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 3987189707861) ^ 1520992 = 1316580607658 := by
        calc
          (2 : ZMod 3987189707861) ^ 1520992 = (2 : ZMod 3987189707861) ^ (760496 + 760496) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 760496 * (2 : ZMod 3987189707861) ^ 760496 := by rw [pow_add]
          _ = 1316580607658 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 3987189707861) ^ 3041984 = 1015704744754 := by
        calc
          (2 : ZMod 3987189707861) ^ 3041984 = (2 : ZMod 3987189707861) ^ (1520992 + 1520992) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1520992 * (2 : ZMod 3987189707861) ^ 1520992 := by rw [pow_add]
          _ = 1015704744754 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 3987189707861) ^ 6083968 = 203669039815 := by
        calc
          (2 : ZMod 3987189707861) ^ 6083968 = (2 : ZMod 3987189707861) ^ (3041984 + 3041984) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3041984 * (2 : ZMod 3987189707861) ^ 3041984 := by rw [pow_add]
          _ = 203669039815 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 3987189707861) ^ 12167937 = 1635801143382 := by
        calc
          (2 : ZMod 3987189707861) ^ 12167937 = (2 : ZMod 3987189707861) ^ (6083968 + 6083968 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 6083968 * (2 : ZMod 3987189707861) ^ 6083968) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1635801143382 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 3987189707861) ^ 24335874 = 2070141479198 := by
        calc
          (2 : ZMod 3987189707861) ^ 24335874 = (2 : ZMod 3987189707861) ^ (12167937 + 12167937) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 12167937 * (2 : ZMod 3987189707861) ^ 12167937 := by rw [pow_add]
          _ = 2070141479198 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 3987189707861) ^ 48671749 = 3299310468223 := by
        calc
          (2 : ZMod 3987189707861) ^ 48671749 = (2 : ZMod 3987189707861) ^ (24335874 + 24335874 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 24335874 * (2 : ZMod 3987189707861) ^ 24335874) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3299310468223 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 3987189707861) ^ 97343498 = 3407127237507 := by
        calc
          (2 : ZMod 3987189707861) ^ 97343498 = (2 : ZMod 3987189707861) ^ (48671749 + 48671749) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 48671749 * (2 : ZMod 3987189707861) ^ 48671749 := by rw [pow_add]
          _ = 3407127237507 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 3987189707861) ^ 194686997 = 3568171253453 := by
        calc
          (2 : ZMod 3987189707861) ^ 194686997 = (2 : ZMod 3987189707861) ^ (97343498 + 97343498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 97343498 * (2 : ZMod 3987189707861) ^ 97343498) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3568171253453 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 3987189707861) ^ 389373994 = 409555638302 := by
        calc
          (2 : ZMod 3987189707861) ^ 389373994 = (2 : ZMod 3987189707861) ^ (194686997 + 194686997) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 194686997 * (2 : ZMod 3987189707861) ^ 194686997 := by rw [pow_add]
          _ = 409555638302 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 3987189707861) ^ 778747989 = 2498738784935 := by
        calc
          (2 : ZMod 3987189707861) ^ 778747989 = (2 : ZMod 3987189707861) ^ (389373994 + 389373994 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 389373994 * (2 : ZMod 3987189707861) ^ 389373994) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2498738784935 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 3987189707861) ^ 1557495979 = 579724482910 := by
        calc
          (2 : ZMod 3987189707861) ^ 1557495979 = (2 : ZMod 3987189707861) ^ (778747989 + 778747989 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 778747989 * (2 : ZMod 3987189707861) ^ 778747989) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 579724482910 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 3987189707861) ^ 3114991959 = 1797990738085 := by
        calc
          (2 : ZMod 3987189707861) ^ 3114991959 = (2 : ZMod 3987189707861) ^ (1557495979 + 1557495979 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1557495979 * (2 : ZMod 3987189707861) ^ 1557495979) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1797990738085 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 3987189707861) ^ 6229983918 = 1382355050443 := by
        calc
          (2 : ZMod 3987189707861) ^ 6229983918 = (2 : ZMod 3987189707861) ^ (3114991959 + 3114991959) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 3114991959 * (2 : ZMod 3987189707861) ^ 3114991959 := by rw [pow_add]
          _ = 1382355050443 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 3987189707861) ^ 12459967837 = 1857553806525 := by
        calc
          (2 : ZMod 3987189707861) ^ 12459967837 = (2 : ZMod 3987189707861) ^ (6229983918 + 6229983918 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 6229983918 * (2 : ZMod 3987189707861) ^ 6229983918) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1857553806525 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 3987189707861) ^ 24919935674 = 2945792750036 := by
        calc
          (2 : ZMod 3987189707861) ^ 24919935674 = (2 : ZMod 3987189707861) ^ (12459967837 + 12459967837) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 12459967837 * (2 : ZMod 3987189707861) ^ 12459967837 := by rw [pow_add]
          _ = 2945792750036 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 3987189707861) ^ 49839871348 = 702375447225 := by
        calc
          (2 : ZMod 3987189707861) ^ 49839871348 = (2 : ZMod 3987189707861) ^ (24919935674 + 24919935674) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 24919935674 * (2 : ZMod 3987189707861) ^ 24919935674 := by rw [pow_add]
          _ = 702375447225 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 3987189707861) ^ 99679742696 = 3294270183191 := by
        calc
          (2 : ZMod 3987189707861) ^ 99679742696 = (2 : ZMod 3987189707861) ^ (49839871348 + 49839871348) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 49839871348 * (2 : ZMod 3987189707861) ^ 49839871348 := by rw [pow_add]
          _ = 3294270183191 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 3987189707861) ^ 199359485393 = 2192576852123 := by
        calc
          (2 : ZMod 3987189707861) ^ 199359485393 = (2 : ZMod 3987189707861) ^ (99679742696 + 99679742696 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 99679742696 * (2 : ZMod 3987189707861) ^ 99679742696) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2192576852123 := by rw [factor_1_36]; decide
      have factor_1_38 : (2 : ZMod 3987189707861) ^ 398718970786 = 3786347962984 := by
        calc
          (2 : ZMod 3987189707861) ^ 398718970786 = (2 : ZMod 3987189707861) ^ (199359485393 + 199359485393) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 199359485393 * (2 : ZMod 3987189707861) ^ 199359485393 := by rw [pow_add]
          _ = 3786347962984 := by rw [factor_1_37]; decide
      have factor_1_39 : (2 : ZMod 3987189707861) ^ 797437941572 = 324910921713 := by
        calc
          (2 : ZMod 3987189707861) ^ 797437941572 = (2 : ZMod 3987189707861) ^ (398718970786 + 398718970786) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 398718970786 * (2 : ZMod 3987189707861) ^ 398718970786 := by rw [pow_add]
          _ = 324910921713 := by rw [factor_1_38]; decide
      change (2 : ZMod 3987189707861) ^ 797437941572 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (2 : ZMod 3987189707861) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 3987189707861) ^ 2 = 4 := by
        calc
          (2 : ZMod 3987189707861) ^ 2 = (2 : ZMod 3987189707861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1 * (2 : ZMod 3987189707861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 3987189707861) ^ 5 = 32 := by
        calc
          (2 : ZMod 3987189707861) ^ 5 = (2 : ZMod 3987189707861) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 2 * (2 : ZMod 3987189707861) ^ 2) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 3987189707861) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3987189707861) ^ 11 = (2 : ZMod 3987189707861) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 5 * (2 : ZMod 3987189707861) ^ 5) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 3987189707861) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 3987189707861) ^ 22 = (2 : ZMod 3987189707861) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 11 * (2 : ZMod 3987189707861) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 3987189707861) ^ 45 = 3286854425944 := by
        calc
          (2 : ZMod 3987189707861) ^ 45 = (2 : ZMod 3987189707861) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 22 * (2 : ZMod 3987189707861) ^ 22) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3286854425944 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 3987189707861) ^ 90 = 1590877973088 := by
        calc
          (2 : ZMod 3987189707861) ^ 90 = (2 : ZMod 3987189707861) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 45 * (2 : ZMod 3987189707861) ^ 45 := by rw [pow_add]
          _ = 1590877973088 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 3987189707861) ^ 181 = 2940292883765 := by
        calc
          (2 : ZMod 3987189707861) ^ 181 = (2 : ZMod 3987189707861) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 90 * (2 : ZMod 3987189707861) ^ 90) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2940292883765 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 3987189707861) ^ 362 = 2433786501381 := by
        calc
          (2 : ZMod 3987189707861) ^ 362 = (2 : ZMod 3987189707861) ^ (181 + 181) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 181 * (2 : ZMod 3987189707861) ^ 181 := by rw [pow_add]
          _ = 2433786501381 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 3987189707861) ^ 724 = 3184550525030 := by
        calc
          (2 : ZMod 3987189707861) ^ 724 = (2 : ZMod 3987189707861) ^ (362 + 362) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 362 * (2 : ZMod 3987189707861) ^ 362 := by rw [pow_add]
          _ = 3184550525030 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 3987189707861) ^ 1449 = 3495342454433 := by
        calc
          (2 : ZMod 3987189707861) ^ 1449 = (2 : ZMod 3987189707861) ^ (724 + 724 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 724 * (2 : ZMod 3987189707861) ^ 724) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3495342454433 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 3987189707861) ^ 2898 = 822312247690 := by
        calc
          (2 : ZMod 3987189707861) ^ 2898 = (2 : ZMod 3987189707861) ^ (1449 + 1449) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1449 * (2 : ZMod 3987189707861) ^ 1449 := by rw [pow_add]
          _ = 822312247690 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 3987189707861) ^ 5796 = 1019216021268 := by
        calc
          (2 : ZMod 3987189707861) ^ 5796 = (2 : ZMod 3987189707861) ^ (2898 + 2898) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 2898 * (2 : ZMod 3987189707861) ^ 2898 := by rw [pow_add]
          _ = 1019216021268 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 3987189707861) ^ 11592 = 632742843538 := by
        calc
          (2 : ZMod 3987189707861) ^ 11592 = (2 : ZMod 3987189707861) ^ (5796 + 5796) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 5796 * (2 : ZMod 3987189707861) ^ 5796 := by rw [pow_add]
          _ = 632742843538 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 3987189707861) ^ 23185 = 129962618384 := by
        calc
          (2 : ZMod 3987189707861) ^ 23185 = (2 : ZMod 3987189707861) ^ (11592 + 11592 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 11592 * (2 : ZMod 3987189707861) ^ 11592) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 129962618384 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 3987189707861) ^ 46371 = 1585781831847 := by
        calc
          (2 : ZMod 3987189707861) ^ 46371 = (2 : ZMod 3987189707861) ^ (23185 + 23185 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 23185 * (2 : ZMod 3987189707861) ^ 23185) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1585781831847 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 3987189707861) ^ 92743 = 3526382275560 := by
        calc
          (2 : ZMod 3987189707861) ^ 92743 = (2 : ZMod 3987189707861) ^ (46371 + 46371 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 46371 * (2 : ZMod 3987189707861) ^ 46371) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3526382275560 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 3987189707861) ^ 185486 = 2702728351659 := by
        calc
          (2 : ZMod 3987189707861) ^ 185486 = (2 : ZMod 3987189707861) ^ (92743 + 92743) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 92743 * (2 : ZMod 3987189707861) ^ 92743 := by rw [pow_add]
          _ = 2702728351659 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 3987189707861) ^ 370973 = 89171269731 := by
        calc
          (2 : ZMod 3987189707861) ^ 370973 = (2 : ZMod 3987189707861) ^ (185486 + 185486 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 185486 * (2 : ZMod 3987189707861) ^ 185486) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 89171269731 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 3987189707861) ^ 741947 = 1203390086387 := by
        calc
          (2 : ZMod 3987189707861) ^ 741947 = (2 : ZMod 3987189707861) ^ (370973 + 370973 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 370973 * (2 : ZMod 3987189707861) ^ 370973) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1203390086387 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 3987189707861) ^ 1483894 = 2490982500780 := by
        calc
          (2 : ZMod 3987189707861) ^ 1483894 = (2 : ZMod 3987189707861) ^ (741947 + 741947) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 741947 * (2 : ZMod 3987189707861) ^ 741947 := by rw [pow_add]
          _ = 2490982500780 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 3987189707861) ^ 2967789 = 2574131450767 := by
        calc
          (2 : ZMod 3987189707861) ^ 2967789 = (2 : ZMod 3987189707861) ^ (1483894 + 1483894 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1483894 * (2 : ZMod 3987189707861) ^ 1483894) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2574131450767 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 3987189707861) ^ 5935579 = 710908841866 := by
        calc
          (2 : ZMod 3987189707861) ^ 5935579 = (2 : ZMod 3987189707861) ^ (2967789 + 2967789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 2967789 * (2 : ZMod 3987189707861) ^ 2967789) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 710908841866 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 3987189707861) ^ 11871158 = 1025084403746 := by
        calc
          (2 : ZMod 3987189707861) ^ 11871158 = (2 : ZMod 3987189707861) ^ (5935579 + 5935579) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 5935579 * (2 : ZMod 3987189707861) ^ 5935579 := by rw [pow_add]
          _ = 1025084403746 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 3987189707861) ^ 23742316 = 3847407239026 := by
        calc
          (2 : ZMod 3987189707861) ^ 23742316 = (2 : ZMod 3987189707861) ^ (11871158 + 11871158) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 11871158 * (2 : ZMod 3987189707861) ^ 11871158 := by rw [pow_add]
          _ = 3847407239026 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 3987189707861) ^ 47484633 = 1044428685931 := by
        calc
          (2 : ZMod 3987189707861) ^ 47484633 = (2 : ZMod 3987189707861) ^ (23742316 + 23742316 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 23742316 * (2 : ZMod 3987189707861) ^ 23742316) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1044428685931 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 3987189707861) ^ 94969267 = 1615701084709 := by
        calc
          (2 : ZMod 3987189707861) ^ 94969267 = (2 : ZMod 3987189707861) ^ (47484633 + 47484633 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 47484633 * (2 : ZMod 3987189707861) ^ 47484633) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1615701084709 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 3987189707861) ^ 189938534 = 1135526364971 := by
        calc
          (2 : ZMod 3987189707861) ^ 189938534 = (2 : ZMod 3987189707861) ^ (94969267 + 94969267) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 94969267 * (2 : ZMod 3987189707861) ^ 94969267 := by rw [pow_add]
          _ = 1135526364971 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 3987189707861) ^ 379877068 = 2622074424176 := by
        calc
          (2 : ZMod 3987189707861) ^ 379877068 = (2 : ZMod 3987189707861) ^ (189938534 + 189938534) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 189938534 * (2 : ZMod 3987189707861) ^ 189938534 := by rw [pow_add]
          _ = 2622074424176 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 3987189707861) ^ 759754136 = 3175358600131 := by
        calc
          (2 : ZMod 3987189707861) ^ 759754136 = (2 : ZMod 3987189707861) ^ (379877068 + 379877068) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 379877068 * (2 : ZMod 3987189707861) ^ 379877068 := by rw [pow_add]
          _ = 3175358600131 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 3987189707861) ^ 1519508272 = 1253641362398 := by
        calc
          (2 : ZMod 3987189707861) ^ 1519508272 = (2 : ZMod 3987189707861) ^ (759754136 + 759754136) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 759754136 * (2 : ZMod 3987189707861) ^ 759754136 := by rw [pow_add]
          _ = 1253641362398 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 3987189707861) ^ 3039016545 = 3010577845097 := by
        calc
          (2 : ZMod 3987189707861) ^ 3039016545 = (2 : ZMod 3987189707861) ^ (1519508272 + 1519508272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1519508272 * (2 : ZMod 3987189707861) ^ 1519508272) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3010577845097 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 3987189707861) ^ 6078033091 = 357957961818 := by
        calc
          (2 : ZMod 3987189707861) ^ 6078033091 = (2 : ZMod 3987189707861) ^ (3039016545 + 3039016545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 3039016545 * (2 : ZMod 3987189707861) ^ 3039016545) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 357957961818 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 3987189707861) ^ 12156066182 = 2040954072486 := by
        calc
          (2 : ZMod 3987189707861) ^ 12156066182 = (2 : ZMod 3987189707861) ^ (6078033091 + 6078033091) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 6078033091 * (2 : ZMod 3987189707861) ^ 6078033091 := by rw [pow_add]
          _ = 2040954072486 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 3987189707861) ^ 24312132365 = 415745843102 := by
        calc
          (2 : ZMod 3987189707861) ^ 24312132365 = (2 : ZMod 3987189707861) ^ (12156066182 + 12156066182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 12156066182 * (2 : ZMod 3987189707861) ^ 12156066182) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 415745843102 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 3987189707861) ^ 48624264730 = 3043484619404 := by
        calc
          (2 : ZMod 3987189707861) ^ 48624264730 = (2 : ZMod 3987189707861) ^ (24312132365 + 24312132365) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 24312132365 * (2 : ZMod 3987189707861) ^ 24312132365 := by rw [pow_add]
          _ = 3043484619404 := by rw [factor_2_34]; decide
      have factor_2_36 : (2 : ZMod 3987189707861) ^ 97248529460 = 2184157066759 := by
        calc
          (2 : ZMod 3987189707861) ^ 97248529460 = (2 : ZMod 3987189707861) ^ (48624264730 + 48624264730) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 48624264730 * (2 : ZMod 3987189707861) ^ 48624264730 := by rw [pow_add]
          _ = 2184157066759 := by rw [factor_2_35]; decide
      change (2 : ZMod 3987189707861) ^ 97248529460 ≠ 1
      rw [factor_2_36]
      decide
    ·
      have factor_3_0 : (2 : ZMod 3987189707861) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 3987189707861) ^ 2 = 4 := by
        calc
          (2 : ZMod 3987189707861) ^ 2 = (2 : ZMod 3987189707861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1 * (2 : ZMod 3987189707861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 3987189707861) ^ 5 = 32 := by
        calc
          (2 : ZMod 3987189707861) ^ 5 = (2 : ZMod 3987189707861) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 2 * (2 : ZMod 3987189707861) ^ 2) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 3987189707861) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3987189707861) ^ 11 = (2 : ZMod 3987189707861) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 5 * (2 : ZMod 3987189707861) ^ 5) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 3987189707861) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 3987189707861) ^ 22 = (2 : ZMod 3987189707861) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 11 * (2 : ZMod 3987189707861) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 3987189707861) ^ 44 = 1643427212972 := by
        calc
          (2 : ZMod 3987189707861) ^ 44 = (2 : ZMod 3987189707861) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 22 * (2 : ZMod 3987189707861) ^ 22 := by rw [pow_add]
          _ = 1643427212972 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 3987189707861) ^ 89 = 795438986544 := by
        calc
          (2 : ZMod 3987189707861) ^ 89 = (2 : ZMod 3987189707861) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 44 * (2 : ZMod 3987189707861) ^ 44) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 795438986544 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 3987189707861) ^ 178 = 3856327604849 := by
        calc
          (2 : ZMod 3987189707861) ^ 178 = (2 : ZMod 3987189707861) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 89 * (2 : ZMod 3987189707861) ^ 89 := by rw [pow_add]
          _ = 3856327604849 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 3987189707861) ^ 357 = 1945051003728 := by
        calc
          (2 : ZMod 3987189707861) ^ 357 = (2 : ZMod 3987189707861) ^ (178 + 178 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 178 * (2 : ZMod 3987189707861) ^ 178) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1945051003728 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 3987189707861) ^ 714 = 3188189190972 := by
        calc
          (2 : ZMod 3987189707861) ^ 714 = (2 : ZMod 3987189707861) ^ (357 + 357) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 357 * (2 : ZMod 3987189707861) ^ 357 := by rw [pow_add]
          _ = 3188189190972 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 3987189707861) ^ 1428 = 2910030425189 := by
        calc
          (2 : ZMod 3987189707861) ^ 1428 = (2 : ZMod 3987189707861) ^ (714 + 714) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 714 * (2 : ZMod 3987189707861) ^ 714 := by rw [pow_add]
          _ = 2910030425189 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 3987189707861) ^ 2856 = 2636650337278 := by
        calc
          (2 : ZMod 3987189707861) ^ 2856 = (2 : ZMod 3987189707861) ^ (1428 + 1428) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1428 * (2 : ZMod 3987189707861) ^ 1428 := by rw [pow_add]
          _ = 2636650337278 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 3987189707861) ^ 5712 = 2814086930060 := by
        calc
          (2 : ZMod 3987189707861) ^ 5712 = (2 : ZMod 3987189707861) ^ (2856 + 2856) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 2856 * (2 : ZMod 3987189707861) ^ 2856 := by rw [pow_add]
          _ = 2814086930060 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 3987189707861) ^ 11424 = 2911097096285 := by
        calc
          (2 : ZMod 3987189707861) ^ 11424 = (2 : ZMod 3987189707861) ^ (5712 + 5712) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 5712 * (2 : ZMod 3987189707861) ^ 5712 := by rw [pow_add]
          _ = 2911097096285 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 3987189707861) ^ 22848 = 1004614039834 := by
        calc
          (2 : ZMod 3987189707861) ^ 22848 = (2 : ZMod 3987189707861) ^ (11424 + 11424) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 11424 * (2 : ZMod 3987189707861) ^ 11424 := by rw [pow_add]
          _ = 1004614039834 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 3987189707861) ^ 45696 = 3565170075846 := by
        calc
          (2 : ZMod 3987189707861) ^ 45696 = (2 : ZMod 3987189707861) ^ (22848 + 22848) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 22848 * (2 : ZMod 3987189707861) ^ 22848 := by rw [pow_add]
          _ = 3565170075846 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 3987189707861) ^ 91393 = 2324220540030 := by
        calc
          (2 : ZMod 3987189707861) ^ 91393 = (2 : ZMod 3987189707861) ^ (45696 + 45696 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 45696 * (2 : ZMod 3987189707861) ^ 45696) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2324220540030 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 3987189707861) ^ 182787 = 455491638706 := by
        calc
          (2 : ZMod 3987189707861) ^ 182787 = (2 : ZMod 3987189707861) ^ (91393 + 91393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 91393 * (2 : ZMod 3987189707861) ^ 91393) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 455491638706 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 3987189707861) ^ 365575 = 2384808823370 := by
        calc
          (2 : ZMod 3987189707861) ^ 365575 = (2 : ZMod 3987189707861) ^ (182787 + 182787 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 182787 * (2 : ZMod 3987189707861) ^ 182787) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2384808823370 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 3987189707861) ^ 731150 = 1989477569424 := by
        calc
          (2 : ZMod 3987189707861) ^ 731150 = (2 : ZMod 3987189707861) ^ (365575 + 365575) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 365575 * (2 : ZMod 3987189707861) ^ 365575 := by rw [pow_add]
          _ = 1989477569424 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 3987189707861) ^ 1462300 = 3243362413174 := by
        calc
          (2 : ZMod 3987189707861) ^ 1462300 = (2 : ZMod 3987189707861) ^ (731150 + 731150) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 731150 * (2 : ZMod 3987189707861) ^ 731150 := by rw [pow_add]
          _ = 3243362413174 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 3987189707861) ^ 2924600 = 1573963963241 := by
        calc
          (2 : ZMod 3987189707861) ^ 2924600 = (2 : ZMod 3987189707861) ^ (1462300 + 1462300) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1462300 * (2 : ZMod 3987189707861) ^ 1462300 := by rw [pow_add]
          _ = 1573963963241 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 3987189707861) ^ 5849200 = 1923338436435 := by
        calc
          (2 : ZMod 3987189707861) ^ 5849200 = (2 : ZMod 3987189707861) ^ (2924600 + 2924600) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 2924600 * (2 : ZMod 3987189707861) ^ 2924600 := by rw [pow_add]
          _ = 1923338436435 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 3987189707861) ^ 11698401 = 775338525764 := by
        calc
          (2 : ZMod 3987189707861) ^ 11698401 = (2 : ZMod 3987189707861) ^ (5849200 + 5849200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 5849200 * (2 : ZMod 3987189707861) ^ 5849200) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 775338525764 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 3987189707861) ^ 23396803 = 1793022918545 := by
        calc
          (2 : ZMod 3987189707861) ^ 23396803 = (2 : ZMod 3987189707861) ^ (11698401 + 11698401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 11698401 * (2 : ZMod 3987189707861) ^ 11698401) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1793022918545 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 3987189707861) ^ 46793607 = 1185012137614 := by
        calc
          (2 : ZMod 3987189707861) ^ 46793607 = (2 : ZMod 3987189707861) ^ (23396803 + 23396803 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 23396803 * (2 : ZMod 3987189707861) ^ 23396803) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1185012137614 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 3987189707861) ^ 93587215 = 1094978925020 := by
        calc
          (2 : ZMod 3987189707861) ^ 93587215 = (2 : ZMod 3987189707861) ^ (46793607 + 46793607 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 46793607 * (2 : ZMod 3987189707861) ^ 46793607) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1094978925020 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 3987189707861) ^ 187174430 = 1081895835049 := by
        calc
          (2 : ZMod 3987189707861) ^ 187174430 = (2 : ZMod 3987189707861) ^ (93587215 + 93587215) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 93587215 * (2 : ZMod 3987189707861) ^ 93587215 := by rw [pow_add]
          _ = 1081895835049 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 3987189707861) ^ 374348860 = 2705945431676 := by
        calc
          (2 : ZMod 3987189707861) ^ 374348860 = (2 : ZMod 3987189707861) ^ (187174430 + 187174430) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 187174430 * (2 : ZMod 3987189707861) ^ 187174430 := by rw [pow_add]
          _ = 2705945431676 := by rw [factor_3_27]; decide
      change (2 : ZMod 3987189707861) ^ 374348860 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (2 : ZMod 3987189707861) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 3987189707861) ^ 2 = 4 := by
        calc
          (2 : ZMod 3987189707861) ^ 2 = (2 : ZMod 3987189707861) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1 * (2 : ZMod 3987189707861) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 3987189707861) ^ 4 = 16 := by
        calc
          (2 : ZMod 3987189707861) ^ 4 = (2 : ZMod 3987189707861) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 2 * (2 : ZMod 3987189707861) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 3987189707861) ^ 8 = 256 := by
        calc
          (2 : ZMod 3987189707861) ^ 8 = (2 : ZMod 3987189707861) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 4 * (2 : ZMod 3987189707861) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 3987189707861) ^ 16 = 65536 := by
        calc
          (2 : ZMod 3987189707861) ^ 16 = (2 : ZMod 3987189707861) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 8 * (2 : ZMod 3987189707861) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 3987189707861) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 3987189707861) ^ 33 = (2 : ZMod 3987189707861) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 16 * (2 : ZMod 3987189707861) ^ 16) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 3987189707861) ^ 66 = 3689265461854 := by
        calc
          (2 : ZMod 3987189707861) ^ 66 = (2 : ZMod 3987189707861) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 33 * (2 : ZMod 3987189707861) ^ 33 := by rw [pow_add]
          _ = 3689265461854 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 3987189707861) ^ 133 = 1105498695840 := by
        calc
          (2 : ZMod 3987189707861) ^ 133 = (2 : ZMod 3987189707861) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 66 * (2 : ZMod 3987189707861) ^ 66) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1105498695840 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 3987189707861) ^ 266 = 2862541829590 := by
        calc
          (2 : ZMod 3987189707861) ^ 266 = (2 : ZMod 3987189707861) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 133 * (2 : ZMod 3987189707861) ^ 133 := by rw [pow_add]
          _ = 2862541829590 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 3987189707861) ^ 533 = 3058866464581 := by
        calc
          (2 : ZMod 3987189707861) ^ 533 = (2 : ZMod 3987189707861) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 266 * (2 : ZMod 3987189707861) ^ 266) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3058866464581 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 3987189707861) ^ 1066 = 2763662233556 := by
        calc
          (2 : ZMod 3987189707861) ^ 1066 = (2 : ZMod 3987189707861) ^ (533 + 533) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 533 * (2 : ZMod 3987189707861) ^ 533 := by rw [pow_add]
          _ = 2763662233556 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 3987189707861) ^ 2132 = 3705228829888 := by
        calc
          (2 : ZMod 3987189707861) ^ 2132 = (2 : ZMod 3987189707861) ^ (1066 + 1066) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 1066 * (2 : ZMod 3987189707861) ^ 1066 := by rw [pow_add]
          _ = 3705228829888 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 3987189707861) ^ 4264 = 3352375955576 := by
        calc
          (2 : ZMod 3987189707861) ^ 4264 = (2 : ZMod 3987189707861) ^ (2132 + 2132) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 2132 * (2 : ZMod 3987189707861) ^ 2132 := by rw [pow_add]
          _ = 3352375955576 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 3987189707861) ^ 8529 = 977561333073 := by
        calc
          (2 : ZMod 3987189707861) ^ 8529 = (2 : ZMod 3987189707861) ^ (4264 + 4264 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 4264 * (2 : ZMod 3987189707861) ^ 4264) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 977561333073 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 3987189707861) ^ 17058 = 3817514682116 := by
        calc
          (2 : ZMod 3987189707861) ^ 17058 = (2 : ZMod 3987189707861) ^ (8529 + 8529) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 8529 * (2 : ZMod 3987189707861) ^ 8529 := by rw [pow_add]
          _ = 3817514682116 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 3987189707861) ^ 34116 = 825180713287 := by
        calc
          (2 : ZMod 3987189707861) ^ 34116 = (2 : ZMod 3987189707861) ^ (17058 + 17058) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 17058 * (2 : ZMod 3987189707861) ^ 17058 := by rw [pow_add]
          _ = 825180713287 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 3987189707861) ^ 68232 = 23023490819 := by
        calc
          (2 : ZMod 3987189707861) ^ 68232 = (2 : ZMod 3987189707861) ^ (34116 + 34116) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 34116 * (2 : ZMod 3987189707861) ^ 34116 := by rw [pow_add]
          _ = 23023490819 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 3987189707861) ^ 136465 = 2502037659839 := by
        calc
          (2 : ZMod 3987189707861) ^ 136465 = (2 : ZMod 3987189707861) ^ (68232 + 68232 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 68232 * (2 : ZMod 3987189707861) ^ 68232) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 2502037659839 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 3987189707861) ^ 272931 = 1191018098152 := by
        calc
          (2 : ZMod 3987189707861) ^ 272931 = (2 : ZMod 3987189707861) ^ (136465 + 136465 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 136465 * (2 : ZMod 3987189707861) ^ 136465) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1191018098152 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 3987189707861) ^ 545863 = 3324941370874 := by
        calc
          (2 : ZMod 3987189707861) ^ 545863 = (2 : ZMod 3987189707861) ^ (272931 + 272931 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 272931 * (2 : ZMod 3987189707861) ^ 272931) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 3324941370874 := by rw [factor_4_18]; decide
      have factor_4_20 : (2 : ZMod 3987189707861) ^ 1091727 = 73950417678 := by
        calc
          (2 : ZMod 3987189707861) ^ 1091727 = (2 : ZMod 3987189707861) ^ (545863 + 545863 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 545863 * (2 : ZMod 3987189707861) ^ 545863) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 73950417678 := by rw [factor_4_19]; decide
      have factor_4_21 : (2 : ZMod 3987189707861) ^ 2183455 = 1820516749998 := by
        calc
          (2 : ZMod 3987189707861) ^ 2183455 = (2 : ZMod 3987189707861) ^ (1091727 + 1091727 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = ((2 : ZMod 3987189707861) ^ 1091727 * (2 : ZMod 3987189707861) ^ 1091727) * (2 : ZMod 3987189707861) := by rw [pow_succ, pow_add]
          _ = 1820516749998 := by rw [factor_4_20]; decide
      have factor_4_22 : (2 : ZMod 3987189707861) ^ 4366910 = 344301554165 := by
        calc
          (2 : ZMod 3987189707861) ^ 4366910 = (2 : ZMod 3987189707861) ^ (2183455 + 2183455) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 2183455 * (2 : ZMod 3987189707861) ^ 2183455 := by rw [pow_add]
          _ = 344301554165 := by rw [factor_4_21]; decide
      have factor_4_23 : (2 : ZMod 3987189707861) ^ 8733820 = 3037310289457 := by
        calc
          (2 : ZMod 3987189707861) ^ 8733820 = (2 : ZMod 3987189707861) ^ (4366910 + 4366910) :=
            congrArg (fun n : ℕ => (2 : ZMod 3987189707861) ^ n) (by norm_num)
          _ = (2 : ZMod 3987189707861) ^ 4366910 * (2 : ZMod 3987189707861) ^ 4366910 := by rw [pow_add]
          _ = 3037310289457 := by rw [factor_4_22]; decide
      change (2 : ZMod 3987189707861) ^ 8733820 ≠ 1
      rw [factor_4_23]
      decide

#print axioms prime_lucas_3987189707861

end TotientTailPeriodKiller
end Erdos249257
