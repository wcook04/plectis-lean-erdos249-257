import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1155228423149 : Nat.Prime 1155228423149 := by
  apply lucas_primality 1155228423149 (2 : ZMod 1155228423149)
  ·
      have fermat_0 : (2 : ZMod 1155228423149) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1155228423149) ^ 2 = 4 := by
        calc
          (2 : ZMod 1155228423149) ^ 2 = (2 : ZMod 1155228423149) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 1 * (2 : ZMod 1155228423149) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1155228423149) ^ 4 = 16 := by
        calc
          (2 : ZMod 1155228423149) ^ 4 = (2 : ZMod 1155228423149) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 2 * (2 : ZMod 1155228423149) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1155228423149) ^ 8 = 256 := by
        calc
          (2 : ZMod 1155228423149) ^ 8 = (2 : ZMod 1155228423149) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 4 * (2 : ZMod 1155228423149) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1155228423149) ^ 16 = 65536 := by
        calc
          (2 : ZMod 1155228423149) ^ 16 = (2 : ZMod 1155228423149) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8 * (2 : ZMod 1155228423149) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1155228423149) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 1155228423149) ^ 33 = (2 : ZMod 1155228423149) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 16 * (2 : ZMod 1155228423149) ^ 16) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1155228423149) ^ 67 = 53388682520 := by
        calc
          (2 : ZMod 1155228423149) ^ 67 = (2 : ZMod 1155228423149) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 33 * (2 : ZMod 1155228423149) ^ 33) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 53388682520 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1155228423149) ^ 134 = 382227835713 := by
        calc
          (2 : ZMod 1155228423149) ^ 134 = (2 : ZMod 1155228423149) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 67 * (2 : ZMod 1155228423149) ^ 67 := by rw [pow_add]
          _ = 382227835713 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1155228423149) ^ 268 = 748034710145 := by
        calc
          (2 : ZMod 1155228423149) ^ 268 = (2 : ZMod 1155228423149) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 134 * (2 : ZMod 1155228423149) ^ 134 := by rw [pow_add]
          _ = 748034710145 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1155228423149) ^ 537 = 731831363382 := by
        calc
          (2 : ZMod 1155228423149) ^ 537 = (2 : ZMod 1155228423149) ^ (268 + 268 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 268 * (2 : ZMod 1155228423149) ^ 268) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 731831363382 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1155228423149) ^ 1075 = 1005478041032 := by
        calc
          (2 : ZMod 1155228423149) ^ 1075 = (2 : ZMod 1155228423149) ^ (537 + 537 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 537 * (2 : ZMod 1155228423149) ^ 537) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1005478041032 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1155228423149) ^ 2151 = 58505659564 := by
        calc
          (2 : ZMod 1155228423149) ^ 2151 = (2 : ZMod 1155228423149) ^ (1075 + 1075 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1075 * (2 : ZMod 1155228423149) ^ 1075) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 58505659564 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1155228423149) ^ 4303 = 793752305167 := by
        calc
          (2 : ZMod 1155228423149) ^ 4303 = (2 : ZMod 1155228423149) ^ (2151 + 2151 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2151 * (2 : ZMod 1155228423149) ^ 2151) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 793752305167 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1155228423149) ^ 8607 = 149453261029 := by
        calc
          (2 : ZMod 1155228423149) ^ 8607 = (2 : ZMod 1155228423149) ^ (4303 + 4303 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 4303 * (2 : ZMod 1155228423149) ^ 4303) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 149453261029 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1155228423149) ^ 17214 = 666466614055 := by
        calc
          (2 : ZMod 1155228423149) ^ 17214 = (2 : ZMod 1155228423149) ^ (8607 + 8607) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8607 * (2 : ZMod 1155228423149) ^ 8607 := by rw [pow_add]
          _ = 666466614055 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1155228423149) ^ 34428 = 511013347092 := by
        calc
          (2 : ZMod 1155228423149) ^ 34428 = (2 : ZMod 1155228423149) ^ (17214 + 17214) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 17214 * (2 : ZMod 1155228423149) ^ 17214 := by rw [pow_add]
          _ = 511013347092 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1155228423149) ^ 68856 = 1022050276039 := by
        calc
          (2 : ZMod 1155228423149) ^ 68856 = (2 : ZMod 1155228423149) ^ (34428 + 34428) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 34428 * (2 : ZMod 1155228423149) ^ 34428 := by rw [pow_add]
          _ = 1022050276039 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1155228423149) ^ 137713 = 621637289762 := by
        calc
          (2 : ZMod 1155228423149) ^ 137713 = (2 : ZMod 1155228423149) ^ (68856 + 68856 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 68856 * (2 : ZMod 1155228423149) ^ 68856) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 621637289762 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1155228423149) ^ 275427 = 1146268421526 := by
        calc
          (2 : ZMod 1155228423149) ^ 275427 = (2 : ZMod 1155228423149) ^ (137713 + 137713 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 137713 * (2 : ZMod 1155228423149) ^ 137713) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1146268421526 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1155228423149) ^ 550855 = 418596648578 := by
        calc
          (2 : ZMod 1155228423149) ^ 550855 = (2 : ZMod 1155228423149) ^ (275427 + 275427 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 275427 * (2 : ZMod 1155228423149) ^ 275427) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 418596648578 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1155228423149) ^ 1101711 = 115774562805 := by
        calc
          (2 : ZMod 1155228423149) ^ 1101711 = (2 : ZMod 1155228423149) ^ (550855 + 550855 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 550855 * (2 : ZMod 1155228423149) ^ 550855) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 115774562805 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1155228423149) ^ 2203423 = 185814337857 := by
        calc
          (2 : ZMod 1155228423149) ^ 2203423 = (2 : ZMod 1155228423149) ^ (1101711 + 1101711 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1101711 * (2 : ZMod 1155228423149) ^ 1101711) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 185814337857 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1155228423149) ^ 4406846 = 331958906486 := by
        calc
          (2 : ZMod 1155228423149) ^ 4406846 = (2 : ZMod 1155228423149) ^ (2203423 + 2203423) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 2203423 * (2 : ZMod 1155228423149) ^ 2203423 := by rw [pow_add]
          _ = 331958906486 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1155228423149) ^ 8813693 = 1003586392050 := by
        calc
          (2 : ZMod 1155228423149) ^ 8813693 = (2 : ZMod 1155228423149) ^ (4406846 + 4406846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 4406846 * (2 : ZMod 1155228423149) ^ 4406846) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1003586392050 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1155228423149) ^ 17627386 = 281054883621 := by
        calc
          (2 : ZMod 1155228423149) ^ 17627386 = (2 : ZMod 1155228423149) ^ (8813693 + 8813693) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8813693 * (2 : ZMod 1155228423149) ^ 8813693 := by rw [pow_add]
          _ = 281054883621 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1155228423149) ^ 35254773 = 1076260407912 := by
        calc
          (2 : ZMod 1155228423149) ^ 35254773 = (2 : ZMod 1155228423149) ^ (17627386 + 17627386 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 17627386 * (2 : ZMod 1155228423149) ^ 17627386) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1076260407912 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1155228423149) ^ 70509547 = 845559979684 := by
        calc
          (2 : ZMod 1155228423149) ^ 70509547 = (2 : ZMod 1155228423149) ^ (35254773 + 35254773 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 35254773 * (2 : ZMod 1155228423149) ^ 35254773) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 845559979684 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1155228423149) ^ 141019094 = 73780932820 := by
        calc
          (2 : ZMod 1155228423149) ^ 141019094 = (2 : ZMod 1155228423149) ^ (70509547 + 70509547) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 70509547 * (2 : ZMod 1155228423149) ^ 70509547 := by rw [pow_add]
          _ = 73780932820 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1155228423149) ^ 282038189 = 1046947015750 := by
        calc
          (2 : ZMod 1155228423149) ^ 282038189 = (2 : ZMod 1155228423149) ^ (141019094 + 141019094 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 141019094 * (2 : ZMod 1155228423149) ^ 141019094) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1046947015750 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1155228423149) ^ 564076378 = 731189219916 := by
        calc
          (2 : ZMod 1155228423149) ^ 564076378 = (2 : ZMod 1155228423149) ^ (282038189 + 282038189) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 282038189 * (2 : ZMod 1155228423149) ^ 282038189 := by rw [pow_add]
          _ = 731189219916 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1155228423149) ^ 1128152756 = 330248912563 := by
        calc
          (2 : ZMod 1155228423149) ^ 1128152756 = (2 : ZMod 1155228423149) ^ (564076378 + 564076378) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 564076378 * (2 : ZMod 1155228423149) ^ 564076378 := by rw [pow_add]
          _ = 330248912563 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 1155228423149) ^ 2256305513 = 734802611924 := by
        calc
          (2 : ZMod 1155228423149) ^ 2256305513 = (2 : ZMod 1155228423149) ^ (1128152756 + 1128152756 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1128152756 * (2 : ZMod 1155228423149) ^ 1128152756) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 734802611924 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 1155228423149) ^ 4512611027 = 685707153940 := by
        calc
          (2 : ZMod 1155228423149) ^ 4512611027 = (2 : ZMod 1155228423149) ^ (2256305513 + 2256305513 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2256305513 * (2 : ZMod 1155228423149) ^ 2256305513) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 685707153940 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 1155228423149) ^ 9025222055 = 747099792463 := by
        calc
          (2 : ZMod 1155228423149) ^ 9025222055 = (2 : ZMod 1155228423149) ^ (4512611027 + 4512611027 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 4512611027 * (2 : ZMod 1155228423149) ^ 4512611027) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 747099792463 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 1155228423149) ^ 18050444111 = 930176895234 := by
        calc
          (2 : ZMod 1155228423149) ^ 18050444111 = (2 : ZMod 1155228423149) ^ (9025222055 + 9025222055 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 9025222055 * (2 : ZMod 1155228423149) ^ 9025222055) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 930176895234 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 1155228423149) ^ 36100888223 = 702021734930 := by
        calc
          (2 : ZMod 1155228423149) ^ 36100888223 = (2 : ZMod 1155228423149) ^ (18050444111 + 18050444111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 18050444111 * (2 : ZMod 1155228423149) ^ 18050444111) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 702021734930 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 1155228423149) ^ 72201776446 = 37239342074 := by
        calc
          (2 : ZMod 1155228423149) ^ 72201776446 = (2 : ZMod 1155228423149) ^ (36100888223 + 36100888223) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 36100888223 * (2 : ZMod 1155228423149) ^ 36100888223 := by rw [pow_add]
          _ = 37239342074 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 1155228423149) ^ 144403552893 = 1150399615542 := by
        calc
          (2 : ZMod 1155228423149) ^ 144403552893 = (2 : ZMod 1155228423149) ^ (72201776446 + 72201776446 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 72201776446 * (2 : ZMod 1155228423149) ^ 72201776446) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1150399615542 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 1155228423149) ^ 288807105787 = 1145570807934 := by
        calc
          (2 : ZMod 1155228423149) ^ 288807105787 = (2 : ZMod 1155228423149) ^ (144403552893 + 144403552893 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 144403552893 * (2 : ZMod 1155228423149) ^ 144403552893) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1145570807934 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 1155228423149) ^ 577614211574 = 1155228423148 := by
        calc
          (2 : ZMod 1155228423149) ^ 577614211574 = (2 : ZMod 1155228423149) ^ (288807105787 + 288807105787) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 288807105787 * (2 : ZMod 1155228423149) ^ 288807105787 := by rw [pow_add]
          _ = 1155228423148 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 1155228423149) ^ 1155228423148 = 1 := by
        calc
          (2 : ZMod 1155228423149) ^ 1155228423148 = (2 : ZMod 1155228423149) ^ (577614211574 + 577614211574) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 577614211574 * (2 : ZMod 1155228423149) ^ 577614211574 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (409, 1), (4253, 1), (166031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (409, 1), (4253, 1), (166031, 1)] : List FactorBlock).map factorBlockValue).prod = 1155228423149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1155228423149) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1155228423149) ^ 2 = 4 := by
        calc
          (2 : ZMod 1155228423149) ^ 2 = (2 : ZMod 1155228423149) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 1 * (2 : ZMod 1155228423149) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1155228423149) ^ 4 = 16 := by
        calc
          (2 : ZMod 1155228423149) ^ 4 = (2 : ZMod 1155228423149) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 2 * (2 : ZMod 1155228423149) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1155228423149) ^ 8 = 256 := by
        calc
          (2 : ZMod 1155228423149) ^ 8 = (2 : ZMod 1155228423149) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 4 * (2 : ZMod 1155228423149) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1155228423149) ^ 16 = 65536 := by
        calc
          (2 : ZMod 1155228423149) ^ 16 = (2 : ZMod 1155228423149) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8 * (2 : ZMod 1155228423149) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1155228423149) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 1155228423149) ^ 33 = (2 : ZMod 1155228423149) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 16 * (2 : ZMod 1155228423149) ^ 16) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1155228423149) ^ 67 = 53388682520 := by
        calc
          (2 : ZMod 1155228423149) ^ 67 = (2 : ZMod 1155228423149) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 33 * (2 : ZMod 1155228423149) ^ 33) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 53388682520 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1155228423149) ^ 134 = 382227835713 := by
        calc
          (2 : ZMod 1155228423149) ^ 134 = (2 : ZMod 1155228423149) ^ (67 + 67) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 67 * (2 : ZMod 1155228423149) ^ 67 := by rw [pow_add]
          _ = 382227835713 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1155228423149) ^ 268 = 748034710145 := by
        calc
          (2 : ZMod 1155228423149) ^ 268 = (2 : ZMod 1155228423149) ^ (134 + 134) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 134 * (2 : ZMod 1155228423149) ^ 134 := by rw [pow_add]
          _ = 748034710145 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1155228423149) ^ 537 = 731831363382 := by
        calc
          (2 : ZMod 1155228423149) ^ 537 = (2 : ZMod 1155228423149) ^ (268 + 268 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 268 * (2 : ZMod 1155228423149) ^ 268) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 731831363382 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1155228423149) ^ 1075 = 1005478041032 := by
        calc
          (2 : ZMod 1155228423149) ^ 1075 = (2 : ZMod 1155228423149) ^ (537 + 537 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 537 * (2 : ZMod 1155228423149) ^ 537) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1005478041032 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1155228423149) ^ 2151 = 58505659564 := by
        calc
          (2 : ZMod 1155228423149) ^ 2151 = (2 : ZMod 1155228423149) ^ (1075 + 1075 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1075 * (2 : ZMod 1155228423149) ^ 1075) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 58505659564 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1155228423149) ^ 4303 = 793752305167 := by
        calc
          (2 : ZMod 1155228423149) ^ 4303 = (2 : ZMod 1155228423149) ^ (2151 + 2151 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2151 * (2 : ZMod 1155228423149) ^ 2151) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 793752305167 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1155228423149) ^ 8607 = 149453261029 := by
        calc
          (2 : ZMod 1155228423149) ^ 8607 = (2 : ZMod 1155228423149) ^ (4303 + 4303 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 4303 * (2 : ZMod 1155228423149) ^ 4303) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 149453261029 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1155228423149) ^ 17214 = 666466614055 := by
        calc
          (2 : ZMod 1155228423149) ^ 17214 = (2 : ZMod 1155228423149) ^ (8607 + 8607) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8607 * (2 : ZMod 1155228423149) ^ 8607 := by rw [pow_add]
          _ = 666466614055 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1155228423149) ^ 34428 = 511013347092 := by
        calc
          (2 : ZMod 1155228423149) ^ 34428 = (2 : ZMod 1155228423149) ^ (17214 + 17214) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 17214 * (2 : ZMod 1155228423149) ^ 17214 := by rw [pow_add]
          _ = 511013347092 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1155228423149) ^ 68856 = 1022050276039 := by
        calc
          (2 : ZMod 1155228423149) ^ 68856 = (2 : ZMod 1155228423149) ^ (34428 + 34428) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 34428 * (2 : ZMod 1155228423149) ^ 34428 := by rw [pow_add]
          _ = 1022050276039 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1155228423149) ^ 137713 = 621637289762 := by
        calc
          (2 : ZMod 1155228423149) ^ 137713 = (2 : ZMod 1155228423149) ^ (68856 + 68856 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 68856 * (2 : ZMod 1155228423149) ^ 68856) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 621637289762 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1155228423149) ^ 275427 = 1146268421526 := by
        calc
          (2 : ZMod 1155228423149) ^ 275427 = (2 : ZMod 1155228423149) ^ (137713 + 137713 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 137713 * (2 : ZMod 1155228423149) ^ 137713) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1146268421526 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1155228423149) ^ 550855 = 418596648578 := by
        calc
          (2 : ZMod 1155228423149) ^ 550855 = (2 : ZMod 1155228423149) ^ (275427 + 275427 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 275427 * (2 : ZMod 1155228423149) ^ 275427) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 418596648578 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1155228423149) ^ 1101711 = 115774562805 := by
        calc
          (2 : ZMod 1155228423149) ^ 1101711 = (2 : ZMod 1155228423149) ^ (550855 + 550855 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 550855 * (2 : ZMod 1155228423149) ^ 550855) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 115774562805 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1155228423149) ^ 2203423 = 185814337857 := by
        calc
          (2 : ZMod 1155228423149) ^ 2203423 = (2 : ZMod 1155228423149) ^ (1101711 + 1101711 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1101711 * (2 : ZMod 1155228423149) ^ 1101711) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 185814337857 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1155228423149) ^ 4406846 = 331958906486 := by
        calc
          (2 : ZMod 1155228423149) ^ 4406846 = (2 : ZMod 1155228423149) ^ (2203423 + 2203423) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 2203423 * (2 : ZMod 1155228423149) ^ 2203423 := by rw [pow_add]
          _ = 331958906486 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1155228423149) ^ 8813693 = 1003586392050 := by
        calc
          (2 : ZMod 1155228423149) ^ 8813693 = (2 : ZMod 1155228423149) ^ (4406846 + 4406846 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 4406846 * (2 : ZMod 1155228423149) ^ 4406846) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1003586392050 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1155228423149) ^ 17627386 = 281054883621 := by
        calc
          (2 : ZMod 1155228423149) ^ 17627386 = (2 : ZMod 1155228423149) ^ (8813693 + 8813693) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8813693 * (2 : ZMod 1155228423149) ^ 8813693 := by rw [pow_add]
          _ = 281054883621 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1155228423149) ^ 35254773 = 1076260407912 := by
        calc
          (2 : ZMod 1155228423149) ^ 35254773 = (2 : ZMod 1155228423149) ^ (17627386 + 17627386 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 17627386 * (2 : ZMod 1155228423149) ^ 17627386) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1076260407912 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1155228423149) ^ 70509547 = 845559979684 := by
        calc
          (2 : ZMod 1155228423149) ^ 70509547 = (2 : ZMod 1155228423149) ^ (35254773 + 35254773 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 35254773 * (2 : ZMod 1155228423149) ^ 35254773) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 845559979684 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1155228423149) ^ 141019094 = 73780932820 := by
        calc
          (2 : ZMod 1155228423149) ^ 141019094 = (2 : ZMod 1155228423149) ^ (70509547 + 70509547) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 70509547 * (2 : ZMod 1155228423149) ^ 70509547 := by rw [pow_add]
          _ = 73780932820 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1155228423149) ^ 282038189 = 1046947015750 := by
        calc
          (2 : ZMod 1155228423149) ^ 282038189 = (2 : ZMod 1155228423149) ^ (141019094 + 141019094 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 141019094 * (2 : ZMod 1155228423149) ^ 141019094) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1046947015750 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1155228423149) ^ 564076378 = 731189219916 := by
        calc
          (2 : ZMod 1155228423149) ^ 564076378 = (2 : ZMod 1155228423149) ^ (282038189 + 282038189) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 282038189 * (2 : ZMod 1155228423149) ^ 282038189 := by rw [pow_add]
          _ = 731189219916 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 1155228423149) ^ 1128152756 = 330248912563 := by
        calc
          (2 : ZMod 1155228423149) ^ 1128152756 = (2 : ZMod 1155228423149) ^ (564076378 + 564076378) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 564076378 * (2 : ZMod 1155228423149) ^ 564076378 := by rw [pow_add]
          _ = 330248912563 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 1155228423149) ^ 2256305513 = 734802611924 := by
        calc
          (2 : ZMod 1155228423149) ^ 2256305513 = (2 : ZMod 1155228423149) ^ (1128152756 + 1128152756 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1128152756 * (2 : ZMod 1155228423149) ^ 1128152756) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 734802611924 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 1155228423149) ^ 4512611027 = 685707153940 := by
        calc
          (2 : ZMod 1155228423149) ^ 4512611027 = (2 : ZMod 1155228423149) ^ (2256305513 + 2256305513 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2256305513 * (2 : ZMod 1155228423149) ^ 2256305513) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 685707153940 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 1155228423149) ^ 9025222055 = 747099792463 := by
        calc
          (2 : ZMod 1155228423149) ^ 9025222055 = (2 : ZMod 1155228423149) ^ (4512611027 + 4512611027 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 4512611027 * (2 : ZMod 1155228423149) ^ 4512611027) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 747099792463 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 1155228423149) ^ 18050444111 = 930176895234 := by
        calc
          (2 : ZMod 1155228423149) ^ 18050444111 = (2 : ZMod 1155228423149) ^ (9025222055 + 9025222055 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 9025222055 * (2 : ZMod 1155228423149) ^ 9025222055) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 930176895234 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 1155228423149) ^ 36100888223 = 702021734930 := by
        calc
          (2 : ZMod 1155228423149) ^ 36100888223 = (2 : ZMod 1155228423149) ^ (18050444111 + 18050444111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 18050444111 * (2 : ZMod 1155228423149) ^ 18050444111) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 702021734930 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 1155228423149) ^ 72201776446 = 37239342074 := by
        calc
          (2 : ZMod 1155228423149) ^ 72201776446 = (2 : ZMod 1155228423149) ^ (36100888223 + 36100888223) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 36100888223 * (2 : ZMod 1155228423149) ^ 36100888223 := by rw [pow_add]
          _ = 37239342074 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 1155228423149) ^ 144403552893 = 1150399615542 := by
        calc
          (2 : ZMod 1155228423149) ^ 144403552893 = (2 : ZMod 1155228423149) ^ (72201776446 + 72201776446 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 72201776446 * (2 : ZMod 1155228423149) ^ 72201776446) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1150399615542 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 1155228423149) ^ 288807105787 = 1145570807934 := by
        calc
          (2 : ZMod 1155228423149) ^ 288807105787 = (2 : ZMod 1155228423149) ^ (144403552893 + 144403552893 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 144403552893 * (2 : ZMod 1155228423149) ^ 144403552893) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1145570807934 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 1155228423149) ^ 577614211574 = 1155228423148 := by
        calc
          (2 : ZMod 1155228423149) ^ 577614211574 = (2 : ZMod 1155228423149) ^ (288807105787 + 288807105787) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 288807105787 * (2 : ZMod 1155228423149) ^ 288807105787 := by rw [pow_add]
          _ = 1155228423148 := by rw [factor_0_38]; decide
      change (2 : ZMod 1155228423149) ^ 577614211574 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1155228423149) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1155228423149) ^ 2 = 4 := by
        calc
          (2 : ZMod 1155228423149) ^ 2 = (2 : ZMod 1155228423149) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 1 * (2 : ZMod 1155228423149) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1155228423149) ^ 5 = 32 := by
        calc
          (2 : ZMod 1155228423149) ^ 5 = (2 : ZMod 1155228423149) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2 * (2 : ZMod 1155228423149) ^ 2) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1155228423149) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1155228423149) ^ 10 = (2 : ZMod 1155228423149) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 5 * (2 : ZMod 1155228423149) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1155228423149) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 1155228423149) ^ 21 = (2 : ZMod 1155228423149) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 10 * (2 : ZMod 1155228423149) ^ 10) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1155228423149) ^ 42 = 932361241657 := by
        calc
          (2 : ZMod 1155228423149) ^ 42 = (2 : ZMod 1155228423149) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 21 * (2 : ZMod 1155228423149) ^ 21 := by rw [pow_add]
          _ = 932361241657 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1155228423149) ^ 84 = 542836247947 := by
        calc
          (2 : ZMod 1155228423149) ^ 84 = (2 : ZMod 1155228423149) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 42 * (2 : ZMod 1155228423149) ^ 42 := by rw [pow_add]
          _ = 542836247947 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1155228423149) ^ 168 = 576554438952 := by
        calc
          (2 : ZMod 1155228423149) ^ 168 = (2 : ZMod 1155228423149) ^ (84 + 84) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 84 * (2 : ZMod 1155228423149) ^ 84 := by rw [pow_add]
          _ = 576554438952 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1155228423149) ^ 336 = 28694271323 := by
        calc
          (2 : ZMod 1155228423149) ^ 336 = (2 : ZMod 1155228423149) ^ (168 + 168) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 168 * (2 : ZMod 1155228423149) ^ 168 := by rw [pow_add]
          _ = 28694271323 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1155228423149) ^ 673 = 276316662289 := by
        calc
          (2 : ZMod 1155228423149) ^ 673 = (2 : ZMod 1155228423149) ^ (336 + 336 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 336 * (2 : ZMod 1155228423149) ^ 336) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 276316662289 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1155228423149) ^ 1346 = 79240862674 := by
        calc
          (2 : ZMod 1155228423149) ^ 1346 = (2 : ZMod 1155228423149) ^ (673 + 673) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 673 * (2 : ZMod 1155228423149) ^ 673 := by rw [pow_add]
          _ = 79240862674 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1155228423149) ^ 2693 = 998330131574 := by
        calc
          (2 : ZMod 1155228423149) ^ 2693 = (2 : ZMod 1155228423149) ^ (1346 + 1346 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1346 * (2 : ZMod 1155228423149) ^ 1346) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 998330131574 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1155228423149) ^ 5387 = 655354407516 := by
        calc
          (2 : ZMod 1155228423149) ^ 5387 = (2 : ZMod 1155228423149) ^ (2693 + 2693 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2693 * (2 : ZMod 1155228423149) ^ 2693) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 655354407516 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1155228423149) ^ 10774 = 441779810452 := by
        calc
          (2 : ZMod 1155228423149) ^ 10774 = (2 : ZMod 1155228423149) ^ (5387 + 5387) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 5387 * (2 : ZMod 1155228423149) ^ 5387 := by rw [pow_add]
          _ = 441779810452 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1155228423149) ^ 21549 = 800596296225 := by
        calc
          (2 : ZMod 1155228423149) ^ 21549 = (2 : ZMod 1155228423149) ^ (10774 + 10774 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 10774 * (2 : ZMod 1155228423149) ^ 10774) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 800596296225 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1155228423149) ^ 43098 = 974423389261 := by
        calc
          (2 : ZMod 1155228423149) ^ 43098 = (2 : ZMod 1155228423149) ^ (21549 + 21549) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 21549 * (2 : ZMod 1155228423149) ^ 21549 := by rw [pow_add]
          _ = 974423389261 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1155228423149) ^ 86197 = 717429263848 := by
        calc
          (2 : ZMod 1155228423149) ^ 86197 = (2 : ZMod 1155228423149) ^ (43098 + 43098 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 43098 * (2 : ZMod 1155228423149) ^ 43098) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 717429263848 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1155228423149) ^ 172394 = 56968956831 := by
        calc
          (2 : ZMod 1155228423149) ^ 172394 = (2 : ZMod 1155228423149) ^ (86197 + 86197) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 86197 * (2 : ZMod 1155228423149) ^ 86197 := by rw [pow_add]
          _ = 56968956831 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1155228423149) ^ 344789 = 944520349602 := by
        calc
          (2 : ZMod 1155228423149) ^ 344789 = (2 : ZMod 1155228423149) ^ (172394 + 172394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 172394 * (2 : ZMod 1155228423149) ^ 172394) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 944520349602 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1155228423149) ^ 689579 = 363419745115 := by
        calc
          (2 : ZMod 1155228423149) ^ 689579 = (2 : ZMod 1155228423149) ^ (344789 + 344789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 344789 * (2 : ZMod 1155228423149) ^ 344789) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 363419745115 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1155228423149) ^ 1379159 = 684291542076 := by
        calc
          (2 : ZMod 1155228423149) ^ 1379159 = (2 : ZMod 1155228423149) ^ (689579 + 689579 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 689579 * (2 : ZMod 1155228423149) ^ 689579) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 684291542076 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1155228423149) ^ 2758319 = 25122697379 := by
        calc
          (2 : ZMod 1155228423149) ^ 2758319 = (2 : ZMod 1155228423149) ^ (1379159 + 1379159 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1379159 * (2 : ZMod 1155228423149) ^ 1379159) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 25122697379 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1155228423149) ^ 5516639 = 672571970333 := by
        calc
          (2 : ZMod 1155228423149) ^ 5516639 = (2 : ZMod 1155228423149) ^ (2758319 + 2758319 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2758319 * (2 : ZMod 1155228423149) ^ 2758319) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 672571970333 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1155228423149) ^ 11033278 = 578911576859 := by
        calc
          (2 : ZMod 1155228423149) ^ 11033278 = (2 : ZMod 1155228423149) ^ (5516639 + 5516639) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 5516639 * (2 : ZMod 1155228423149) ^ 5516639 := by rw [pow_add]
          _ = 578911576859 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1155228423149) ^ 22066557 = 264749597286 := by
        calc
          (2 : ZMod 1155228423149) ^ 22066557 = (2 : ZMod 1155228423149) ^ (11033278 + 11033278 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 11033278 * (2 : ZMod 1155228423149) ^ 11033278) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 264749597286 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1155228423149) ^ 44133115 = 482246530923 := by
        calc
          (2 : ZMod 1155228423149) ^ 44133115 = (2 : ZMod 1155228423149) ^ (22066557 + 22066557 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 22066557 * (2 : ZMod 1155228423149) ^ 22066557) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 482246530923 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1155228423149) ^ 88266230 = 868518005573 := by
        calc
          (2 : ZMod 1155228423149) ^ 88266230 = (2 : ZMod 1155228423149) ^ (44133115 + 44133115) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 44133115 * (2 : ZMod 1155228423149) ^ 44133115 := by rw [pow_add]
          _ = 868518005573 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1155228423149) ^ 176532460 = 51262541963 := by
        calc
          (2 : ZMod 1155228423149) ^ 176532460 = (2 : ZMod 1155228423149) ^ (88266230 + 88266230) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 88266230 * (2 : ZMod 1155228423149) ^ 88266230 := by rw [pow_add]
          _ = 51262541963 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 1155228423149) ^ 353064921 = 1124618779498 := by
        calc
          (2 : ZMod 1155228423149) ^ 353064921 = (2 : ZMod 1155228423149) ^ (176532460 + 176532460 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 176532460 * (2 : ZMod 1155228423149) ^ 176532460) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1124618779498 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 1155228423149) ^ 706129843 = 179028074585 := by
        calc
          (2 : ZMod 1155228423149) ^ 706129843 = (2 : ZMod 1155228423149) ^ (353064921 + 353064921 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 353064921 * (2 : ZMod 1155228423149) ^ 353064921) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 179028074585 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 1155228423149) ^ 1412259686 = 37625409385 := by
        calc
          (2 : ZMod 1155228423149) ^ 1412259686 = (2 : ZMod 1155228423149) ^ (706129843 + 706129843) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 706129843 * (2 : ZMod 1155228423149) ^ 706129843 := by rw [pow_add]
          _ = 37625409385 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 1155228423149) ^ 2824519372 = 656630961170 := by
        calc
          (2 : ZMod 1155228423149) ^ 2824519372 = (2 : ZMod 1155228423149) ^ (1412259686 + 1412259686) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 1412259686 * (2 : ZMod 1155228423149) ^ 1412259686 := by rw [pow_add]
          _ = 656630961170 := by rw [factor_1_30]; decide
      change (2 : ZMod 1155228423149) ^ 2824519372 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1155228423149) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1155228423149) ^ 2 = 4 := by
        calc
          (2 : ZMod 1155228423149) ^ 2 = (2 : ZMod 1155228423149) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 1 * (2 : ZMod 1155228423149) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1155228423149) ^ 4 = 16 := by
        calc
          (2 : ZMod 1155228423149) ^ 4 = (2 : ZMod 1155228423149) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 2 * (2 : ZMod 1155228423149) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1155228423149) ^ 8 = 256 := by
        calc
          (2 : ZMod 1155228423149) ^ 8 = (2 : ZMod 1155228423149) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 4 * (2 : ZMod 1155228423149) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1155228423149) ^ 16 = 65536 := by
        calc
          (2 : ZMod 1155228423149) ^ 16 = (2 : ZMod 1155228423149) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8 * (2 : ZMod 1155228423149) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1155228423149) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 1155228423149) ^ 32 = (2 : ZMod 1155228423149) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 16 * (2 : ZMod 1155228423149) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1155228423149) ^ 64 = 6673585315 := by
        calc
          (2 : ZMod 1155228423149) ^ 64 = (2 : ZMod 1155228423149) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 32 * (2 : ZMod 1155228423149) ^ 32 := by rw [pow_add]
          _ = 6673585315 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1155228423149) ^ 129 = 986668601898 := by
        calc
          (2 : ZMod 1155228423149) ^ 129 = (2 : ZMod 1155228423149) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 64 * (2 : ZMod 1155228423149) ^ 64) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 986668601898 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1155228423149) ^ 259 = 928802571532 := by
        calc
          (2 : ZMod 1155228423149) ^ 259 = (2 : ZMod 1155228423149) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 129 * (2 : ZMod 1155228423149) ^ 129) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 928802571532 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1155228423149) ^ 518 = 211358170770 := by
        calc
          (2 : ZMod 1155228423149) ^ 518 = (2 : ZMod 1155228423149) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 259 * (2 : ZMod 1155228423149) ^ 259 := by rw [pow_add]
          _ = 211358170770 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1155228423149) ^ 1036 = 169641079886 := by
        calc
          (2 : ZMod 1155228423149) ^ 1036 = (2 : ZMod 1155228423149) ^ (518 + 518) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 518 * (2 : ZMod 1155228423149) ^ 518 := by rw [pow_add]
          _ = 169641079886 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1155228423149) ^ 2072 = 1022231556458 := by
        calc
          (2 : ZMod 1155228423149) ^ 2072 = (2 : ZMod 1155228423149) ^ (1036 + 1036) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 1036 * (2 : ZMod 1155228423149) ^ 1036 := by rw [pow_add]
          _ = 1022231556458 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1155228423149) ^ 4144 = 95463983324 := by
        calc
          (2 : ZMod 1155228423149) ^ 4144 = (2 : ZMod 1155228423149) ^ (2072 + 2072) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 2072 * (2 : ZMod 1155228423149) ^ 2072 := by rw [pow_add]
          _ = 95463983324 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1155228423149) ^ 8289 = 431125013360 := by
        calc
          (2 : ZMod 1155228423149) ^ 8289 = (2 : ZMod 1155228423149) ^ (4144 + 4144 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 4144 * (2 : ZMod 1155228423149) ^ 4144) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 431125013360 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1155228423149) ^ 16578 = 437248440381 := by
        calc
          (2 : ZMod 1155228423149) ^ 16578 = (2 : ZMod 1155228423149) ^ (8289 + 8289) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 8289 * (2 : ZMod 1155228423149) ^ 8289 := by rw [pow_add]
          _ = 437248440381 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1155228423149) ^ 33157 = 1141491293782 := by
        calc
          (2 : ZMod 1155228423149) ^ 33157 = (2 : ZMod 1155228423149) ^ (16578 + 16578 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 16578 * (2 : ZMod 1155228423149) ^ 16578) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1141491293782 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1155228423149) ^ 66315 = 94306764118 := by
        calc
          (2 : ZMod 1155228423149) ^ 66315 = (2 : ZMod 1155228423149) ^ (33157 + 33157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 33157 * (2 : ZMod 1155228423149) ^ 33157) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 94306764118 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1155228423149) ^ 132630 = 551316552252 := by
        calc
          (2 : ZMod 1155228423149) ^ 132630 = (2 : ZMod 1155228423149) ^ (66315 + 66315) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 66315 * (2 : ZMod 1155228423149) ^ 66315 := by rw [pow_add]
          _ = 551316552252 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1155228423149) ^ 265260 = 808381826784 := by
        calc
          (2 : ZMod 1155228423149) ^ 265260 = (2 : ZMod 1155228423149) ^ (132630 + 132630) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 132630 * (2 : ZMod 1155228423149) ^ 132630 := by rw [pow_add]
          _ = 808381826784 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1155228423149) ^ 530520 = 380044115693 := by
        calc
          (2 : ZMod 1155228423149) ^ 530520 = (2 : ZMod 1155228423149) ^ (265260 + 265260) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 265260 * (2 : ZMod 1155228423149) ^ 265260 := by rw [pow_add]
          _ = 380044115693 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1155228423149) ^ 1061041 = 436282674673 := by
        calc
          (2 : ZMod 1155228423149) ^ 1061041 = (2 : ZMod 1155228423149) ^ (530520 + 530520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 530520 * (2 : ZMod 1155228423149) ^ 530520) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 436282674673 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1155228423149) ^ 2122083 = 1056573050089 := by
        calc
          (2 : ZMod 1155228423149) ^ 2122083 = (2 : ZMod 1155228423149) ^ (1061041 + 1061041 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1061041 * (2 : ZMod 1155228423149) ^ 1061041) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1056573050089 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1155228423149) ^ 4244167 = 435161995286 := by
        calc
          (2 : ZMod 1155228423149) ^ 4244167 = (2 : ZMod 1155228423149) ^ (2122083 + 2122083 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 2122083 * (2 : ZMod 1155228423149) ^ 2122083) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 435161995286 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1155228423149) ^ 8488334 = 996366920975 := by
        calc
          (2 : ZMod 1155228423149) ^ 8488334 = (2 : ZMod 1155228423149) ^ (4244167 + 4244167) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 4244167 * (2 : ZMod 1155228423149) ^ 4244167 := by rw [pow_add]
          _ = 996366920975 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1155228423149) ^ 16976669 = 331786444383 := by
        calc
          (2 : ZMod 1155228423149) ^ 16976669 = (2 : ZMod 1155228423149) ^ (8488334 + 8488334 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 8488334 * (2 : ZMod 1155228423149) ^ 8488334) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 331786444383 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1155228423149) ^ 33953339 = 945430509388 := by
        calc
          (2 : ZMod 1155228423149) ^ 33953339 = (2 : ZMod 1155228423149) ^ (16976669 + 16976669 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 16976669 * (2 : ZMod 1155228423149) ^ 16976669) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 945430509388 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1155228423149) ^ 67906679 = 39978095288 := by
        calc
          (2 : ZMod 1155228423149) ^ 67906679 = (2 : ZMod 1155228423149) ^ (33953339 + 33953339 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 33953339 * (2 : ZMod 1155228423149) ^ 33953339) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 39978095288 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 1155228423149) ^ 135813358 = 745371530073 := by
        calc
          (2 : ZMod 1155228423149) ^ 135813358 = (2 : ZMod 1155228423149) ^ (67906679 + 67906679) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 67906679 * (2 : ZMod 1155228423149) ^ 67906679 := by rw [pow_add]
          _ = 745371530073 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 1155228423149) ^ 271626716 = 613183602937 := by
        calc
          (2 : ZMod 1155228423149) ^ 271626716 = (2 : ZMod 1155228423149) ^ (135813358 + 135813358) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 135813358 * (2 : ZMod 1155228423149) ^ 135813358 := by rw [pow_add]
          _ = 613183602937 := by rw [factor_2_27]; decide
      change (2 : ZMod 1155228423149) ^ 271626716 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1155228423149) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1155228423149) ^ 3 = 8 := by
        calc
          (2 : ZMod 1155228423149) ^ 3 = (2 : ZMod 1155228423149) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1 * (2 : ZMod 1155228423149) ^ 1) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1155228423149) ^ 6 = 64 := by
        calc
          (2 : ZMod 1155228423149) ^ 6 = (2 : ZMod 1155228423149) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 3 * (2 : ZMod 1155228423149) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1155228423149) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1155228423149) ^ 13 = (2 : ZMod 1155228423149) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 6 * (2 : ZMod 1155228423149) ^ 6) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1155228423149) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 1155228423149) ^ 26 = (2 : ZMod 1155228423149) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 13 * (2 : ZMod 1155228423149) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1155228423149) ^ 53 = 1038467871388 := by
        calc
          (2 : ZMod 1155228423149) ^ 53 = (2 : ZMod 1155228423149) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 26 * (2 : ZMod 1155228423149) ^ 26) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 1038467871388 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1155228423149) ^ 106 = 185807923321 := by
        calc
          (2 : ZMod 1155228423149) ^ 106 = (2 : ZMod 1155228423149) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 53 * (2 : ZMod 1155228423149) ^ 53 := by rw [pow_add]
          _ = 185807923321 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1155228423149) ^ 212 = 929688605853 := by
        calc
          (2 : ZMod 1155228423149) ^ 212 = (2 : ZMod 1155228423149) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 106 * (2 : ZMod 1155228423149) ^ 106 := by rw [pow_add]
          _ = 929688605853 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1155228423149) ^ 424 = 129082580604 := by
        calc
          (2 : ZMod 1155228423149) ^ 424 = (2 : ZMod 1155228423149) ^ (212 + 212) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 212 * (2 : ZMod 1155228423149) ^ 212 := by rw [pow_add]
          _ = 129082580604 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1155228423149) ^ 849 = 860167243310 := by
        calc
          (2 : ZMod 1155228423149) ^ 849 = (2 : ZMod 1155228423149) ^ (424 + 424 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 424 * (2 : ZMod 1155228423149) ^ 424) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 860167243310 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 1155228423149) ^ 1698 = 963748608949 := by
        calc
          (2 : ZMod 1155228423149) ^ 1698 = (2 : ZMod 1155228423149) ^ (849 + 849) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 849 * (2 : ZMod 1155228423149) ^ 849 := by rw [pow_add]
          _ = 963748608949 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 1155228423149) ^ 3397 = 644513271523 := by
        calc
          (2 : ZMod 1155228423149) ^ 3397 = (2 : ZMod 1155228423149) ^ (1698 + 1698 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 1698 * (2 : ZMod 1155228423149) ^ 1698) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 644513271523 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 1155228423149) ^ 6794 = 1086646956699 := by
        calc
          (2 : ZMod 1155228423149) ^ 6794 = (2 : ZMod 1155228423149) ^ (3397 + 3397) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 3397 * (2 : ZMod 1155228423149) ^ 3397 := by rw [pow_add]
          _ = 1086646956699 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 1155228423149) ^ 13589 = 390232096007 := by
        calc
          (2 : ZMod 1155228423149) ^ 13589 = (2 : ZMod 1155228423149) ^ (6794 + 6794 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 6794 * (2 : ZMod 1155228423149) ^ 6794) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 390232096007 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 1155228423149) ^ 27179 = 170659616850 := by
        calc
          (2 : ZMod 1155228423149) ^ 27179 = (2 : ZMod 1155228423149) ^ (13589 + 13589 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 13589 * (2 : ZMod 1155228423149) ^ 13589) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 170659616850 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 1155228423149) ^ 54358 = 882275921607 := by
        calc
          (2 : ZMod 1155228423149) ^ 54358 = (2 : ZMod 1155228423149) ^ (27179 + 27179) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 27179 * (2 : ZMod 1155228423149) ^ 27179 := by rw [pow_add]
          _ = 882275921607 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 1155228423149) ^ 108717 = 465509577698 := by
        calc
          (2 : ZMod 1155228423149) ^ 108717 = (2 : ZMod 1155228423149) ^ (54358 + 54358 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 54358 * (2 : ZMod 1155228423149) ^ 54358) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 465509577698 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 1155228423149) ^ 217434 = 640198117804 := by
        calc
          (2 : ZMod 1155228423149) ^ 217434 = (2 : ZMod 1155228423149) ^ (108717 + 108717) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 108717 * (2 : ZMod 1155228423149) ^ 108717 := by rw [pow_add]
          _ = 640198117804 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 1155228423149) ^ 434869 = 117543363090 := by
        calc
          (2 : ZMod 1155228423149) ^ 434869 = (2 : ZMod 1155228423149) ^ (217434 + 217434 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 217434 * (2 : ZMod 1155228423149) ^ 217434) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 117543363090 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 1155228423149) ^ 869738 = 323759292973 := by
        calc
          (2 : ZMod 1155228423149) ^ 869738 = (2 : ZMod 1155228423149) ^ (434869 + 434869) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 434869 * (2 : ZMod 1155228423149) ^ 434869 := by rw [pow_add]
          _ = 323759292973 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 1155228423149) ^ 1739477 = 806973310242 := by
        calc
          (2 : ZMod 1155228423149) ^ 1739477 = (2 : ZMod 1155228423149) ^ (869738 + 869738 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = ((2 : ZMod 1155228423149) ^ 869738 * (2 : ZMod 1155228423149) ^ 869738) * (2 : ZMod 1155228423149) := by rw [pow_succ, pow_add]
          _ = 806973310242 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 1155228423149) ^ 3478954 = 1034030623755 := by
        calc
          (2 : ZMod 1155228423149) ^ 3478954 = (2 : ZMod 1155228423149) ^ (1739477 + 1739477) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 1739477 * (2 : ZMod 1155228423149) ^ 1739477 := by rw [pow_add]
          _ = 1034030623755 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 1155228423149) ^ 6957908 = 225473405106 := by
        calc
          (2 : ZMod 1155228423149) ^ 6957908 = (2 : ZMod 1155228423149) ^ (3478954 + 3478954) :=
            congrArg (fun n : ℕ => (2 : ZMod 1155228423149) ^ n) (by norm_num)
          _ = (2 : ZMod 1155228423149) ^ 3478954 * (2 : ZMod 1155228423149) ^ 3478954 := by rw [pow_add]
          _ = 225473405106 := by rw [factor_3_21]; decide
      change (2 : ZMod 1155228423149) ^ 6957908 ≠ 1
      rw [factor_3_22]
      decide

#print axioms prime_lucas_1155228423149

end TotientTailPeriodKiller
end Erdos249257
