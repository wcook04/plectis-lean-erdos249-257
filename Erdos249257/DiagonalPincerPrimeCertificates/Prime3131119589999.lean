import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime92091752647

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3131119589999 : Nat.Prime 3131119589999 := by
  apply lucas_primality 3131119589999 (7 : ZMod 3131119589999)
  ·
      have fermat_0 : (7 : ZMod 3131119589999) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 3131119589999) ^ 2 = 49 := by
        calc
          (7 : ZMod 3131119589999) ^ 2 = (7 : ZMod 3131119589999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1 * (7 : ZMod 3131119589999) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 3131119589999) ^ 5 = 16807 := by
        calc
          (7 : ZMod 3131119589999) ^ 5 = (7 : ZMod 3131119589999) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 2 * (7 : ZMod 3131119589999) ^ 2) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 3131119589999) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 3131119589999) ^ 11 = (7 : ZMod 3131119589999) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 5 * (7 : ZMod 3131119589999) ^ 5) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 3131119589999) ^ 22 = 1409910006746 := by
        calc
          (7 : ZMod 3131119589999) ^ 22 = (7 : ZMod 3131119589999) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 11 * (7 : ZMod 3131119589999) ^ 11 := by rw [pow_add]
          _ = 1409910006746 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 3131119589999) ^ 45 = 283238719142 := by
        calc
          (7 : ZMod 3131119589999) ^ 45 = (7 : ZMod 3131119589999) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 22 * (7 : ZMod 3131119589999) ^ 22) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 283238719142 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 3131119589999) ^ 91 = 3105131441148 := by
        calc
          (7 : ZMod 3131119589999) ^ 91 = (7 : ZMod 3131119589999) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 45 * (7 : ZMod 3131119589999) ^ 45) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 3105131441148 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 3131119589999) ^ 182 = 1184089540643 := by
        calc
          (7 : ZMod 3131119589999) ^ 182 = (7 : ZMod 3131119589999) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 91 * (7 : ZMod 3131119589999) ^ 91 := by rw [pow_add]
          _ = 1184089540643 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 3131119589999) ^ 364 = 2414832383153 := by
        calc
          (7 : ZMod 3131119589999) ^ 364 = (7 : ZMod 3131119589999) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 182 * (7 : ZMod 3131119589999) ^ 182 := by rw [pow_add]
          _ = 2414832383153 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 3131119589999) ^ 729 = 2715617243738 := by
        calc
          (7 : ZMod 3131119589999) ^ 729 = (7 : ZMod 3131119589999) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 364 * (7 : ZMod 3131119589999) ^ 364) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2715617243738 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 3131119589999) ^ 1458 = 495502359936 := by
        calc
          (7 : ZMod 3131119589999) ^ 1458 = (7 : ZMod 3131119589999) ^ (729 + 729) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 729 * (7 : ZMod 3131119589999) ^ 729 := by rw [pow_add]
          _ = 495502359936 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 3131119589999) ^ 2916 = 2275698537430 := by
        calc
          (7 : ZMod 3131119589999) ^ 2916 = (7 : ZMod 3131119589999) ^ (1458 + 1458) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1458 * (7 : ZMod 3131119589999) ^ 1458 := by rw [pow_add]
          _ = 2275698537430 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 3131119589999) ^ 5832 = 2721197667457 := by
        calc
          (7 : ZMod 3131119589999) ^ 5832 = (7 : ZMod 3131119589999) ^ (2916 + 2916) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 2916 * (7 : ZMod 3131119589999) ^ 2916 := by rw [pow_add]
          _ = 2721197667457 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 3131119589999) ^ 11664 = 2021144432911 := by
        calc
          (7 : ZMod 3131119589999) ^ 11664 = (7 : ZMod 3131119589999) ^ (5832 + 5832) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 5832 * (7 : ZMod 3131119589999) ^ 5832 := by rw [pow_add]
          _ = 2021144432911 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 3131119589999) ^ 23328 = 2561621384478 := by
        calc
          (7 : ZMod 3131119589999) ^ 23328 = (7 : ZMod 3131119589999) ^ (11664 + 11664) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 11664 * (7 : ZMod 3131119589999) ^ 11664 := by rw [pow_add]
          _ = 2561621384478 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 3131119589999) ^ 46657 = 2380423939415 := by
        calc
          (7 : ZMod 3131119589999) ^ 46657 = (7 : ZMod 3131119589999) ^ (23328 + 23328 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 23328 * (7 : ZMod 3131119589999) ^ 23328) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2380423939415 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 3131119589999) ^ 93314 = 439211525813 := by
        calc
          (7 : ZMod 3131119589999) ^ 93314 = (7 : ZMod 3131119589999) ^ (46657 + 46657) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 46657 * (7 : ZMod 3131119589999) ^ 46657 := by rw [pow_add]
          _ = 439211525813 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 3131119589999) ^ 186629 = 1799471713095 := by
        calc
          (7 : ZMod 3131119589999) ^ 186629 = (7 : ZMod 3131119589999) ^ (93314 + 93314 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 93314 * (7 : ZMod 3131119589999) ^ 93314) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1799471713095 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 3131119589999) ^ 373258 = 554368616166 := by
        calc
          (7 : ZMod 3131119589999) ^ 373258 = (7 : ZMod 3131119589999) ^ (186629 + 186629) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 186629 * (7 : ZMod 3131119589999) ^ 186629 := by rw [pow_add]
          _ = 554368616166 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 3131119589999) ^ 746517 = 618153815859 := by
        calc
          (7 : ZMod 3131119589999) ^ 746517 = (7 : ZMod 3131119589999) ^ (373258 + 373258 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 373258 * (7 : ZMod 3131119589999) ^ 373258) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 618153815859 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 3131119589999) ^ 1493034 = 2039105320388 := by
        calc
          (7 : ZMod 3131119589999) ^ 1493034 = (7 : ZMod 3131119589999) ^ (746517 + 746517) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 746517 * (7 : ZMod 3131119589999) ^ 746517 := by rw [pow_add]
          _ = 2039105320388 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 3131119589999) ^ 2986068 = 2547526792287 := by
        calc
          (7 : ZMod 3131119589999) ^ 2986068 = (7 : ZMod 3131119589999) ^ (1493034 + 1493034) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1493034 * (7 : ZMod 3131119589999) ^ 1493034 := by rw [pow_add]
          _ = 2547526792287 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 3131119589999) ^ 5972136 = 2788076895753 := by
        calc
          (7 : ZMod 3131119589999) ^ 5972136 = (7 : ZMod 3131119589999) ^ (2986068 + 2986068) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 2986068 * (7 : ZMod 3131119589999) ^ 2986068 := by rw [pow_add]
          _ = 2788076895753 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 3131119589999) ^ 11944273 = 1295227809839 := by
        calc
          (7 : ZMod 3131119589999) ^ 11944273 = (7 : ZMod 3131119589999) ^ (5972136 + 5972136 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 5972136 * (7 : ZMod 3131119589999) ^ 5972136) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1295227809839 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 3131119589999) ^ 23888546 = 846162445164 := by
        calc
          (7 : ZMod 3131119589999) ^ 23888546 = (7 : ZMod 3131119589999) ^ (11944273 + 11944273) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 11944273 * (7 : ZMod 3131119589999) ^ 11944273 := by rw [pow_add]
          _ = 846162445164 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 3131119589999) ^ 47777093 = 1348858796040 := by
        calc
          (7 : ZMod 3131119589999) ^ 47777093 = (7 : ZMod 3131119589999) ^ (23888546 + 23888546 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 23888546 * (7 : ZMod 3131119589999) ^ 23888546) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1348858796040 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 3131119589999) ^ 95554186 = 2282651034124 := by
        calc
          (7 : ZMod 3131119589999) ^ 95554186 = (7 : ZMod 3131119589999) ^ (47777093 + 47777093) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 47777093 * (7 : ZMod 3131119589999) ^ 47777093 := by rw [pow_add]
          _ = 2282651034124 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 3131119589999) ^ 191108373 = 2401869423103 := by
        calc
          (7 : ZMod 3131119589999) ^ 191108373 = (7 : ZMod 3131119589999) ^ (95554186 + 95554186 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 95554186 * (7 : ZMod 3131119589999) ^ 95554186) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2401869423103 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 3131119589999) ^ 382216746 = 1941863420045 := by
        calc
          (7 : ZMod 3131119589999) ^ 382216746 = (7 : ZMod 3131119589999) ^ (191108373 + 191108373) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 191108373 * (7 : ZMod 3131119589999) ^ 191108373 := by rw [pow_add]
          _ = 1941863420045 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 3131119589999) ^ 764433493 = 1279060891901 := by
        calc
          (7 : ZMod 3131119589999) ^ 764433493 = (7 : ZMod 3131119589999) ^ (382216746 + 382216746 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 382216746 * (7 : ZMod 3131119589999) ^ 382216746) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1279060891901 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 3131119589999) ^ 1528866987 = 357148310378 := by
        calc
          (7 : ZMod 3131119589999) ^ 1528866987 = (7 : ZMod 3131119589999) ^ (764433493 + 764433493 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 764433493 * (7 : ZMod 3131119589999) ^ 764433493) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 357148310378 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 3131119589999) ^ 3057733974 = 589589060320 := by
        calc
          (7 : ZMod 3131119589999) ^ 3057733974 = (7 : ZMod 3131119589999) ^ (1528866987 + 1528866987) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1528866987 * (7 : ZMod 3131119589999) ^ 1528866987 := by rw [pow_add]
          _ = 589589060320 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 3131119589999) ^ 6115467949 = 2481796457460 := by
        calc
          (7 : ZMod 3131119589999) ^ 6115467949 = (7 : ZMod 3131119589999) ^ (3057733974 + 3057733974 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 3057733974 * (7 : ZMod 3131119589999) ^ 3057733974) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2481796457460 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 3131119589999) ^ 12230935898 = 734526415816 := by
        calc
          (7 : ZMod 3131119589999) ^ 12230935898 = (7 : ZMod 3131119589999) ^ (6115467949 + 6115467949) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 6115467949 * (7 : ZMod 3131119589999) ^ 6115467949 := by rw [pow_add]
          _ = 734526415816 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 3131119589999) ^ 24461871796 = 1206703420677 := by
        calc
          (7 : ZMod 3131119589999) ^ 24461871796 = (7 : ZMod 3131119589999) ^ (12230935898 + 12230935898) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 12230935898 * (7 : ZMod 3131119589999) ^ 12230935898 := by rw [pow_add]
          _ = 1206703420677 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 3131119589999) ^ 48923743593 = 3123571557645 := by
        calc
          (7 : ZMod 3131119589999) ^ 48923743593 = (7 : ZMod 3131119589999) ^ (24461871796 + 24461871796 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 24461871796 * (7 : ZMod 3131119589999) ^ 24461871796) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 3123571557645 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 3131119589999) ^ 97847487187 = 124171548843 := by
        calc
          (7 : ZMod 3131119589999) ^ 97847487187 = (7 : ZMod 3131119589999) ^ (48923743593 + 48923743593 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 48923743593 * (7 : ZMod 3131119589999) ^ 48923743593) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 124171548843 := by rw [fermat_35]; decide
      have fermat_37 : (7 : ZMod 3131119589999) ^ 195694974374 = 1787154829078 := by
        calc
          (7 : ZMod 3131119589999) ^ 195694974374 = (7 : ZMod 3131119589999) ^ (97847487187 + 97847487187) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 97847487187 * (7 : ZMod 3131119589999) ^ 97847487187 := by rw [pow_add]
          _ = 1787154829078 := by rw [fermat_36]; decide
      have fermat_38 : (7 : ZMod 3131119589999) ^ 391389948749 = 1521622409707 := by
        calc
          (7 : ZMod 3131119589999) ^ 391389948749 = (7 : ZMod 3131119589999) ^ (195694974374 + 195694974374 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 195694974374 * (7 : ZMod 3131119589999) ^ 195694974374) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1521622409707 := by rw [fermat_37]; decide
      have fermat_39 : (7 : ZMod 3131119589999) ^ 782779897499 = 1288035600961 := by
        calc
          (7 : ZMod 3131119589999) ^ 782779897499 = (7 : ZMod 3131119589999) ^ (391389948749 + 391389948749 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 391389948749 * (7 : ZMod 3131119589999) ^ 391389948749) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1288035600961 := by rw [fermat_38]; decide
      have fermat_40 : (7 : ZMod 3131119589999) ^ 1565559794999 = 3131119589998 := by
        calc
          (7 : ZMod 3131119589999) ^ 1565559794999 = (7 : ZMod 3131119589999) ^ (782779897499 + 782779897499 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 782779897499 * (7 : ZMod 3131119589999) ^ 782779897499) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 3131119589998 := by rw [fermat_39]; decide
      have fermat_41 : (7 : ZMod 3131119589999) ^ 3131119589998 = 1 := by
        calc
          (7 : ZMod 3131119589999) ^ 3131119589998 = (7 : ZMod 3131119589999) ^ (1565559794999 + 1565559794999) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1565559794999 * (7 : ZMod 3131119589999) ^ 1565559794999 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (92091752647, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (92091752647, 1)] : List FactorBlock).map factorBlockValue).prod = 3131119589999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_92091752647) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 3131119589999) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 3131119589999) ^ 2 = 49 := by
        calc
          (7 : ZMod 3131119589999) ^ 2 = (7 : ZMod 3131119589999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1 * (7 : ZMod 3131119589999) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 3131119589999) ^ 5 = 16807 := by
        calc
          (7 : ZMod 3131119589999) ^ 5 = (7 : ZMod 3131119589999) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 2 * (7 : ZMod 3131119589999) ^ 2) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 3131119589999) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 3131119589999) ^ 11 = (7 : ZMod 3131119589999) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 5 * (7 : ZMod 3131119589999) ^ 5) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 3131119589999) ^ 22 = 1409910006746 := by
        calc
          (7 : ZMod 3131119589999) ^ 22 = (7 : ZMod 3131119589999) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 11 * (7 : ZMod 3131119589999) ^ 11 := by rw [pow_add]
          _ = 1409910006746 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 3131119589999) ^ 45 = 283238719142 := by
        calc
          (7 : ZMod 3131119589999) ^ 45 = (7 : ZMod 3131119589999) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 22 * (7 : ZMod 3131119589999) ^ 22) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 283238719142 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 3131119589999) ^ 91 = 3105131441148 := by
        calc
          (7 : ZMod 3131119589999) ^ 91 = (7 : ZMod 3131119589999) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 45 * (7 : ZMod 3131119589999) ^ 45) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 3105131441148 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 3131119589999) ^ 182 = 1184089540643 := by
        calc
          (7 : ZMod 3131119589999) ^ 182 = (7 : ZMod 3131119589999) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 91 * (7 : ZMod 3131119589999) ^ 91 := by rw [pow_add]
          _ = 1184089540643 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 3131119589999) ^ 364 = 2414832383153 := by
        calc
          (7 : ZMod 3131119589999) ^ 364 = (7 : ZMod 3131119589999) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 182 * (7 : ZMod 3131119589999) ^ 182 := by rw [pow_add]
          _ = 2414832383153 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 3131119589999) ^ 729 = 2715617243738 := by
        calc
          (7 : ZMod 3131119589999) ^ 729 = (7 : ZMod 3131119589999) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 364 * (7 : ZMod 3131119589999) ^ 364) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2715617243738 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 3131119589999) ^ 1458 = 495502359936 := by
        calc
          (7 : ZMod 3131119589999) ^ 1458 = (7 : ZMod 3131119589999) ^ (729 + 729) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 729 * (7 : ZMod 3131119589999) ^ 729 := by rw [pow_add]
          _ = 495502359936 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 3131119589999) ^ 2916 = 2275698537430 := by
        calc
          (7 : ZMod 3131119589999) ^ 2916 = (7 : ZMod 3131119589999) ^ (1458 + 1458) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1458 * (7 : ZMod 3131119589999) ^ 1458 := by rw [pow_add]
          _ = 2275698537430 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 3131119589999) ^ 5832 = 2721197667457 := by
        calc
          (7 : ZMod 3131119589999) ^ 5832 = (7 : ZMod 3131119589999) ^ (2916 + 2916) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 2916 * (7 : ZMod 3131119589999) ^ 2916 := by rw [pow_add]
          _ = 2721197667457 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 3131119589999) ^ 11664 = 2021144432911 := by
        calc
          (7 : ZMod 3131119589999) ^ 11664 = (7 : ZMod 3131119589999) ^ (5832 + 5832) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 5832 * (7 : ZMod 3131119589999) ^ 5832 := by rw [pow_add]
          _ = 2021144432911 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 3131119589999) ^ 23328 = 2561621384478 := by
        calc
          (7 : ZMod 3131119589999) ^ 23328 = (7 : ZMod 3131119589999) ^ (11664 + 11664) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 11664 * (7 : ZMod 3131119589999) ^ 11664 := by rw [pow_add]
          _ = 2561621384478 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 3131119589999) ^ 46657 = 2380423939415 := by
        calc
          (7 : ZMod 3131119589999) ^ 46657 = (7 : ZMod 3131119589999) ^ (23328 + 23328 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 23328 * (7 : ZMod 3131119589999) ^ 23328) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2380423939415 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 3131119589999) ^ 93314 = 439211525813 := by
        calc
          (7 : ZMod 3131119589999) ^ 93314 = (7 : ZMod 3131119589999) ^ (46657 + 46657) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 46657 * (7 : ZMod 3131119589999) ^ 46657 := by rw [pow_add]
          _ = 439211525813 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 3131119589999) ^ 186629 = 1799471713095 := by
        calc
          (7 : ZMod 3131119589999) ^ 186629 = (7 : ZMod 3131119589999) ^ (93314 + 93314 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 93314 * (7 : ZMod 3131119589999) ^ 93314) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1799471713095 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 3131119589999) ^ 373258 = 554368616166 := by
        calc
          (7 : ZMod 3131119589999) ^ 373258 = (7 : ZMod 3131119589999) ^ (186629 + 186629) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 186629 * (7 : ZMod 3131119589999) ^ 186629 := by rw [pow_add]
          _ = 554368616166 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 3131119589999) ^ 746517 = 618153815859 := by
        calc
          (7 : ZMod 3131119589999) ^ 746517 = (7 : ZMod 3131119589999) ^ (373258 + 373258 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 373258 * (7 : ZMod 3131119589999) ^ 373258) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 618153815859 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 3131119589999) ^ 1493034 = 2039105320388 := by
        calc
          (7 : ZMod 3131119589999) ^ 1493034 = (7 : ZMod 3131119589999) ^ (746517 + 746517) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 746517 * (7 : ZMod 3131119589999) ^ 746517 := by rw [pow_add]
          _ = 2039105320388 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 3131119589999) ^ 2986068 = 2547526792287 := by
        calc
          (7 : ZMod 3131119589999) ^ 2986068 = (7 : ZMod 3131119589999) ^ (1493034 + 1493034) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1493034 * (7 : ZMod 3131119589999) ^ 1493034 := by rw [pow_add]
          _ = 2547526792287 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 3131119589999) ^ 5972136 = 2788076895753 := by
        calc
          (7 : ZMod 3131119589999) ^ 5972136 = (7 : ZMod 3131119589999) ^ (2986068 + 2986068) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 2986068 * (7 : ZMod 3131119589999) ^ 2986068 := by rw [pow_add]
          _ = 2788076895753 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 3131119589999) ^ 11944273 = 1295227809839 := by
        calc
          (7 : ZMod 3131119589999) ^ 11944273 = (7 : ZMod 3131119589999) ^ (5972136 + 5972136 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 5972136 * (7 : ZMod 3131119589999) ^ 5972136) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1295227809839 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 3131119589999) ^ 23888546 = 846162445164 := by
        calc
          (7 : ZMod 3131119589999) ^ 23888546 = (7 : ZMod 3131119589999) ^ (11944273 + 11944273) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 11944273 * (7 : ZMod 3131119589999) ^ 11944273 := by rw [pow_add]
          _ = 846162445164 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 3131119589999) ^ 47777093 = 1348858796040 := by
        calc
          (7 : ZMod 3131119589999) ^ 47777093 = (7 : ZMod 3131119589999) ^ (23888546 + 23888546 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 23888546 * (7 : ZMod 3131119589999) ^ 23888546) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1348858796040 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 3131119589999) ^ 95554186 = 2282651034124 := by
        calc
          (7 : ZMod 3131119589999) ^ 95554186 = (7 : ZMod 3131119589999) ^ (47777093 + 47777093) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 47777093 * (7 : ZMod 3131119589999) ^ 47777093 := by rw [pow_add]
          _ = 2282651034124 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 3131119589999) ^ 191108373 = 2401869423103 := by
        calc
          (7 : ZMod 3131119589999) ^ 191108373 = (7 : ZMod 3131119589999) ^ (95554186 + 95554186 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 95554186 * (7 : ZMod 3131119589999) ^ 95554186) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2401869423103 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 3131119589999) ^ 382216746 = 1941863420045 := by
        calc
          (7 : ZMod 3131119589999) ^ 382216746 = (7 : ZMod 3131119589999) ^ (191108373 + 191108373) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 191108373 * (7 : ZMod 3131119589999) ^ 191108373 := by rw [pow_add]
          _ = 1941863420045 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 3131119589999) ^ 764433493 = 1279060891901 := by
        calc
          (7 : ZMod 3131119589999) ^ 764433493 = (7 : ZMod 3131119589999) ^ (382216746 + 382216746 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 382216746 * (7 : ZMod 3131119589999) ^ 382216746) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1279060891901 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 3131119589999) ^ 1528866987 = 357148310378 := by
        calc
          (7 : ZMod 3131119589999) ^ 1528866987 = (7 : ZMod 3131119589999) ^ (764433493 + 764433493 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 764433493 * (7 : ZMod 3131119589999) ^ 764433493) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 357148310378 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 3131119589999) ^ 3057733974 = 589589060320 := by
        calc
          (7 : ZMod 3131119589999) ^ 3057733974 = (7 : ZMod 3131119589999) ^ (1528866987 + 1528866987) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1528866987 * (7 : ZMod 3131119589999) ^ 1528866987 := by rw [pow_add]
          _ = 589589060320 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 3131119589999) ^ 6115467949 = 2481796457460 := by
        calc
          (7 : ZMod 3131119589999) ^ 6115467949 = (7 : ZMod 3131119589999) ^ (3057733974 + 3057733974 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 3057733974 * (7 : ZMod 3131119589999) ^ 3057733974) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2481796457460 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 3131119589999) ^ 12230935898 = 734526415816 := by
        calc
          (7 : ZMod 3131119589999) ^ 12230935898 = (7 : ZMod 3131119589999) ^ (6115467949 + 6115467949) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 6115467949 * (7 : ZMod 3131119589999) ^ 6115467949 := by rw [pow_add]
          _ = 734526415816 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 3131119589999) ^ 24461871796 = 1206703420677 := by
        calc
          (7 : ZMod 3131119589999) ^ 24461871796 = (7 : ZMod 3131119589999) ^ (12230935898 + 12230935898) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 12230935898 * (7 : ZMod 3131119589999) ^ 12230935898 := by rw [pow_add]
          _ = 1206703420677 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 3131119589999) ^ 48923743593 = 3123571557645 := by
        calc
          (7 : ZMod 3131119589999) ^ 48923743593 = (7 : ZMod 3131119589999) ^ (24461871796 + 24461871796 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 24461871796 * (7 : ZMod 3131119589999) ^ 24461871796) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 3123571557645 := by rw [factor_0_34]; decide
      have factor_0_36 : (7 : ZMod 3131119589999) ^ 97847487187 = 124171548843 := by
        calc
          (7 : ZMod 3131119589999) ^ 97847487187 = (7 : ZMod 3131119589999) ^ (48923743593 + 48923743593 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 48923743593 * (7 : ZMod 3131119589999) ^ 48923743593) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 124171548843 := by rw [factor_0_35]; decide
      have factor_0_37 : (7 : ZMod 3131119589999) ^ 195694974374 = 1787154829078 := by
        calc
          (7 : ZMod 3131119589999) ^ 195694974374 = (7 : ZMod 3131119589999) ^ (97847487187 + 97847487187) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 97847487187 * (7 : ZMod 3131119589999) ^ 97847487187 := by rw [pow_add]
          _ = 1787154829078 := by rw [factor_0_36]; decide
      have factor_0_38 : (7 : ZMod 3131119589999) ^ 391389948749 = 1521622409707 := by
        calc
          (7 : ZMod 3131119589999) ^ 391389948749 = (7 : ZMod 3131119589999) ^ (195694974374 + 195694974374 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 195694974374 * (7 : ZMod 3131119589999) ^ 195694974374) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1521622409707 := by rw [factor_0_37]; decide
      have factor_0_39 : (7 : ZMod 3131119589999) ^ 782779897499 = 1288035600961 := by
        calc
          (7 : ZMod 3131119589999) ^ 782779897499 = (7 : ZMod 3131119589999) ^ (391389948749 + 391389948749 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 391389948749 * (7 : ZMod 3131119589999) ^ 391389948749) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1288035600961 := by rw [factor_0_38]; decide
      have factor_0_40 : (7 : ZMod 3131119589999) ^ 1565559794999 = 3131119589998 := by
        calc
          (7 : ZMod 3131119589999) ^ 1565559794999 = (7 : ZMod 3131119589999) ^ (782779897499 + 782779897499 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 782779897499 * (7 : ZMod 3131119589999) ^ 782779897499) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 3131119589998 := by rw [factor_0_39]; decide
      change (7 : ZMod 3131119589999) ^ 1565559794999 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (7 : ZMod 3131119589999) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 3131119589999) ^ 2 = 49 := by
        calc
          (7 : ZMod 3131119589999) ^ 2 = (7 : ZMod 3131119589999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1 * (7 : ZMod 3131119589999) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 3131119589999) ^ 5 = 16807 := by
        calc
          (7 : ZMod 3131119589999) ^ 5 = (7 : ZMod 3131119589999) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 2 * (7 : ZMod 3131119589999) ^ 2) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 3131119589999) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 3131119589999) ^ 10 = (7 : ZMod 3131119589999) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 5 * (7 : ZMod 3131119589999) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 3131119589999) ^ 21 = 1096021312392 := by
        calc
          (7 : ZMod 3131119589999) ^ 21 = (7 : ZMod 3131119589999) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 10 * (7 : ZMod 3131119589999) ^ 10) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1096021312392 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 3131119589999) ^ 42 = 2712028445915 := by
        calc
          (7 : ZMod 3131119589999) ^ 42 = (7 : ZMod 3131119589999) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 21 * (7 : ZMod 3131119589999) ^ 21 := by rw [pow_add]
          _ = 2712028445915 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 3131119589999) ^ 85 = 2828384238875 := by
        calc
          (7 : ZMod 3131119589999) ^ 85 = (7 : ZMod 3131119589999) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 42 * (7 : ZMod 3131119589999) ^ 42) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2828384238875 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 3131119589999) ^ 171 = 943063302254 := by
        calc
          (7 : ZMod 3131119589999) ^ 171 = (7 : ZMod 3131119589999) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 85 * (7 : ZMod 3131119589999) ^ 85) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 943063302254 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 3131119589999) ^ 343 = 1079001022439 := by
        calc
          (7 : ZMod 3131119589999) ^ 343 = (7 : ZMod 3131119589999) ^ (171 + 171 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 171 * (7 : ZMod 3131119589999) ^ 171) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1079001022439 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 3131119589999) ^ 686 = 2022041862308 := by
        calc
          (7 : ZMod 3131119589999) ^ 686 = (7 : ZMod 3131119589999) ^ (343 + 343) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 343 * (7 : ZMod 3131119589999) ^ 343 := by rw [pow_add]
          _ = 2022041862308 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 3131119589999) ^ 1372 = 881388499853 := by
        calc
          (7 : ZMod 3131119589999) ^ 1372 = (7 : ZMod 3131119589999) ^ (686 + 686) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 686 * (7 : ZMod 3131119589999) ^ 686 := by rw [pow_add]
          _ = 881388499853 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 3131119589999) ^ 2744 = 1698902545845 := by
        calc
          (7 : ZMod 3131119589999) ^ 2744 = (7 : ZMod 3131119589999) ^ (1372 + 1372) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1372 * (7 : ZMod 3131119589999) ^ 1372 := by rw [pow_add]
          _ = 1698902545845 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 3131119589999) ^ 5489 = 2585399423208 := by
        calc
          (7 : ZMod 3131119589999) ^ 5489 = (7 : ZMod 3131119589999) ^ (2744 + 2744 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 2744 * (7 : ZMod 3131119589999) ^ 2744) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2585399423208 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 3131119589999) ^ 10978 = 900971130800 := by
        calc
          (7 : ZMod 3131119589999) ^ 10978 = (7 : ZMod 3131119589999) ^ (5489 + 5489) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 5489 * (7 : ZMod 3131119589999) ^ 5489 := by rw [pow_add]
          _ = 900971130800 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 3131119589999) ^ 21956 = 2357941538051 := by
        calc
          (7 : ZMod 3131119589999) ^ 21956 = (7 : ZMod 3131119589999) ^ (10978 + 10978) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 10978 * (7 : ZMod 3131119589999) ^ 10978 := by rw [pow_add]
          _ = 2357941538051 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 3131119589999) ^ 43912 = 733306071182 := by
        calc
          (7 : ZMod 3131119589999) ^ 43912 = (7 : ZMod 3131119589999) ^ (21956 + 21956) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 21956 * (7 : ZMod 3131119589999) ^ 21956 := by rw [pow_add]
          _ = 733306071182 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 3131119589999) ^ 87825 = 3131011829910 := by
        calc
          (7 : ZMod 3131119589999) ^ 87825 = (7 : ZMod 3131119589999) ^ (43912 + 43912 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 43912 * (7 : ZMod 3131119589999) ^ 43912) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 3131011829910 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 3131119589999) ^ 175651 = 1792912641407 := by
        calc
          (7 : ZMod 3131119589999) ^ 175651 = (7 : ZMod 3131119589999) ^ (87825 + 87825 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 87825 * (7 : ZMod 3131119589999) ^ 87825) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1792912641407 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 3131119589999) ^ 351302 = 715458687324 := by
        calc
          (7 : ZMod 3131119589999) ^ 351302 = (7 : ZMod 3131119589999) ^ (175651 + 175651) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 175651 * (7 : ZMod 3131119589999) ^ 175651 := by rw [pow_add]
          _ = 715458687324 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 3131119589999) ^ 702604 = 1891011052271 := by
        calc
          (7 : ZMod 3131119589999) ^ 702604 = (7 : ZMod 3131119589999) ^ (351302 + 351302) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 351302 * (7 : ZMod 3131119589999) ^ 351302 := by rw [pow_add]
          _ = 1891011052271 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 3131119589999) ^ 1405208 = 560230595191 := by
        calc
          (7 : ZMod 3131119589999) ^ 1405208 = (7 : ZMod 3131119589999) ^ (702604 + 702604) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 702604 * (7 : ZMod 3131119589999) ^ 702604 := by rw [pow_add]
          _ = 560230595191 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 3131119589999) ^ 2810417 = 262195626003 := by
        calc
          (7 : ZMod 3131119589999) ^ 2810417 = (7 : ZMod 3131119589999) ^ (1405208 + 1405208 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 1405208 * (7 : ZMod 3131119589999) ^ 1405208) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 262195626003 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 3131119589999) ^ 5620834 = 2943382665270 := by
        calc
          (7 : ZMod 3131119589999) ^ 5620834 = (7 : ZMod 3131119589999) ^ (2810417 + 2810417) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 2810417 * (7 : ZMod 3131119589999) ^ 2810417 := by rw [pow_add]
          _ = 2943382665270 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 3131119589999) ^ 11241669 = 763260025119 := by
        calc
          (7 : ZMod 3131119589999) ^ 11241669 = (7 : ZMod 3131119589999) ^ (5620834 + 5620834 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 5620834 * (7 : ZMod 3131119589999) ^ 5620834) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 763260025119 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 3131119589999) ^ 22483338 = 2643134252177 := by
        calc
          (7 : ZMod 3131119589999) ^ 22483338 = (7 : ZMod 3131119589999) ^ (11241669 + 11241669) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 11241669 * (7 : ZMod 3131119589999) ^ 11241669 := by rw [pow_add]
          _ = 2643134252177 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 3131119589999) ^ 44966676 = 1759611503087 := by
        calc
          (7 : ZMod 3131119589999) ^ 44966676 = (7 : ZMod 3131119589999) ^ (22483338 + 22483338) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 22483338 * (7 : ZMod 3131119589999) ^ 22483338 := by rw [pow_add]
          _ = 1759611503087 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 3131119589999) ^ 89933352 = 1950790265183 := by
        calc
          (7 : ZMod 3131119589999) ^ 89933352 = (7 : ZMod 3131119589999) ^ (44966676 + 44966676) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 44966676 * (7 : ZMod 3131119589999) ^ 44966676 := by rw [pow_add]
          _ = 1950790265183 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 3131119589999) ^ 179866704 = 2535670011932 := by
        calc
          (7 : ZMod 3131119589999) ^ 179866704 = (7 : ZMod 3131119589999) ^ (89933352 + 89933352) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 89933352 * (7 : ZMod 3131119589999) ^ 89933352 := by rw [pow_add]
          _ = 2535670011932 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 3131119589999) ^ 359733408 = 2586835711003 := by
        calc
          (7 : ZMod 3131119589999) ^ 359733408 = (7 : ZMod 3131119589999) ^ (179866704 + 179866704) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 179866704 * (7 : ZMod 3131119589999) ^ 179866704 := by rw [pow_add]
          _ = 2586835711003 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 3131119589999) ^ 719466817 = 2610857068589 := by
        calc
          (7 : ZMod 3131119589999) ^ 719466817 = (7 : ZMod 3131119589999) ^ (359733408 + 359733408 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 359733408 * (7 : ZMod 3131119589999) ^ 359733408) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2610857068589 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 3131119589999) ^ 1438933635 = 808469117987 := by
        calc
          (7 : ZMod 3131119589999) ^ 1438933635 = (7 : ZMod 3131119589999) ^ (719466817 + 719466817 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 719466817 * (7 : ZMod 3131119589999) ^ 719466817) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 808469117987 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 3131119589999) ^ 2877867270 = 864637843585 := by
        calc
          (7 : ZMod 3131119589999) ^ 2877867270 = (7 : ZMod 3131119589999) ^ (1438933635 + 1438933635) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1438933635 * (7 : ZMod 3131119589999) ^ 1438933635 := by rw [pow_add]
          _ = 864637843585 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 3131119589999) ^ 5755734540 = 1809614740335 := by
        calc
          (7 : ZMod 3131119589999) ^ 5755734540 = (7 : ZMod 3131119589999) ^ (2877867270 + 2877867270) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 2877867270 * (7 : ZMod 3131119589999) ^ 2877867270 := by rw [pow_add]
          _ = 1809614740335 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 3131119589999) ^ 11511469080 = 1571700524437 := by
        calc
          (7 : ZMod 3131119589999) ^ 11511469080 = (7 : ZMod 3131119589999) ^ (5755734540 + 5755734540) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 5755734540 * (7 : ZMod 3131119589999) ^ 5755734540 := by rw [pow_add]
          _ = 1571700524437 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 3131119589999) ^ 23022938161 = 1830251899427 := by
        calc
          (7 : ZMod 3131119589999) ^ 23022938161 = (7 : ZMod 3131119589999) ^ (11511469080 + 11511469080 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 11511469080 * (7 : ZMod 3131119589999) ^ 11511469080) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 1830251899427 := by rw [factor_1_33]; decide
      have factor_1_35 : (7 : ZMod 3131119589999) ^ 46045876323 = 548146013058 := by
        calc
          (7 : ZMod 3131119589999) ^ 46045876323 = (7 : ZMod 3131119589999) ^ (23022938161 + 23022938161 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 23022938161 * (7 : ZMod 3131119589999) ^ 23022938161) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 548146013058 := by rw [factor_1_34]; decide
      have factor_1_36 : (7 : ZMod 3131119589999) ^ 92091752647 = 2511497898934 := by
        calc
          (7 : ZMod 3131119589999) ^ 92091752647 = (7 : ZMod 3131119589999) ^ (46045876323 + 46045876323 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 46045876323 * (7 : ZMod 3131119589999) ^ 46045876323) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 2511497898934 := by rw [factor_1_35]; decide
      have factor_1_37 : (7 : ZMod 3131119589999) ^ 184183505294 = 1444089168397 := by
        calc
          (7 : ZMod 3131119589999) ^ 184183505294 = (7 : ZMod 3131119589999) ^ (92091752647 + 92091752647) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 92091752647 * (7 : ZMod 3131119589999) ^ 92091752647 := by rw [pow_add]
          _ = 1444089168397 := by rw [factor_1_36]; decide
      change (7 : ZMod 3131119589999) ^ 184183505294 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (7 : ZMod 3131119589999) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 3131119589999) ^ 2 = 49 := by
        calc
          (7 : ZMod 3131119589999) ^ 2 = (7 : ZMod 3131119589999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 1 * (7 : ZMod 3131119589999) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 3131119589999) ^ 4 = 2401 := by
        calc
          (7 : ZMod 3131119589999) ^ 4 = (7 : ZMod 3131119589999) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 2 * (7 : ZMod 3131119589999) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 3131119589999) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 3131119589999) ^ 8 = (7 : ZMod 3131119589999) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 4 * (7 : ZMod 3131119589999) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 3131119589999) ^ 17 = 927664327281 := by
        calc
          (7 : ZMod 3131119589999) ^ 17 = (7 : ZMod 3131119589999) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = ((7 : ZMod 3131119589999) ^ 8 * (7 : ZMod 3131119589999) ^ 8) * (7 : ZMod 3131119589999) := by rw [pow_succ, pow_add]
          _ = 927664327281 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 3131119589999) ^ 34 = 2940400323054 := by
        calc
          (7 : ZMod 3131119589999) ^ 34 = (7 : ZMod 3131119589999) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 3131119589999) ^ n) (by norm_num)
          _ = (7 : ZMod 3131119589999) ^ 17 * (7 : ZMod 3131119589999) ^ 17 := by rw [pow_add]
          _ = 2940400323054 := by rw [factor_2_4]; decide
      change (7 : ZMod 3131119589999) ^ 34 ≠ 1
      rw [factor_2_5]
      decide

#print axioms prime_lucas_3131119589999

end TotientTailPeriodKiller
end Erdos249257
