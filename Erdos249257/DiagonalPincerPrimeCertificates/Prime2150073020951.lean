import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2150073020951 : Nat.Prime 2150073020951 := by
  apply lucas_primality 2150073020951 (7 : ZMod 2150073020951)
  ·
      have fermat_0 : (7 : ZMod 2150073020951) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 2150073020951) ^ 3 = 343 := by
        calc
          (7 : ZMod 2150073020951) ^ 3 = (7 : ZMod 2150073020951) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1 * (7 : ZMod 2150073020951) ^ 1) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 2150073020951) ^ 7 = 823543 := by
        calc
          (7 : ZMod 2150073020951) ^ 7 = (7 : ZMod 2150073020951) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 3 * (7 : ZMod 2150073020951) ^ 3) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 2150073020951) ^ 15 = 447415468041 := by
        calc
          (7 : ZMod 2150073020951) ^ 15 = (7 : ZMod 2150073020951) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 7 * (7 : ZMod 2150073020951) ^ 7) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 447415468041 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 2150073020951) ^ 31 = 85139089438 := by
        calc
          (7 : ZMod 2150073020951) ^ 31 = (7 : ZMod 2150073020951) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 15 * (7 : ZMod 2150073020951) ^ 15) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 85139089438 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 2150073020951) ^ 62 = 1459641666513 := by
        calc
          (7 : ZMod 2150073020951) ^ 62 = (7 : ZMod 2150073020951) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 31 * (7 : ZMod 2150073020951) ^ 31 := by rw [pow_add]
          _ = 1459641666513 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 2150073020951) ^ 125 = 158532913107 := by
        calc
          (7 : ZMod 2150073020951) ^ 125 = (7 : ZMod 2150073020951) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 62 * (7 : ZMod 2150073020951) ^ 62) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 158532913107 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 2150073020951) ^ 250 = 1309783424288 := by
        calc
          (7 : ZMod 2150073020951) ^ 250 = (7 : ZMod 2150073020951) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 125 * (7 : ZMod 2150073020951) ^ 125 := by rw [pow_add]
          _ = 1309783424288 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 2150073020951) ^ 500 = 1018329408982 := by
        calc
          (7 : ZMod 2150073020951) ^ 500 = (7 : ZMod 2150073020951) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 250 * (7 : ZMod 2150073020951) ^ 250 := by rw [pow_add]
          _ = 1018329408982 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 2150073020951) ^ 1001 = 759717191759 := by
        calc
          (7 : ZMod 2150073020951) ^ 1001 = (7 : ZMod 2150073020951) ^ (500 + 500 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 500 * (7 : ZMod 2150073020951) ^ 500) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 759717191759 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 2150073020951) ^ 2002 = 839425031003 := by
        calc
          (7 : ZMod 2150073020951) ^ 2002 = (7 : ZMod 2150073020951) ^ (1001 + 1001) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 1001 * (7 : ZMod 2150073020951) ^ 1001 := by rw [pow_add]
          _ = 839425031003 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 2150073020951) ^ 4004 = 1521594505763 := by
        calc
          (7 : ZMod 2150073020951) ^ 4004 = (7 : ZMod 2150073020951) ^ (2002 + 2002) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 2002 * (7 : ZMod 2150073020951) ^ 2002 := by rw [pow_add]
          _ = 1521594505763 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 2150073020951) ^ 8009 = 353770257931 := by
        calc
          (7 : ZMod 2150073020951) ^ 8009 = (7 : ZMod 2150073020951) ^ (4004 + 4004 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 4004 * (7 : ZMod 2150073020951) ^ 4004) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 353770257931 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 2150073020951) ^ 16019 = 961194369007 := by
        calc
          (7 : ZMod 2150073020951) ^ 16019 = (7 : ZMod 2150073020951) ^ (8009 + 8009 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 8009 * (7 : ZMod 2150073020951) ^ 8009) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 961194369007 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 2150073020951) ^ 32038 = 93694352344 := by
        calc
          (7 : ZMod 2150073020951) ^ 32038 = (7 : ZMod 2150073020951) ^ (16019 + 16019) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 16019 * (7 : ZMod 2150073020951) ^ 16019 := by rw [pow_add]
          _ = 93694352344 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 2150073020951) ^ 64077 = 1422970433788 := by
        calc
          (7 : ZMod 2150073020951) ^ 64077 = (7 : ZMod 2150073020951) ^ (32038 + 32038 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 32038 * (7 : ZMod 2150073020951) ^ 32038) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1422970433788 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 2150073020951) ^ 128154 = 129464653380 := by
        calc
          (7 : ZMod 2150073020951) ^ 128154 = (7 : ZMod 2150073020951) ^ (64077 + 64077) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 64077 * (7 : ZMod 2150073020951) ^ 64077 := by rw [pow_add]
          _ = 129464653380 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 2150073020951) ^ 256308 = 1961601252389 := by
        calc
          (7 : ZMod 2150073020951) ^ 256308 = (7 : ZMod 2150073020951) ^ (128154 + 128154) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 128154 * (7 : ZMod 2150073020951) ^ 128154 := by rw [pow_add]
          _ = 1961601252389 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 2150073020951) ^ 512617 = 435578762237 := by
        calc
          (7 : ZMod 2150073020951) ^ 512617 = (7 : ZMod 2150073020951) ^ (256308 + 256308 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 256308 * (7 : ZMod 2150073020951) ^ 256308) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 435578762237 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 2150073020951) ^ 1025234 = 342729935669 := by
        calc
          (7 : ZMod 2150073020951) ^ 1025234 = (7 : ZMod 2150073020951) ^ (512617 + 512617) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 512617 * (7 : ZMod 2150073020951) ^ 512617 := by rw [pow_add]
          _ = 342729935669 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 2150073020951) ^ 2050469 = 1597111442863 := by
        calc
          (7 : ZMod 2150073020951) ^ 2050469 = (7 : ZMod 2150073020951) ^ (1025234 + 1025234 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1025234 * (7 : ZMod 2150073020951) ^ 1025234) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1597111442863 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 2150073020951) ^ 4100938 = 1988875321853 := by
        calc
          (7 : ZMod 2150073020951) ^ 4100938 = (7 : ZMod 2150073020951) ^ (2050469 + 2050469) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 2050469 * (7 : ZMod 2150073020951) ^ 2050469 := by rw [pow_add]
          _ = 1988875321853 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 2150073020951) ^ 8201877 = 563277970557 := by
        calc
          (7 : ZMod 2150073020951) ^ 8201877 = (7 : ZMod 2150073020951) ^ (4100938 + 4100938 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 4100938 * (7 : ZMod 2150073020951) ^ 4100938) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 563277970557 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 2150073020951) ^ 16403755 = 1802358928726 := by
        calc
          (7 : ZMod 2150073020951) ^ 16403755 = (7 : ZMod 2150073020951) ^ (8201877 + 8201877 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 8201877 * (7 : ZMod 2150073020951) ^ 8201877) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1802358928726 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 2150073020951) ^ 32807510 = 1472231645631 := by
        calc
          (7 : ZMod 2150073020951) ^ 32807510 = (7 : ZMod 2150073020951) ^ (16403755 + 16403755) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 16403755 * (7 : ZMod 2150073020951) ^ 16403755 := by rw [pow_add]
          _ = 1472231645631 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 2150073020951) ^ 65615021 = 1845020523616 := by
        calc
          (7 : ZMod 2150073020951) ^ 65615021 = (7 : ZMod 2150073020951) ^ (32807510 + 32807510 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 32807510 * (7 : ZMod 2150073020951) ^ 32807510) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1845020523616 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 2150073020951) ^ 131230042 = 1795073327249 := by
        calc
          (7 : ZMod 2150073020951) ^ 131230042 = (7 : ZMod 2150073020951) ^ (65615021 + 65615021) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 65615021 * (7 : ZMod 2150073020951) ^ 65615021 := by rw [pow_add]
          _ = 1795073327249 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 2150073020951) ^ 262460085 = 1260328110778 := by
        calc
          (7 : ZMod 2150073020951) ^ 262460085 = (7 : ZMod 2150073020951) ^ (131230042 + 131230042 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 131230042 * (7 : ZMod 2150073020951) ^ 131230042) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1260328110778 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 2150073020951) ^ 524920171 = 1533427117753 := by
        calc
          (7 : ZMod 2150073020951) ^ 524920171 = (7 : ZMod 2150073020951) ^ (262460085 + 262460085 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 262460085 * (7 : ZMod 2150073020951) ^ 262460085) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1533427117753 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 2150073020951) ^ 1049840342 = 2128734707502 := by
        calc
          (7 : ZMod 2150073020951) ^ 1049840342 = (7 : ZMod 2150073020951) ^ (524920171 + 524920171) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 524920171 * (7 : ZMod 2150073020951) ^ 524920171 := by rw [pow_add]
          _ = 2128734707502 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 2150073020951) ^ 2099680684 = 1860800131116 := by
        calc
          (7 : ZMod 2150073020951) ^ 2099680684 = (7 : ZMod 2150073020951) ^ (1049840342 + 1049840342) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 1049840342 * (7 : ZMod 2150073020951) ^ 1049840342 := by rw [pow_add]
          _ = 1860800131116 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 2150073020951) ^ 4199361369 = 2012493980986 := by
        calc
          (7 : ZMod 2150073020951) ^ 4199361369 = (7 : ZMod 2150073020951) ^ (2099680684 + 2099680684 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 2099680684 * (7 : ZMod 2150073020951) ^ 2099680684) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2012493980986 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 2150073020951) ^ 8398722738 = 662778832248 := by
        calc
          (7 : ZMod 2150073020951) ^ 8398722738 = (7 : ZMod 2150073020951) ^ (4199361369 + 4199361369) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 4199361369 * (7 : ZMod 2150073020951) ^ 4199361369 := by rw [pow_add]
          _ = 662778832248 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 2150073020951) ^ 16797445476 = 866704452993 := by
        calc
          (7 : ZMod 2150073020951) ^ 16797445476 = (7 : ZMod 2150073020951) ^ (8398722738 + 8398722738) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 8398722738 * (7 : ZMod 2150073020951) ^ 8398722738 := by rw [pow_add]
          _ = 866704452993 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 2150073020951) ^ 33594890952 = 1691513761796 := by
        calc
          (7 : ZMod 2150073020951) ^ 33594890952 = (7 : ZMod 2150073020951) ^ (16797445476 + 16797445476) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 16797445476 * (7 : ZMod 2150073020951) ^ 16797445476 := by rw [pow_add]
          _ = 1691513761796 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 2150073020951) ^ 67189781904 = 261842307271 := by
        calc
          (7 : ZMod 2150073020951) ^ 67189781904 = (7 : ZMod 2150073020951) ^ (33594890952 + 33594890952) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 33594890952 * (7 : ZMod 2150073020951) ^ 33594890952 := by rw [pow_add]
          _ = 261842307271 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 2150073020951) ^ 134379563809 = 459713404004 := by
        calc
          (7 : ZMod 2150073020951) ^ 134379563809 = (7 : ZMod 2150073020951) ^ (67189781904 + 67189781904 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 67189781904 * (7 : ZMod 2150073020951) ^ 67189781904) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 459713404004 := by rw [fermat_35]; decide
      have fermat_37 : (7 : ZMod 2150073020951) ^ 268759127618 = 1194591057475 := by
        calc
          (7 : ZMod 2150073020951) ^ 268759127618 = (7 : ZMod 2150073020951) ^ (134379563809 + 134379563809) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 134379563809 * (7 : ZMod 2150073020951) ^ 134379563809 := by rw [pow_add]
          _ = 1194591057475 := by rw [fermat_36]; decide
      have fermat_38 : (7 : ZMod 2150073020951) ^ 537518255237 = 1906301121311 := by
        calc
          (7 : ZMod 2150073020951) ^ 537518255237 = (7 : ZMod 2150073020951) ^ (268759127618 + 268759127618 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 268759127618 * (7 : ZMod 2150073020951) ^ 268759127618) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1906301121311 := by rw [fermat_37]; decide
      have fermat_39 : (7 : ZMod 2150073020951) ^ 1075036510475 = 2150073020950 := by
        calc
          (7 : ZMod 2150073020951) ^ 1075036510475 = (7 : ZMod 2150073020951) ^ (537518255237 + 537518255237 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 537518255237 * (7 : ZMod 2150073020951) ^ 537518255237) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2150073020950 := by rw [fermat_38]; decide
      have fermat_40 : (7 : ZMod 2150073020951) ^ 2150073020950 = 1 := by
        calc
          (7 : ZMod 2150073020951) ^ 2150073020950 = (7 : ZMod 2150073020951) ^ (1075036510475 + 1075036510475) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 1075036510475 * (7 : ZMod 2150073020951) ^ 1075036510475 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (2411, 1), (17835529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (2411, 1), (17835529, 1)] : List FactorBlock).map factorBlockValue).prod = 2150073020951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 2150073020951) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 2150073020951) ^ 3 = 343 := by
        calc
          (7 : ZMod 2150073020951) ^ 3 = (7 : ZMod 2150073020951) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1 * (7 : ZMod 2150073020951) ^ 1) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 2150073020951) ^ 7 = 823543 := by
        calc
          (7 : ZMod 2150073020951) ^ 7 = (7 : ZMod 2150073020951) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 3 * (7 : ZMod 2150073020951) ^ 3) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 2150073020951) ^ 15 = 447415468041 := by
        calc
          (7 : ZMod 2150073020951) ^ 15 = (7 : ZMod 2150073020951) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 7 * (7 : ZMod 2150073020951) ^ 7) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 447415468041 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 2150073020951) ^ 31 = 85139089438 := by
        calc
          (7 : ZMod 2150073020951) ^ 31 = (7 : ZMod 2150073020951) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 15 * (7 : ZMod 2150073020951) ^ 15) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 85139089438 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 2150073020951) ^ 62 = 1459641666513 := by
        calc
          (7 : ZMod 2150073020951) ^ 62 = (7 : ZMod 2150073020951) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 31 * (7 : ZMod 2150073020951) ^ 31 := by rw [pow_add]
          _ = 1459641666513 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 2150073020951) ^ 125 = 158532913107 := by
        calc
          (7 : ZMod 2150073020951) ^ 125 = (7 : ZMod 2150073020951) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 62 * (7 : ZMod 2150073020951) ^ 62) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 158532913107 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 2150073020951) ^ 250 = 1309783424288 := by
        calc
          (7 : ZMod 2150073020951) ^ 250 = (7 : ZMod 2150073020951) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 125 * (7 : ZMod 2150073020951) ^ 125 := by rw [pow_add]
          _ = 1309783424288 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 2150073020951) ^ 500 = 1018329408982 := by
        calc
          (7 : ZMod 2150073020951) ^ 500 = (7 : ZMod 2150073020951) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 250 * (7 : ZMod 2150073020951) ^ 250 := by rw [pow_add]
          _ = 1018329408982 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 2150073020951) ^ 1001 = 759717191759 := by
        calc
          (7 : ZMod 2150073020951) ^ 1001 = (7 : ZMod 2150073020951) ^ (500 + 500 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 500 * (7 : ZMod 2150073020951) ^ 500) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 759717191759 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 2150073020951) ^ 2002 = 839425031003 := by
        calc
          (7 : ZMod 2150073020951) ^ 2002 = (7 : ZMod 2150073020951) ^ (1001 + 1001) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 1001 * (7 : ZMod 2150073020951) ^ 1001 := by rw [pow_add]
          _ = 839425031003 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 2150073020951) ^ 4004 = 1521594505763 := by
        calc
          (7 : ZMod 2150073020951) ^ 4004 = (7 : ZMod 2150073020951) ^ (2002 + 2002) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 2002 * (7 : ZMod 2150073020951) ^ 2002 := by rw [pow_add]
          _ = 1521594505763 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 2150073020951) ^ 8009 = 353770257931 := by
        calc
          (7 : ZMod 2150073020951) ^ 8009 = (7 : ZMod 2150073020951) ^ (4004 + 4004 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 4004 * (7 : ZMod 2150073020951) ^ 4004) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 353770257931 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 2150073020951) ^ 16019 = 961194369007 := by
        calc
          (7 : ZMod 2150073020951) ^ 16019 = (7 : ZMod 2150073020951) ^ (8009 + 8009 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 8009 * (7 : ZMod 2150073020951) ^ 8009) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 961194369007 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 2150073020951) ^ 32038 = 93694352344 := by
        calc
          (7 : ZMod 2150073020951) ^ 32038 = (7 : ZMod 2150073020951) ^ (16019 + 16019) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 16019 * (7 : ZMod 2150073020951) ^ 16019 := by rw [pow_add]
          _ = 93694352344 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 2150073020951) ^ 64077 = 1422970433788 := by
        calc
          (7 : ZMod 2150073020951) ^ 64077 = (7 : ZMod 2150073020951) ^ (32038 + 32038 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 32038 * (7 : ZMod 2150073020951) ^ 32038) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1422970433788 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 2150073020951) ^ 128154 = 129464653380 := by
        calc
          (7 : ZMod 2150073020951) ^ 128154 = (7 : ZMod 2150073020951) ^ (64077 + 64077) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 64077 * (7 : ZMod 2150073020951) ^ 64077 := by rw [pow_add]
          _ = 129464653380 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 2150073020951) ^ 256308 = 1961601252389 := by
        calc
          (7 : ZMod 2150073020951) ^ 256308 = (7 : ZMod 2150073020951) ^ (128154 + 128154) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 128154 * (7 : ZMod 2150073020951) ^ 128154 := by rw [pow_add]
          _ = 1961601252389 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 2150073020951) ^ 512617 = 435578762237 := by
        calc
          (7 : ZMod 2150073020951) ^ 512617 = (7 : ZMod 2150073020951) ^ (256308 + 256308 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 256308 * (7 : ZMod 2150073020951) ^ 256308) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 435578762237 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 2150073020951) ^ 1025234 = 342729935669 := by
        calc
          (7 : ZMod 2150073020951) ^ 1025234 = (7 : ZMod 2150073020951) ^ (512617 + 512617) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 512617 * (7 : ZMod 2150073020951) ^ 512617 := by rw [pow_add]
          _ = 342729935669 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 2150073020951) ^ 2050469 = 1597111442863 := by
        calc
          (7 : ZMod 2150073020951) ^ 2050469 = (7 : ZMod 2150073020951) ^ (1025234 + 1025234 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1025234 * (7 : ZMod 2150073020951) ^ 1025234) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1597111442863 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 2150073020951) ^ 4100938 = 1988875321853 := by
        calc
          (7 : ZMod 2150073020951) ^ 4100938 = (7 : ZMod 2150073020951) ^ (2050469 + 2050469) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 2050469 * (7 : ZMod 2150073020951) ^ 2050469 := by rw [pow_add]
          _ = 1988875321853 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 2150073020951) ^ 8201877 = 563277970557 := by
        calc
          (7 : ZMod 2150073020951) ^ 8201877 = (7 : ZMod 2150073020951) ^ (4100938 + 4100938 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 4100938 * (7 : ZMod 2150073020951) ^ 4100938) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 563277970557 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 2150073020951) ^ 16403755 = 1802358928726 := by
        calc
          (7 : ZMod 2150073020951) ^ 16403755 = (7 : ZMod 2150073020951) ^ (8201877 + 8201877 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 8201877 * (7 : ZMod 2150073020951) ^ 8201877) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1802358928726 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 2150073020951) ^ 32807510 = 1472231645631 := by
        calc
          (7 : ZMod 2150073020951) ^ 32807510 = (7 : ZMod 2150073020951) ^ (16403755 + 16403755) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 16403755 * (7 : ZMod 2150073020951) ^ 16403755 := by rw [pow_add]
          _ = 1472231645631 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 2150073020951) ^ 65615021 = 1845020523616 := by
        calc
          (7 : ZMod 2150073020951) ^ 65615021 = (7 : ZMod 2150073020951) ^ (32807510 + 32807510 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 32807510 * (7 : ZMod 2150073020951) ^ 32807510) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1845020523616 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 2150073020951) ^ 131230042 = 1795073327249 := by
        calc
          (7 : ZMod 2150073020951) ^ 131230042 = (7 : ZMod 2150073020951) ^ (65615021 + 65615021) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 65615021 * (7 : ZMod 2150073020951) ^ 65615021 := by rw [pow_add]
          _ = 1795073327249 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 2150073020951) ^ 262460085 = 1260328110778 := by
        calc
          (7 : ZMod 2150073020951) ^ 262460085 = (7 : ZMod 2150073020951) ^ (131230042 + 131230042 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 131230042 * (7 : ZMod 2150073020951) ^ 131230042) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1260328110778 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 2150073020951) ^ 524920171 = 1533427117753 := by
        calc
          (7 : ZMod 2150073020951) ^ 524920171 = (7 : ZMod 2150073020951) ^ (262460085 + 262460085 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 262460085 * (7 : ZMod 2150073020951) ^ 262460085) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1533427117753 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 2150073020951) ^ 1049840342 = 2128734707502 := by
        calc
          (7 : ZMod 2150073020951) ^ 1049840342 = (7 : ZMod 2150073020951) ^ (524920171 + 524920171) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 524920171 * (7 : ZMod 2150073020951) ^ 524920171 := by rw [pow_add]
          _ = 2128734707502 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 2150073020951) ^ 2099680684 = 1860800131116 := by
        calc
          (7 : ZMod 2150073020951) ^ 2099680684 = (7 : ZMod 2150073020951) ^ (1049840342 + 1049840342) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 1049840342 * (7 : ZMod 2150073020951) ^ 1049840342 := by rw [pow_add]
          _ = 1860800131116 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 2150073020951) ^ 4199361369 = 2012493980986 := by
        calc
          (7 : ZMod 2150073020951) ^ 4199361369 = (7 : ZMod 2150073020951) ^ (2099680684 + 2099680684 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 2099680684 * (7 : ZMod 2150073020951) ^ 2099680684) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2012493980986 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 2150073020951) ^ 8398722738 = 662778832248 := by
        calc
          (7 : ZMod 2150073020951) ^ 8398722738 = (7 : ZMod 2150073020951) ^ (4199361369 + 4199361369) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 4199361369 * (7 : ZMod 2150073020951) ^ 4199361369 := by rw [pow_add]
          _ = 662778832248 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 2150073020951) ^ 16797445476 = 866704452993 := by
        calc
          (7 : ZMod 2150073020951) ^ 16797445476 = (7 : ZMod 2150073020951) ^ (8398722738 + 8398722738) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 8398722738 * (7 : ZMod 2150073020951) ^ 8398722738 := by rw [pow_add]
          _ = 866704452993 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 2150073020951) ^ 33594890952 = 1691513761796 := by
        calc
          (7 : ZMod 2150073020951) ^ 33594890952 = (7 : ZMod 2150073020951) ^ (16797445476 + 16797445476) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 16797445476 * (7 : ZMod 2150073020951) ^ 16797445476 := by rw [pow_add]
          _ = 1691513761796 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 2150073020951) ^ 67189781904 = 261842307271 := by
        calc
          (7 : ZMod 2150073020951) ^ 67189781904 = (7 : ZMod 2150073020951) ^ (33594890952 + 33594890952) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 33594890952 * (7 : ZMod 2150073020951) ^ 33594890952 := by rw [pow_add]
          _ = 261842307271 := by rw [factor_0_34]; decide
      have factor_0_36 : (7 : ZMod 2150073020951) ^ 134379563809 = 459713404004 := by
        calc
          (7 : ZMod 2150073020951) ^ 134379563809 = (7 : ZMod 2150073020951) ^ (67189781904 + 67189781904 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 67189781904 * (7 : ZMod 2150073020951) ^ 67189781904) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 459713404004 := by rw [factor_0_35]; decide
      have factor_0_37 : (7 : ZMod 2150073020951) ^ 268759127618 = 1194591057475 := by
        calc
          (7 : ZMod 2150073020951) ^ 268759127618 = (7 : ZMod 2150073020951) ^ (134379563809 + 134379563809) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 134379563809 * (7 : ZMod 2150073020951) ^ 134379563809 := by rw [pow_add]
          _ = 1194591057475 := by rw [factor_0_36]; decide
      have factor_0_38 : (7 : ZMod 2150073020951) ^ 537518255237 = 1906301121311 := by
        calc
          (7 : ZMod 2150073020951) ^ 537518255237 = (7 : ZMod 2150073020951) ^ (268759127618 + 268759127618 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 268759127618 * (7 : ZMod 2150073020951) ^ 268759127618) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1906301121311 := by rw [factor_0_37]; decide
      have factor_0_39 : (7 : ZMod 2150073020951) ^ 1075036510475 = 2150073020950 := by
        calc
          (7 : ZMod 2150073020951) ^ 1075036510475 = (7 : ZMod 2150073020951) ^ (537518255237 + 537518255237 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 537518255237 * (7 : ZMod 2150073020951) ^ 537518255237) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2150073020950 := by rw [factor_0_38]; decide
      change (7 : ZMod 2150073020951) ^ 1075036510475 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (7 : ZMod 2150073020951) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 2150073020951) ^ 3 = 343 := by
        calc
          (7 : ZMod 2150073020951) ^ 3 = (7 : ZMod 2150073020951) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1 * (7 : ZMod 2150073020951) ^ 1) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 2150073020951) ^ 6 = 117649 := by
        calc
          (7 : ZMod 2150073020951) ^ 6 = (7 : ZMod 2150073020951) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 3 * (7 : ZMod 2150073020951) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 2150073020951) ^ 12 = 13841287201 := by
        calc
          (7 : ZMod 2150073020951) ^ 12 = (7 : ZMod 2150073020951) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 6 * (7 : ZMod 2150073020951) ^ 6 := by rw [pow_add]
          _ = 13841287201 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 2150073020951) ^ 25 = 884836850245 := by
        calc
          (7 : ZMod 2150073020951) ^ 25 = (7 : ZMod 2150073020951) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 12 * (7 : ZMod 2150073020951) ^ 12) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 884836850245 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 2150073020951) ^ 50 = 2076061178514 := by
        calc
          (7 : ZMod 2150073020951) ^ 50 = (7 : ZMod 2150073020951) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 25 * (7 : ZMod 2150073020951) ^ 25 := by rw [pow_add]
          _ = 2076061178514 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 2150073020951) ^ 100 = 892223566538 := by
        calc
          (7 : ZMod 2150073020951) ^ 100 = (7 : ZMod 2150073020951) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 50 * (7 : ZMod 2150073020951) ^ 50 := by rw [pow_add]
          _ = 892223566538 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 2150073020951) ^ 200 = 991806364254 := by
        calc
          (7 : ZMod 2150073020951) ^ 200 = (7 : ZMod 2150073020951) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 100 * (7 : ZMod 2150073020951) ^ 100 := by rw [pow_add]
          _ = 991806364254 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 2150073020951) ^ 400 = 1628298239914 := by
        calc
          (7 : ZMod 2150073020951) ^ 400 = (7 : ZMod 2150073020951) ^ (200 + 200) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 200 * (7 : ZMod 2150073020951) ^ 200 := by rw [pow_add]
          _ = 1628298239914 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 2150073020951) ^ 800 = 155589635759 := by
        calc
          (7 : ZMod 2150073020951) ^ 800 = (7 : ZMod 2150073020951) ^ (400 + 400) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 400 * (7 : ZMod 2150073020951) ^ 400 := by rw [pow_add]
          _ = 155589635759 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 2150073020951) ^ 1601 = 1787905633888 := by
        calc
          (7 : ZMod 2150073020951) ^ 1601 = (7 : ZMod 2150073020951) ^ (800 + 800 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 800 * (7 : ZMod 2150073020951) ^ 800) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1787905633888 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 2150073020951) ^ 3203 = 465906518738 := by
        calc
          (7 : ZMod 2150073020951) ^ 3203 = (7 : ZMod 2150073020951) ^ (1601 + 1601 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1601 * (7 : ZMod 2150073020951) ^ 1601) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 465906518738 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 2150073020951) ^ 6407 = 1977593387325 := by
        calc
          (7 : ZMod 2150073020951) ^ 6407 = (7 : ZMod 2150073020951) ^ (3203 + 3203 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 3203 * (7 : ZMod 2150073020951) ^ 3203) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1977593387325 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 2150073020951) ^ 12815 = 2024040845874 := by
        calc
          (7 : ZMod 2150073020951) ^ 12815 = (7 : ZMod 2150073020951) ^ (6407 + 6407 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 6407 * (7 : ZMod 2150073020951) ^ 6407) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2024040845874 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 2150073020951) ^ 25630 = 2010779055844 := by
        calc
          (7 : ZMod 2150073020951) ^ 25630 = (7 : ZMod 2150073020951) ^ (12815 + 12815) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 12815 * (7 : ZMod 2150073020951) ^ 12815 := by rw [pow_add]
          _ = 2010779055844 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 2150073020951) ^ 51261 = 1327893434292 := by
        calc
          (7 : ZMod 2150073020951) ^ 51261 = (7 : ZMod 2150073020951) ^ (25630 + 25630 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 25630 * (7 : ZMod 2150073020951) ^ 25630) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1327893434292 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 2150073020951) ^ 102523 = 1955964888957 := by
        calc
          (7 : ZMod 2150073020951) ^ 102523 = (7 : ZMod 2150073020951) ^ (51261 + 51261 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 51261 * (7 : ZMod 2150073020951) ^ 51261) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1955964888957 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 2150073020951) ^ 205046 = 540370868289 := by
        calc
          (7 : ZMod 2150073020951) ^ 205046 = (7 : ZMod 2150073020951) ^ (102523 + 102523) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 102523 * (7 : ZMod 2150073020951) ^ 102523 := by rw [pow_add]
          _ = 540370868289 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 2150073020951) ^ 410093 = 190290682837 := by
        calc
          (7 : ZMod 2150073020951) ^ 410093 = (7 : ZMod 2150073020951) ^ (205046 + 205046 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 205046 * (7 : ZMod 2150073020951) ^ 205046) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 190290682837 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 2150073020951) ^ 820187 = 924176265750 := by
        calc
          (7 : ZMod 2150073020951) ^ 820187 = (7 : ZMod 2150073020951) ^ (410093 + 410093 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 410093 * (7 : ZMod 2150073020951) ^ 410093) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 924176265750 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 2150073020951) ^ 1640375 = 497714862394 := by
        calc
          (7 : ZMod 2150073020951) ^ 1640375 = (7 : ZMod 2150073020951) ^ (820187 + 820187 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 820187 * (7 : ZMod 2150073020951) ^ 820187) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 497714862394 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 2150073020951) ^ 3280751 = 677517133252 := by
        calc
          (7 : ZMod 2150073020951) ^ 3280751 = (7 : ZMod 2150073020951) ^ (1640375 + 1640375 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1640375 * (7 : ZMod 2150073020951) ^ 1640375) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 677517133252 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 2150073020951) ^ 6561502 = 18176112589 := by
        calc
          (7 : ZMod 2150073020951) ^ 6561502 = (7 : ZMod 2150073020951) ^ (3280751 + 3280751) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 3280751 * (7 : ZMod 2150073020951) ^ 3280751 := by rw [pow_add]
          _ = 18176112589 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 2150073020951) ^ 13123004 = 1309523811328 := by
        calc
          (7 : ZMod 2150073020951) ^ 13123004 = (7 : ZMod 2150073020951) ^ (6561502 + 6561502) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 6561502 * (7 : ZMod 2150073020951) ^ 6561502 := by rw [pow_add]
          _ = 1309523811328 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 2150073020951) ^ 26246008 = 2052103466390 := by
        calc
          (7 : ZMod 2150073020951) ^ 26246008 = (7 : ZMod 2150073020951) ^ (13123004 + 13123004) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 13123004 * (7 : ZMod 2150073020951) ^ 13123004 := by rw [pow_add]
          _ = 2052103466390 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 2150073020951) ^ 52492017 = 1945111140204 := by
        calc
          (7 : ZMod 2150073020951) ^ 52492017 = (7 : ZMod 2150073020951) ^ (26246008 + 26246008 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 26246008 * (7 : ZMod 2150073020951) ^ 26246008) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1945111140204 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 2150073020951) ^ 104984034 = 1144310074402 := by
        calc
          (7 : ZMod 2150073020951) ^ 104984034 = (7 : ZMod 2150073020951) ^ (52492017 + 52492017) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 52492017 * (7 : ZMod 2150073020951) ^ 52492017 := by rw [pow_add]
          _ = 1144310074402 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 2150073020951) ^ 209968068 = 83588729844 := by
        calc
          (7 : ZMod 2150073020951) ^ 209968068 = (7 : ZMod 2150073020951) ^ (104984034 + 104984034) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 104984034 * (7 : ZMod 2150073020951) ^ 104984034 := by rw [pow_add]
          _ = 83588729844 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 2150073020951) ^ 419936136 = 1260501740379 := by
        calc
          (7 : ZMod 2150073020951) ^ 419936136 = (7 : ZMod 2150073020951) ^ (209968068 + 209968068) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 209968068 * (7 : ZMod 2150073020951) ^ 209968068 := by rw [pow_add]
          _ = 1260501740379 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 2150073020951) ^ 839872273 = 1550205136722 := by
        calc
          (7 : ZMod 2150073020951) ^ 839872273 = (7 : ZMod 2150073020951) ^ (419936136 + 419936136 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 419936136 * (7 : ZMod 2150073020951) ^ 419936136) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1550205136722 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 2150073020951) ^ 1679744547 = 1525953564986 := by
        calc
          (7 : ZMod 2150073020951) ^ 1679744547 = (7 : ZMod 2150073020951) ^ (839872273 + 839872273 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 839872273 * (7 : ZMod 2150073020951) ^ 839872273) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1525953564986 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 2150073020951) ^ 3359489095 = 1485999209749 := by
        calc
          (7 : ZMod 2150073020951) ^ 3359489095 = (7 : ZMod 2150073020951) ^ (1679744547 + 1679744547 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1679744547 * (7 : ZMod 2150073020951) ^ 1679744547) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1485999209749 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 2150073020951) ^ 6718978190 = 2127971766084 := by
        calc
          (7 : ZMod 2150073020951) ^ 6718978190 = (7 : ZMod 2150073020951) ^ (3359489095 + 3359489095) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 3359489095 * (7 : ZMod 2150073020951) ^ 3359489095 := by rw [pow_add]
          _ = 2127971766084 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 2150073020951) ^ 13437956380 = 793075274365 := by
        calc
          (7 : ZMod 2150073020951) ^ 13437956380 = (7 : ZMod 2150073020951) ^ (6718978190 + 6718978190) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 6718978190 * (7 : ZMod 2150073020951) ^ 6718978190 := by rw [pow_add]
          _ = 793075274365 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 2150073020951) ^ 26875912761 = 2029128633861 := by
        calc
          (7 : ZMod 2150073020951) ^ 26875912761 = (7 : ZMod 2150073020951) ^ (13437956380 + 13437956380 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 13437956380 * (7 : ZMod 2150073020951) ^ 13437956380) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2029128633861 := by rw [factor_1_33]; decide
      have factor_1_35 : (7 : ZMod 2150073020951) ^ 53751825523 = 1205840483417 := by
        calc
          (7 : ZMod 2150073020951) ^ 53751825523 = (7 : ZMod 2150073020951) ^ (26875912761 + 26875912761 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 26875912761 * (7 : ZMod 2150073020951) ^ 26875912761) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1205840483417 := by rw [factor_1_34]; decide
      have factor_1_36 : (7 : ZMod 2150073020951) ^ 107503651047 = 990743326682 := by
        calc
          (7 : ZMod 2150073020951) ^ 107503651047 = (7 : ZMod 2150073020951) ^ (53751825523 + 53751825523 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 53751825523 * (7 : ZMod 2150073020951) ^ 53751825523) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 990743326682 := by rw [factor_1_35]; decide
      have factor_1_37 : (7 : ZMod 2150073020951) ^ 215007302095 = 120892881294 := by
        calc
          (7 : ZMod 2150073020951) ^ 215007302095 = (7 : ZMod 2150073020951) ^ (107503651047 + 107503651047 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 107503651047 * (7 : ZMod 2150073020951) ^ 107503651047) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 120892881294 := by rw [factor_1_36]; decide
      have factor_1_38 : (7 : ZMod 2150073020951) ^ 430014604190 = 2108407420155 := by
        calc
          (7 : ZMod 2150073020951) ^ 430014604190 = (7 : ZMod 2150073020951) ^ (215007302095 + 215007302095) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 215007302095 * (7 : ZMod 2150073020951) ^ 215007302095 := by rw [pow_add]
          _ = 2108407420155 := by rw [factor_1_37]; decide
      change (7 : ZMod 2150073020951) ^ 430014604190 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (7 : ZMod 2150073020951) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 2150073020951) ^ 3 = 343 := by
        calc
          (7 : ZMod 2150073020951) ^ 3 = (7 : ZMod 2150073020951) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1 * (7 : ZMod 2150073020951) ^ 1) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 2150073020951) ^ 6 = 117649 := by
        calc
          (7 : ZMod 2150073020951) ^ 6 = (7 : ZMod 2150073020951) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 3 * (7 : ZMod 2150073020951) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 2150073020951) ^ 13 = 96889010407 := by
        calc
          (7 : ZMod 2150073020951) ^ 13 = (7 : ZMod 2150073020951) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 6 * (7 : ZMod 2150073020951) ^ 6) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 96889010407 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 2150073020951) ^ 26 = 1893711909813 := by
        calc
          (7 : ZMod 2150073020951) ^ 26 = (7 : ZMod 2150073020951) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 13 * (7 : ZMod 2150073020951) ^ 13 := by rw [pow_add]
          _ = 1893711909813 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 2150073020951) ^ 53 = 414814295521 := by
        calc
          (7 : ZMod 2150073020951) ^ 53 = (7 : ZMod 2150073020951) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 26 * (7 : ZMod 2150073020951) ^ 26) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 414814295521 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 2150073020951) ^ 106 = 495423780391 := by
        calc
          (7 : ZMod 2150073020951) ^ 106 = (7 : ZMod 2150073020951) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 53 * (7 : ZMod 2150073020951) ^ 53 := by rw [pow_add]
          _ = 495423780391 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 2150073020951) ^ 212 = 1777399359758 := by
        calc
          (7 : ZMod 2150073020951) ^ 212 = (7 : ZMod 2150073020951) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 106 * (7 : ZMod 2150073020951) ^ 106 := by rw [pow_add]
          _ = 1777399359758 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 2150073020951) ^ 425 = 1806516601434 := by
        calc
          (7 : ZMod 2150073020951) ^ 425 = (7 : ZMod 2150073020951) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 212 * (7 : ZMod 2150073020951) ^ 212) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1806516601434 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 2150073020951) ^ 850 = 473424829381 := by
        calc
          (7 : ZMod 2150073020951) ^ 850 = (7 : ZMod 2150073020951) ^ (425 + 425) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 425 * (7 : ZMod 2150073020951) ^ 425 := by rw [pow_add]
          _ = 473424829381 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 2150073020951) ^ 1700 = 1328955850035 := by
        calc
          (7 : ZMod 2150073020951) ^ 1700 = (7 : ZMod 2150073020951) ^ (850 + 850) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 850 * (7 : ZMod 2150073020951) ^ 850 := by rw [pow_add]
          _ = 1328955850035 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 2150073020951) ^ 3401 = 2062902010332 := by
        calc
          (7 : ZMod 2150073020951) ^ 3401 = (7 : ZMod 2150073020951) ^ (1700 + 1700 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1700 * (7 : ZMod 2150073020951) ^ 1700) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2062902010332 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 2150073020951) ^ 6803 = 1107590103974 := by
        calc
          (7 : ZMod 2150073020951) ^ 6803 = (7 : ZMod 2150073020951) ^ (3401 + 3401 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 3401 * (7 : ZMod 2150073020951) ^ 3401) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1107590103974 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 2150073020951) ^ 13607 = 146252880738 := by
        calc
          (7 : ZMod 2150073020951) ^ 13607 = (7 : ZMod 2150073020951) ^ (6803 + 6803 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 6803 * (7 : ZMod 2150073020951) ^ 6803) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 146252880738 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 2150073020951) ^ 27214 = 654039550395 := by
        calc
          (7 : ZMod 2150073020951) ^ 27214 = (7 : ZMod 2150073020951) ^ (13607 + 13607) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 13607 * (7 : ZMod 2150073020951) ^ 13607 := by rw [pow_add]
          _ = 654039550395 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 2150073020951) ^ 54429 = 1968832310637 := by
        calc
          (7 : ZMod 2150073020951) ^ 54429 = (7 : ZMod 2150073020951) ^ (27214 + 27214 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 27214 * (7 : ZMod 2150073020951) ^ 27214) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1968832310637 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 2150073020951) ^ 108859 = 410785966913 := by
        calc
          (7 : ZMod 2150073020951) ^ 108859 = (7 : ZMod 2150073020951) ^ (54429 + 54429 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 54429 * (7 : ZMod 2150073020951) ^ 54429) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 410785966913 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 2150073020951) ^ 217718 = 576154369561 := by
        calc
          (7 : ZMod 2150073020951) ^ 217718 = (7 : ZMod 2150073020951) ^ (108859 + 108859) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 108859 * (7 : ZMod 2150073020951) ^ 108859 := by rw [pow_add]
          _ = 576154369561 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 2150073020951) ^ 435437 = 1134797289962 := by
        calc
          (7 : ZMod 2150073020951) ^ 435437 = (7 : ZMod 2150073020951) ^ (217718 + 217718 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 217718 * (7 : ZMod 2150073020951) ^ 217718) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1134797289962 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 2150073020951) ^ 870875 = 859369036435 := by
        calc
          (7 : ZMod 2150073020951) ^ 870875 = (7 : ZMod 2150073020951) ^ (435437 + 435437 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 435437 * (7 : ZMod 2150073020951) ^ 435437) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 859369036435 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 2150073020951) ^ 1741750 = 401915706676 := by
        calc
          (7 : ZMod 2150073020951) ^ 1741750 = (7 : ZMod 2150073020951) ^ (870875 + 870875) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 870875 * (7 : ZMod 2150073020951) ^ 870875 := by rw [pow_add]
          _ = 401915706676 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 2150073020951) ^ 3483501 = 808808955429 := by
        calc
          (7 : ZMod 2150073020951) ^ 3483501 = (7 : ZMod 2150073020951) ^ (1741750 + 1741750 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1741750 * (7 : ZMod 2150073020951) ^ 1741750) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 808808955429 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 2150073020951) ^ 6967003 = 1627202505388 := by
        calc
          (7 : ZMod 2150073020951) ^ 6967003 = (7 : ZMod 2150073020951) ^ (3483501 + 3483501 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 3483501 * (7 : ZMod 2150073020951) ^ 3483501) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1627202505388 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 2150073020951) ^ 13934007 = 853784087481 := by
        calc
          (7 : ZMod 2150073020951) ^ 13934007 = (7 : ZMod 2150073020951) ^ (6967003 + 6967003 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 6967003 * (7 : ZMod 2150073020951) ^ 6967003) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 853784087481 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 2150073020951) ^ 27868014 = 900916947346 := by
        calc
          (7 : ZMod 2150073020951) ^ 27868014 = (7 : ZMod 2150073020951) ^ (13934007 + 13934007) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 13934007 * (7 : ZMod 2150073020951) ^ 13934007 := by rw [pow_add]
          _ = 900916947346 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 2150073020951) ^ 55736028 = 796011614807 := by
        calc
          (7 : ZMod 2150073020951) ^ 55736028 = (7 : ZMod 2150073020951) ^ (27868014 + 27868014) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 27868014 * (7 : ZMod 2150073020951) ^ 27868014 := by rw [pow_add]
          _ = 796011614807 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 2150073020951) ^ 111472056 = 1154833510139 := by
        calc
          (7 : ZMod 2150073020951) ^ 111472056 = (7 : ZMod 2150073020951) ^ (55736028 + 55736028) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 55736028 * (7 : ZMod 2150073020951) ^ 55736028 := by rw [pow_add]
          _ = 1154833510139 := by rw [factor_2_25]; decide
      have factor_2_27 : (7 : ZMod 2150073020951) ^ 222944112 = 1165591494053 := by
        calc
          (7 : ZMod 2150073020951) ^ 222944112 = (7 : ZMod 2150073020951) ^ (111472056 + 111472056) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 111472056 * (7 : ZMod 2150073020951) ^ 111472056 := by rw [pow_add]
          _ = 1165591494053 := by rw [factor_2_26]; decide
      have factor_2_28 : (7 : ZMod 2150073020951) ^ 445888225 = 297115789712 := by
        calc
          (7 : ZMod 2150073020951) ^ 445888225 = (7 : ZMod 2150073020951) ^ (222944112 + 222944112 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 222944112 * (7 : ZMod 2150073020951) ^ 222944112) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 297115789712 := by rw [factor_2_27]; decide
      have factor_2_29 : (7 : ZMod 2150073020951) ^ 891776450 = 873189168338 := by
        calc
          (7 : ZMod 2150073020951) ^ 891776450 = (7 : ZMod 2150073020951) ^ (445888225 + 445888225) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 445888225 * (7 : ZMod 2150073020951) ^ 445888225 := by rw [pow_add]
          _ = 873189168338 := by rw [factor_2_28]; decide
      change (7 : ZMod 2150073020951) ^ 891776450 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (7 : ZMod 2150073020951) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 2150073020951) ^ 3 = 343 := by
        calc
          (7 : ZMod 2150073020951) ^ 3 = (7 : ZMod 2150073020951) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1 * (7 : ZMod 2150073020951) ^ 1) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 2150073020951) ^ 7 = 823543 := by
        calc
          (7 : ZMod 2150073020951) ^ 7 = (7 : ZMod 2150073020951) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 3 * (7 : ZMod 2150073020951) ^ 3) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 2150073020951) ^ 14 = 678223072849 := by
        calc
          (7 : ZMod 2150073020951) ^ 14 = (7 : ZMod 2150073020951) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 7 * (7 : ZMod 2150073020951) ^ 7 := by rw [pow_add]
          _ = 678223072849 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 2150073020951) ^ 29 = 221132738657 := by
        calc
          (7 : ZMod 2150073020951) ^ 29 = (7 : ZMod 2150073020951) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 14 * (7 : ZMod 2150073020951) ^ 14) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 221132738657 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 2150073020951) ^ 58 = 1247130898305 := by
        calc
          (7 : ZMod 2150073020951) ^ 58 = (7 : ZMod 2150073020951) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 29 * (7 : ZMod 2150073020951) ^ 29 := by rw [pow_add]
          _ = 1247130898305 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 2150073020951) ^ 117 = 583259075498 := by
        calc
          (7 : ZMod 2150073020951) ^ 117 = (7 : ZMod 2150073020951) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 58 * (7 : ZMod 2150073020951) ^ 58) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 583259075498 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 2150073020951) ^ 235 = 2007311187589 := by
        calc
          (7 : ZMod 2150073020951) ^ 235 = (7 : ZMod 2150073020951) ^ (117 + 117 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 117 * (7 : ZMod 2150073020951) ^ 117) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2007311187589 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 2150073020951) ^ 470 = 537496225916 := by
        calc
          (7 : ZMod 2150073020951) ^ 470 = (7 : ZMod 2150073020951) ^ (235 + 235) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 235 * (7 : ZMod 2150073020951) ^ 235 := by rw [pow_add]
          _ = 537496225916 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 2150073020951) ^ 941 = 1937437709723 := by
        calc
          (7 : ZMod 2150073020951) ^ 941 = (7 : ZMod 2150073020951) ^ (470 + 470 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 470 * (7 : ZMod 2150073020951) ^ 470) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1937437709723 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 2150073020951) ^ 1883 = 2094204623340 := by
        calc
          (7 : ZMod 2150073020951) ^ 1883 = (7 : ZMod 2150073020951) ^ (941 + 941 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 941 * (7 : ZMod 2150073020951) ^ 941) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 2094204623340 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 2150073020951) ^ 3767 = 388440509848 := by
        calc
          (7 : ZMod 2150073020951) ^ 3767 = (7 : ZMod 2150073020951) ^ (1883 + 1883 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 1883 * (7 : ZMod 2150073020951) ^ 1883) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 388440509848 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 2150073020951) ^ 7534 = 129145830354 := by
        calc
          (7 : ZMod 2150073020951) ^ 7534 = (7 : ZMod 2150073020951) ^ (3767 + 3767) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 3767 * (7 : ZMod 2150073020951) ^ 3767 := by rw [pow_add]
          _ = 129145830354 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 2150073020951) ^ 15068 = 1538829310844 := by
        calc
          (7 : ZMod 2150073020951) ^ 15068 = (7 : ZMod 2150073020951) ^ (7534 + 7534) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 7534 * (7 : ZMod 2150073020951) ^ 7534 := by rw [pow_add]
          _ = 1538829310844 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 2150073020951) ^ 30137 = 1324431765283 := by
        calc
          (7 : ZMod 2150073020951) ^ 30137 = (7 : ZMod 2150073020951) ^ (15068 + 15068 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 15068 * (7 : ZMod 2150073020951) ^ 15068) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 1324431765283 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 2150073020951) ^ 60275 = 711135276070 := by
        calc
          (7 : ZMod 2150073020951) ^ 60275 = (7 : ZMod 2150073020951) ^ (30137 + 30137 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = ((7 : ZMod 2150073020951) ^ 30137 * (7 : ZMod 2150073020951) ^ 30137) * (7 : ZMod 2150073020951) := by rw [pow_succ, pow_add]
          _ = 711135276070 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 2150073020951) ^ 120550 = 378800848222 := by
        calc
          (7 : ZMod 2150073020951) ^ 120550 = (7 : ZMod 2150073020951) ^ (60275 + 60275) :=
            congrArg (fun n : ℕ => (7 : ZMod 2150073020951) ^ n) (by norm_num)
          _ = (7 : ZMod 2150073020951) ^ 60275 * (7 : ZMod 2150073020951) ^ 60275 := by rw [pow_add]
          _ = 378800848222 := by rw [factor_3_15]; decide
      change (7 : ZMod 2150073020951) ^ 120550 ≠ 1
      rw [factor_3_16]
      decide

#print axioms prime_lucas_2150073020951

end TotientTailPeriodKiller
end Erdos249257
