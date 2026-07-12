import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_7512352185857 : Nat.Prime 7512352185857 := by
  apply lucas_primality 7512352185857 (5 : ZMod 7512352185857)
  ·
      have fermat_0 : (5 : ZMod 7512352185857) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 7512352185857) ^ 3 = 125 := by
        calc
          (5 : ZMod 7512352185857) ^ 3 = (5 : ZMod 7512352185857) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1 * (5 : ZMod 7512352185857) ^ 1) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 7512352185857) ^ 6 = 15625 := by
        calc
          (5 : ZMod 7512352185857) ^ 6 = (5 : ZMod 7512352185857) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3 * (5 : ZMod 7512352185857) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 7512352185857) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 7512352185857) ^ 13 = (5 : ZMod 7512352185857) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 6 * (5 : ZMod 7512352185857) ^ 6) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 7512352185857) ^ 27 = 2483091130236 := by
        calc
          (5 : ZMod 7512352185857) ^ 27 = (5 : ZMod 7512352185857) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 13 * (5 : ZMod 7512352185857) ^ 13) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2483091130236 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 7512352185857) ^ 54 = 6027221900217 := by
        calc
          (5 : ZMod 7512352185857) ^ 54 = (5 : ZMod 7512352185857) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 27 * (5 : ZMod 7512352185857) ^ 27 := by rw [pow_add]
          _ = 6027221900217 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 7512352185857) ^ 109 = 5032412811345 := by
        calc
          (5 : ZMod 7512352185857) ^ 109 = (5 : ZMod 7512352185857) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 54 * (5 : ZMod 7512352185857) ^ 54) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5032412811345 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 7512352185857) ^ 218 = 4091460669760 := by
        calc
          (5 : ZMod 7512352185857) ^ 218 = (5 : ZMod 7512352185857) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 109 * (5 : ZMod 7512352185857) ^ 109 := by rw [pow_add]
          _ = 4091460669760 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 7512352185857) ^ 437 = 4191393317388 := by
        calc
          (5 : ZMod 7512352185857) ^ 437 = (5 : ZMod 7512352185857) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 218 * (5 : ZMod 7512352185857) ^ 218) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4191393317388 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 7512352185857) ^ 874 = 1925568223884 := by
        calc
          (5 : ZMod 7512352185857) ^ 874 = (5 : ZMod 7512352185857) ^ (437 + 437) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 437 * (5 : ZMod 7512352185857) ^ 437 := by rw [pow_add]
          _ = 1925568223884 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 7512352185857) ^ 1749 = 6321819438275 := by
        calc
          (5 : ZMod 7512352185857) ^ 1749 = (5 : ZMod 7512352185857) ^ (874 + 874 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 874 * (5 : ZMod 7512352185857) ^ 874) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6321819438275 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 7512352185857) ^ 3498 = 3079417951490 := by
        calc
          (5 : ZMod 7512352185857) ^ 3498 = (5 : ZMod 7512352185857) ^ (1749 + 1749) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1749 * (5 : ZMod 7512352185857) ^ 1749 := by rw [pow_add]
          _ = 3079417951490 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 7512352185857) ^ 6996 = 2940009101158 := by
        calc
          (5 : ZMod 7512352185857) ^ 6996 = (5 : ZMod 7512352185857) ^ (3498 + 3498) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3498 * (5 : ZMod 7512352185857) ^ 3498 := by rw [pow_add]
          _ = 2940009101158 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 7512352185857) ^ 13992 = 5344421345425 := by
        calc
          (5 : ZMod 7512352185857) ^ 13992 = (5 : ZMod 7512352185857) ^ (6996 + 6996) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 6996 * (5 : ZMod 7512352185857) ^ 6996 := by rw [pow_add]
          _ = 5344421345425 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 7512352185857) ^ 27985 = 735433496564 := by
        calc
          (5 : ZMod 7512352185857) ^ 27985 = (5 : ZMod 7512352185857) ^ (13992 + 13992 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 13992 * (5 : ZMod 7512352185857) ^ 13992) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 735433496564 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 7512352185857) ^ 55971 = 2514685111410 := by
        calc
          (5 : ZMod 7512352185857) ^ 55971 = (5 : ZMod 7512352185857) ^ (27985 + 27985 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 27985 * (5 : ZMod 7512352185857) ^ 27985) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2514685111410 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 7512352185857) ^ 111942 = 5626401382992 := by
        calc
          (5 : ZMod 7512352185857) ^ 111942 = (5 : ZMod 7512352185857) ^ (55971 + 55971) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 55971 * (5 : ZMod 7512352185857) ^ 55971 := by rw [pow_add]
          _ = 5626401382992 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 7512352185857) ^ 223885 = 632238139783 := by
        calc
          (5 : ZMod 7512352185857) ^ 223885 = (5 : ZMod 7512352185857) ^ (111942 + 111942 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 111942 * (5 : ZMod 7512352185857) ^ 111942) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 632238139783 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 7512352185857) ^ 447771 = 6169622235675 := by
        calc
          (5 : ZMod 7512352185857) ^ 447771 = (5 : ZMod 7512352185857) ^ (223885 + 223885 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 223885 * (5 : ZMod 7512352185857) ^ 223885) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6169622235675 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 7512352185857) ^ 895542 = 7018761469583 := by
        calc
          (5 : ZMod 7512352185857) ^ 895542 = (5 : ZMod 7512352185857) ^ (447771 + 447771) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 447771 * (5 : ZMod 7512352185857) ^ 447771 := by rw [pow_add]
          _ = 7018761469583 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 7512352185857) ^ 1791084 = 7501439940668 := by
        calc
          (5 : ZMod 7512352185857) ^ 1791084 = (5 : ZMod 7512352185857) ^ (895542 + 895542) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 895542 * (5 : ZMod 7512352185857) ^ 895542 := by rw [pow_add]
          _ = 7501439940668 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 7512352185857) ^ 3582168 = 2543184075841 := by
        calc
          (5 : ZMod 7512352185857) ^ 3582168 = (5 : ZMod 7512352185857) ^ (1791084 + 1791084) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1791084 * (5 : ZMod 7512352185857) ^ 1791084 := by rw [pow_add]
          _ = 2543184075841 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 7512352185857) ^ 7164337 = 6742069703696 := by
        calc
          (5 : ZMod 7512352185857) ^ 7164337 = (5 : ZMod 7512352185857) ^ (3582168 + 3582168 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 3582168 * (5 : ZMod 7512352185857) ^ 3582168) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6742069703696 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 7512352185857) ^ 14328674 = 873859277369 := by
        calc
          (5 : ZMod 7512352185857) ^ 14328674 = (5 : ZMod 7512352185857) ^ (7164337 + 7164337) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 7164337 * (5 : ZMod 7512352185857) ^ 7164337 := by rw [pow_add]
          _ = 873859277369 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 7512352185857) ^ 28657349 = 4003425535698 := by
        calc
          (5 : ZMod 7512352185857) ^ 28657349 = (5 : ZMod 7512352185857) ^ (14328674 + 14328674 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 14328674 * (5 : ZMod 7512352185857) ^ 14328674) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4003425535698 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 7512352185857) ^ 57314698 = 1328275799717 := by
        calc
          (5 : ZMod 7512352185857) ^ 57314698 = (5 : ZMod 7512352185857) ^ (28657349 + 28657349) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 28657349 * (5 : ZMod 7512352185857) ^ 28657349 := by rw [pow_add]
          _ = 1328275799717 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 7512352185857) ^ 114629397 = 4961888301527 := by
        calc
          (5 : ZMod 7512352185857) ^ 114629397 = (5 : ZMod 7512352185857) ^ (57314698 + 57314698 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 57314698 * (5 : ZMod 7512352185857) ^ 57314698) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4961888301527 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 7512352185857) ^ 229258794 = 705195606255 := by
        calc
          (5 : ZMod 7512352185857) ^ 229258794 = (5 : ZMod 7512352185857) ^ (114629397 + 114629397) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 114629397 * (5 : ZMod 7512352185857) ^ 114629397 := by rw [pow_add]
          _ = 705195606255 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 7512352185857) ^ 458517589 = 6462771271660 := by
        calc
          (5 : ZMod 7512352185857) ^ 458517589 = (5 : ZMod 7512352185857) ^ (229258794 + 229258794 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 229258794 * (5 : ZMod 7512352185857) ^ 229258794) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6462771271660 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 7512352185857) ^ 917035178 = 967538159885 := by
        calc
          (5 : ZMod 7512352185857) ^ 917035178 = (5 : ZMod 7512352185857) ^ (458517589 + 458517589) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 458517589 * (5 : ZMod 7512352185857) ^ 458517589 := by rw [pow_add]
          _ = 967538159885 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 7512352185857) ^ 1834070357 = 5878570525633 := by
        calc
          (5 : ZMod 7512352185857) ^ 1834070357 = (5 : ZMod 7512352185857) ^ (917035178 + 917035178 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 917035178 * (5 : ZMod 7512352185857) ^ 917035178) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5878570525633 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 7512352185857) ^ 3668140715 = 1553123489452 := by
        calc
          (5 : ZMod 7512352185857) ^ 3668140715 = (5 : ZMod 7512352185857) ^ (1834070357 + 1834070357 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1834070357 * (5 : ZMod 7512352185857) ^ 1834070357) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1553123489452 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 7512352185857) ^ 7336281431 = 3104413065958 := by
        calc
          (5 : ZMod 7512352185857) ^ 7336281431 = (5 : ZMod 7512352185857) ^ (3668140715 + 3668140715 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 3668140715 * (5 : ZMod 7512352185857) ^ 3668140715) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3104413065958 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 7512352185857) ^ 14672562863 = 2700216206509 := by
        calc
          (5 : ZMod 7512352185857) ^ 14672562863 = (5 : ZMod 7512352185857) ^ (7336281431 + 7336281431 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 7336281431 * (5 : ZMod 7512352185857) ^ 7336281431) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2700216206509 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 7512352185857) ^ 29345125726 = 2640354589631 := by
        calc
          (5 : ZMod 7512352185857) ^ 29345125726 = (5 : ZMod 7512352185857) ^ (14672562863 + 14672562863) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 14672562863 * (5 : ZMod 7512352185857) ^ 14672562863 := by rw [pow_add]
          _ = 2640354589631 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 7512352185857) ^ 58690251452 = 2151586162396 := by
        calc
          (5 : ZMod 7512352185857) ^ 58690251452 = (5 : ZMod 7512352185857) ^ (29345125726 + 29345125726) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 29345125726 * (5 : ZMod 7512352185857) ^ 29345125726 := by rw [pow_add]
          _ = 2151586162396 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 7512352185857) ^ 117380502904 = 5007264030042 := by
        calc
          (5 : ZMod 7512352185857) ^ 117380502904 = (5 : ZMod 7512352185857) ^ (58690251452 + 58690251452) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 58690251452 * (5 : ZMod 7512352185857) ^ 58690251452 := by rw [pow_add]
          _ = 5007264030042 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 7512352185857) ^ 234761005808 = 2340649477019 := by
        calc
          (5 : ZMod 7512352185857) ^ 234761005808 = (5 : ZMod 7512352185857) ^ (117380502904 + 117380502904) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 117380502904 * (5 : ZMod 7512352185857) ^ 117380502904 := by rw [pow_add]
          _ = 2340649477019 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 7512352185857) ^ 469522011616 = 3641503841550 := by
        calc
          (5 : ZMod 7512352185857) ^ 469522011616 = (5 : ZMod 7512352185857) ^ (234761005808 + 234761005808) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 234761005808 * (5 : ZMod 7512352185857) ^ 234761005808 := by rw [pow_add]
          _ = 3641503841550 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 7512352185857) ^ 939044023232 = 4769814228775 := by
        calc
          (5 : ZMod 7512352185857) ^ 939044023232 = (5 : ZMod 7512352185857) ^ (469522011616 + 469522011616) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 469522011616 * (5 : ZMod 7512352185857) ^ 469522011616 := by rw [pow_add]
          _ = 4769814228775 := by rw [fermat_38]; decide
      have fermat_40 : (5 : ZMod 7512352185857) ^ 1878088046464 = 3772057313155 := by
        calc
          (5 : ZMod 7512352185857) ^ 1878088046464 = (5 : ZMod 7512352185857) ^ (939044023232 + 939044023232) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 939044023232 * (5 : ZMod 7512352185857) ^ 939044023232 := by rw [pow_add]
          _ = 3772057313155 := by rw [fermat_39]; decide
      have fermat_41 : (5 : ZMod 7512352185857) ^ 3756176092928 = 7512352185856 := by
        calc
          (5 : ZMod 7512352185857) ^ 3756176092928 = (5 : ZMod 7512352185857) ^ (1878088046464 + 1878088046464) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1878088046464 * (5 : ZMod 7512352185857) ^ 1878088046464 := by rw [pow_add]
          _ = 7512352185856 := by rw [fermat_40]; decide
      have fermat_42 : (5 : ZMod 7512352185857) ^ 7512352185856 = 1 := by
        calc
          (5 : ZMod 7512352185857) ^ 7512352185856 = (5 : ZMod 7512352185857) ^ (3756176092928 + 3756176092928) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3756176092928 * (5 : ZMod 7512352185857) ^ 3756176092928 := by rw [pow_add]
          _ = 1 := by rw [fermat_41]; decide
      simpa using fermat_42
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (7, 1), (137, 1), (631, 1), (24247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (7, 1), (137, 1), (631, 1), (24247, 1)] : List FactorBlock).map factorBlockValue).prod = 7512352185857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 7512352185857) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 7512352185857) ^ 3 = 125 := by
        calc
          (5 : ZMod 7512352185857) ^ 3 = (5 : ZMod 7512352185857) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1 * (5 : ZMod 7512352185857) ^ 1) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 7512352185857) ^ 6 = 15625 := by
        calc
          (5 : ZMod 7512352185857) ^ 6 = (5 : ZMod 7512352185857) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3 * (5 : ZMod 7512352185857) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 7512352185857) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 7512352185857) ^ 13 = (5 : ZMod 7512352185857) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 6 * (5 : ZMod 7512352185857) ^ 6) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 7512352185857) ^ 27 = 2483091130236 := by
        calc
          (5 : ZMod 7512352185857) ^ 27 = (5 : ZMod 7512352185857) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 13 * (5 : ZMod 7512352185857) ^ 13) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2483091130236 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 7512352185857) ^ 54 = 6027221900217 := by
        calc
          (5 : ZMod 7512352185857) ^ 54 = (5 : ZMod 7512352185857) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 27 * (5 : ZMod 7512352185857) ^ 27 := by rw [pow_add]
          _ = 6027221900217 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 7512352185857) ^ 109 = 5032412811345 := by
        calc
          (5 : ZMod 7512352185857) ^ 109 = (5 : ZMod 7512352185857) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 54 * (5 : ZMod 7512352185857) ^ 54) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5032412811345 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 7512352185857) ^ 218 = 4091460669760 := by
        calc
          (5 : ZMod 7512352185857) ^ 218 = (5 : ZMod 7512352185857) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 109 * (5 : ZMod 7512352185857) ^ 109 := by rw [pow_add]
          _ = 4091460669760 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 7512352185857) ^ 437 = 4191393317388 := by
        calc
          (5 : ZMod 7512352185857) ^ 437 = (5 : ZMod 7512352185857) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 218 * (5 : ZMod 7512352185857) ^ 218) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4191393317388 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 7512352185857) ^ 874 = 1925568223884 := by
        calc
          (5 : ZMod 7512352185857) ^ 874 = (5 : ZMod 7512352185857) ^ (437 + 437) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 437 * (5 : ZMod 7512352185857) ^ 437 := by rw [pow_add]
          _ = 1925568223884 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 7512352185857) ^ 1749 = 6321819438275 := by
        calc
          (5 : ZMod 7512352185857) ^ 1749 = (5 : ZMod 7512352185857) ^ (874 + 874 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 874 * (5 : ZMod 7512352185857) ^ 874) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6321819438275 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 7512352185857) ^ 3498 = 3079417951490 := by
        calc
          (5 : ZMod 7512352185857) ^ 3498 = (5 : ZMod 7512352185857) ^ (1749 + 1749) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1749 * (5 : ZMod 7512352185857) ^ 1749 := by rw [pow_add]
          _ = 3079417951490 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 7512352185857) ^ 6996 = 2940009101158 := by
        calc
          (5 : ZMod 7512352185857) ^ 6996 = (5 : ZMod 7512352185857) ^ (3498 + 3498) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3498 * (5 : ZMod 7512352185857) ^ 3498 := by rw [pow_add]
          _ = 2940009101158 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 7512352185857) ^ 13992 = 5344421345425 := by
        calc
          (5 : ZMod 7512352185857) ^ 13992 = (5 : ZMod 7512352185857) ^ (6996 + 6996) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 6996 * (5 : ZMod 7512352185857) ^ 6996 := by rw [pow_add]
          _ = 5344421345425 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 7512352185857) ^ 27985 = 735433496564 := by
        calc
          (5 : ZMod 7512352185857) ^ 27985 = (5 : ZMod 7512352185857) ^ (13992 + 13992 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 13992 * (5 : ZMod 7512352185857) ^ 13992) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 735433496564 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 7512352185857) ^ 55971 = 2514685111410 := by
        calc
          (5 : ZMod 7512352185857) ^ 55971 = (5 : ZMod 7512352185857) ^ (27985 + 27985 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 27985 * (5 : ZMod 7512352185857) ^ 27985) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2514685111410 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 7512352185857) ^ 111942 = 5626401382992 := by
        calc
          (5 : ZMod 7512352185857) ^ 111942 = (5 : ZMod 7512352185857) ^ (55971 + 55971) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 55971 * (5 : ZMod 7512352185857) ^ 55971 := by rw [pow_add]
          _ = 5626401382992 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 7512352185857) ^ 223885 = 632238139783 := by
        calc
          (5 : ZMod 7512352185857) ^ 223885 = (5 : ZMod 7512352185857) ^ (111942 + 111942 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 111942 * (5 : ZMod 7512352185857) ^ 111942) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 632238139783 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 7512352185857) ^ 447771 = 6169622235675 := by
        calc
          (5 : ZMod 7512352185857) ^ 447771 = (5 : ZMod 7512352185857) ^ (223885 + 223885 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 223885 * (5 : ZMod 7512352185857) ^ 223885) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6169622235675 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 7512352185857) ^ 895542 = 7018761469583 := by
        calc
          (5 : ZMod 7512352185857) ^ 895542 = (5 : ZMod 7512352185857) ^ (447771 + 447771) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 447771 * (5 : ZMod 7512352185857) ^ 447771 := by rw [pow_add]
          _ = 7018761469583 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 7512352185857) ^ 1791084 = 7501439940668 := by
        calc
          (5 : ZMod 7512352185857) ^ 1791084 = (5 : ZMod 7512352185857) ^ (895542 + 895542) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 895542 * (5 : ZMod 7512352185857) ^ 895542 := by rw [pow_add]
          _ = 7501439940668 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 7512352185857) ^ 3582168 = 2543184075841 := by
        calc
          (5 : ZMod 7512352185857) ^ 3582168 = (5 : ZMod 7512352185857) ^ (1791084 + 1791084) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1791084 * (5 : ZMod 7512352185857) ^ 1791084 := by rw [pow_add]
          _ = 2543184075841 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 7512352185857) ^ 7164337 = 6742069703696 := by
        calc
          (5 : ZMod 7512352185857) ^ 7164337 = (5 : ZMod 7512352185857) ^ (3582168 + 3582168 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 3582168 * (5 : ZMod 7512352185857) ^ 3582168) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6742069703696 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 7512352185857) ^ 14328674 = 873859277369 := by
        calc
          (5 : ZMod 7512352185857) ^ 14328674 = (5 : ZMod 7512352185857) ^ (7164337 + 7164337) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 7164337 * (5 : ZMod 7512352185857) ^ 7164337 := by rw [pow_add]
          _ = 873859277369 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 7512352185857) ^ 28657349 = 4003425535698 := by
        calc
          (5 : ZMod 7512352185857) ^ 28657349 = (5 : ZMod 7512352185857) ^ (14328674 + 14328674 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 14328674 * (5 : ZMod 7512352185857) ^ 14328674) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4003425535698 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 7512352185857) ^ 57314698 = 1328275799717 := by
        calc
          (5 : ZMod 7512352185857) ^ 57314698 = (5 : ZMod 7512352185857) ^ (28657349 + 28657349) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 28657349 * (5 : ZMod 7512352185857) ^ 28657349 := by rw [pow_add]
          _ = 1328275799717 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 7512352185857) ^ 114629397 = 4961888301527 := by
        calc
          (5 : ZMod 7512352185857) ^ 114629397 = (5 : ZMod 7512352185857) ^ (57314698 + 57314698 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 57314698 * (5 : ZMod 7512352185857) ^ 57314698) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4961888301527 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 7512352185857) ^ 229258794 = 705195606255 := by
        calc
          (5 : ZMod 7512352185857) ^ 229258794 = (5 : ZMod 7512352185857) ^ (114629397 + 114629397) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 114629397 * (5 : ZMod 7512352185857) ^ 114629397 := by rw [pow_add]
          _ = 705195606255 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 7512352185857) ^ 458517589 = 6462771271660 := by
        calc
          (5 : ZMod 7512352185857) ^ 458517589 = (5 : ZMod 7512352185857) ^ (229258794 + 229258794 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 229258794 * (5 : ZMod 7512352185857) ^ 229258794) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6462771271660 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 7512352185857) ^ 917035178 = 967538159885 := by
        calc
          (5 : ZMod 7512352185857) ^ 917035178 = (5 : ZMod 7512352185857) ^ (458517589 + 458517589) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 458517589 * (5 : ZMod 7512352185857) ^ 458517589 := by rw [pow_add]
          _ = 967538159885 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 7512352185857) ^ 1834070357 = 5878570525633 := by
        calc
          (5 : ZMod 7512352185857) ^ 1834070357 = (5 : ZMod 7512352185857) ^ (917035178 + 917035178 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 917035178 * (5 : ZMod 7512352185857) ^ 917035178) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5878570525633 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 7512352185857) ^ 3668140715 = 1553123489452 := by
        calc
          (5 : ZMod 7512352185857) ^ 3668140715 = (5 : ZMod 7512352185857) ^ (1834070357 + 1834070357 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1834070357 * (5 : ZMod 7512352185857) ^ 1834070357) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1553123489452 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 7512352185857) ^ 7336281431 = 3104413065958 := by
        calc
          (5 : ZMod 7512352185857) ^ 7336281431 = (5 : ZMod 7512352185857) ^ (3668140715 + 3668140715 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 3668140715 * (5 : ZMod 7512352185857) ^ 3668140715) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3104413065958 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 7512352185857) ^ 14672562863 = 2700216206509 := by
        calc
          (5 : ZMod 7512352185857) ^ 14672562863 = (5 : ZMod 7512352185857) ^ (7336281431 + 7336281431 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 7336281431 * (5 : ZMod 7512352185857) ^ 7336281431) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2700216206509 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 7512352185857) ^ 29345125726 = 2640354589631 := by
        calc
          (5 : ZMod 7512352185857) ^ 29345125726 = (5 : ZMod 7512352185857) ^ (14672562863 + 14672562863) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 14672562863 * (5 : ZMod 7512352185857) ^ 14672562863 := by rw [pow_add]
          _ = 2640354589631 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 7512352185857) ^ 58690251452 = 2151586162396 := by
        calc
          (5 : ZMod 7512352185857) ^ 58690251452 = (5 : ZMod 7512352185857) ^ (29345125726 + 29345125726) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 29345125726 * (5 : ZMod 7512352185857) ^ 29345125726 := by rw [pow_add]
          _ = 2151586162396 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 7512352185857) ^ 117380502904 = 5007264030042 := by
        calc
          (5 : ZMod 7512352185857) ^ 117380502904 = (5 : ZMod 7512352185857) ^ (58690251452 + 58690251452) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 58690251452 * (5 : ZMod 7512352185857) ^ 58690251452 := by rw [pow_add]
          _ = 5007264030042 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 7512352185857) ^ 234761005808 = 2340649477019 := by
        calc
          (5 : ZMod 7512352185857) ^ 234761005808 = (5 : ZMod 7512352185857) ^ (117380502904 + 117380502904) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 117380502904 * (5 : ZMod 7512352185857) ^ 117380502904 := by rw [pow_add]
          _ = 2340649477019 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 7512352185857) ^ 469522011616 = 3641503841550 := by
        calc
          (5 : ZMod 7512352185857) ^ 469522011616 = (5 : ZMod 7512352185857) ^ (234761005808 + 234761005808) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 234761005808 * (5 : ZMod 7512352185857) ^ 234761005808 := by rw [pow_add]
          _ = 3641503841550 := by rw [factor_0_37]; decide
      have factor_0_39 : (5 : ZMod 7512352185857) ^ 939044023232 = 4769814228775 := by
        calc
          (5 : ZMod 7512352185857) ^ 939044023232 = (5 : ZMod 7512352185857) ^ (469522011616 + 469522011616) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 469522011616 * (5 : ZMod 7512352185857) ^ 469522011616 := by rw [pow_add]
          _ = 4769814228775 := by rw [factor_0_38]; decide
      have factor_0_40 : (5 : ZMod 7512352185857) ^ 1878088046464 = 3772057313155 := by
        calc
          (5 : ZMod 7512352185857) ^ 1878088046464 = (5 : ZMod 7512352185857) ^ (939044023232 + 939044023232) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 939044023232 * (5 : ZMod 7512352185857) ^ 939044023232 := by rw [pow_add]
          _ = 3772057313155 := by rw [factor_0_39]; decide
      have factor_0_41 : (5 : ZMod 7512352185857) ^ 3756176092928 = 7512352185856 := by
        calc
          (5 : ZMod 7512352185857) ^ 3756176092928 = (5 : ZMod 7512352185857) ^ (1878088046464 + 1878088046464) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1878088046464 * (5 : ZMod 7512352185857) ^ 1878088046464 := by rw [pow_add]
          _ = 7512352185856 := by rw [factor_0_40]; decide
      change (5 : ZMod 7512352185857) ^ 3756176092928 ≠ 1
      rw [factor_0_41]
      decide
    ·
      have factor_1_0 : (5 : ZMod 7512352185857) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 7512352185857) ^ 3 = 125 := by
        calc
          (5 : ZMod 7512352185857) ^ 3 = (5 : ZMod 7512352185857) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1 * (5 : ZMod 7512352185857) ^ 1) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 7512352185857) ^ 7 = 78125 := by
        calc
          (5 : ZMod 7512352185857) ^ 7 = (5 : ZMod 7512352185857) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 3 * (5 : ZMod 7512352185857) ^ 3) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 7512352185857) ^ 15 = 30517578125 := by
        calc
          (5 : ZMod 7512352185857) ^ 15 = (5 : ZMod 7512352185857) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 7 * (5 : ZMod 7512352185857) ^ 7) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 30517578125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 7512352185857) ^ 31 = 4387406110958 := by
        calc
          (5 : ZMod 7512352185857) ^ 31 = (5 : ZMod 7512352185857) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 15 * (5 : ZMod 7512352185857) ^ 15) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4387406110958 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 7512352185857) ^ 62 = 4867372495968 := by
        calc
          (5 : ZMod 7512352185857) ^ 62 = (5 : ZMod 7512352185857) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 31 * (5 : ZMod 7512352185857) ^ 31 := by rw [pow_add]
          _ = 4867372495968 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 7512352185857) ^ 124 = 2808388918402 := by
        calc
          (5 : ZMod 7512352185857) ^ 124 = (5 : ZMod 7512352185857) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 62 * (5 : ZMod 7512352185857) ^ 62 := by rw [pow_add]
          _ = 2808388918402 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 7512352185857) ^ 249 = 1718972834067 := by
        calc
          (5 : ZMod 7512352185857) ^ 249 = (5 : ZMod 7512352185857) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 124 * (5 : ZMod 7512352185857) ^ 124) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1718972834067 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 7512352185857) ^ 499 = 177480903959 := by
        calc
          (5 : ZMod 7512352185857) ^ 499 = (5 : ZMod 7512352185857) ^ (249 + 249 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 249 * (5 : ZMod 7512352185857) ^ 249) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 177480903959 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 7512352185857) ^ 999 = 6093137122525 := by
        calc
          (5 : ZMod 7512352185857) ^ 999 = (5 : ZMod 7512352185857) ^ (499 + 499 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 499 * (5 : ZMod 7512352185857) ^ 499) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6093137122525 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 7512352185857) ^ 1998 = 201777873309 := by
        calc
          (5 : ZMod 7512352185857) ^ 1998 = (5 : ZMod 7512352185857) ^ (999 + 999) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 999 * (5 : ZMod 7512352185857) ^ 999 := by rw [pow_add]
          _ = 201777873309 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 7512352185857) ^ 3997 = 4630701615800 := by
        calc
          (5 : ZMod 7512352185857) ^ 3997 = (5 : ZMod 7512352185857) ^ (1998 + 1998 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1998 * (5 : ZMod 7512352185857) ^ 1998) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4630701615800 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 7512352185857) ^ 7995 = 1103021743009 := by
        calc
          (5 : ZMod 7512352185857) ^ 7995 = (5 : ZMod 7512352185857) ^ (3997 + 3997 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 3997 * (5 : ZMod 7512352185857) ^ 3997) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1103021743009 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 7512352185857) ^ 15991 = 2132566781663 := by
        calc
          (5 : ZMod 7512352185857) ^ 15991 = (5 : ZMod 7512352185857) ^ (7995 + 7995 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 7995 * (5 : ZMod 7512352185857) ^ 7995) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2132566781663 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 7512352185857) ^ 31983 = 766441056425 := by
        calc
          (5 : ZMod 7512352185857) ^ 31983 = (5 : ZMod 7512352185857) ^ (15991 + 15991 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 15991 * (5 : ZMod 7512352185857) ^ 15991) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 766441056425 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 7512352185857) ^ 63967 = 1074869482651 := by
        calc
          (5 : ZMod 7512352185857) ^ 63967 = (5 : ZMod 7512352185857) ^ (31983 + 31983 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 31983 * (5 : ZMod 7512352185857) ^ 31983) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1074869482651 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 7512352185857) ^ 127934 = 2696722705031 := by
        calc
          (5 : ZMod 7512352185857) ^ 127934 = (5 : ZMod 7512352185857) ^ (63967 + 63967) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 63967 * (5 : ZMod 7512352185857) ^ 63967 := by rw [pow_add]
          _ = 2696722705031 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 7512352185857) ^ 255869 = 2085209320458 := by
        calc
          (5 : ZMod 7512352185857) ^ 255869 = (5 : ZMod 7512352185857) ^ (127934 + 127934 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 127934 * (5 : ZMod 7512352185857) ^ 127934) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2085209320458 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 7512352185857) ^ 511738 = 2396308155758 := by
        calc
          (5 : ZMod 7512352185857) ^ 511738 = (5 : ZMod 7512352185857) ^ (255869 + 255869) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 255869 * (5 : ZMod 7512352185857) ^ 255869 := by rw [pow_add]
          _ = 2396308155758 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 7512352185857) ^ 1023476 = 5450725843266 := by
        calc
          (5 : ZMod 7512352185857) ^ 1023476 = (5 : ZMod 7512352185857) ^ (511738 + 511738) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 511738 * (5 : ZMod 7512352185857) ^ 511738 := by rw [pow_add]
          _ = 5450725843266 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 7512352185857) ^ 2046953 = 178878065122 := by
        calc
          (5 : ZMod 7512352185857) ^ 2046953 = (5 : ZMod 7512352185857) ^ (1023476 + 1023476 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1023476 * (5 : ZMod 7512352185857) ^ 1023476) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 178878065122 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 7512352185857) ^ 4093907 = 6111964125469 := by
        calc
          (5 : ZMod 7512352185857) ^ 4093907 = (5 : ZMod 7512352185857) ^ (2046953 + 2046953 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 2046953 * (5 : ZMod 7512352185857) ^ 2046953) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6111964125469 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 7512352185857) ^ 8187814 = 6027247483356 := by
        calc
          (5 : ZMod 7512352185857) ^ 8187814 = (5 : ZMod 7512352185857) ^ (4093907 + 4093907) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 4093907 * (5 : ZMod 7512352185857) ^ 4093907 := by rw [pow_add]
          _ = 6027247483356 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 7512352185857) ^ 16375628 = 4617395829232 := by
        calc
          (5 : ZMod 7512352185857) ^ 16375628 = (5 : ZMod 7512352185857) ^ (8187814 + 8187814) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 8187814 * (5 : ZMod 7512352185857) ^ 8187814 := by rw [pow_add]
          _ = 4617395829232 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 7512352185857) ^ 32751256 = 3062743527597 := by
        calc
          (5 : ZMod 7512352185857) ^ 32751256 = (5 : ZMod 7512352185857) ^ (16375628 + 16375628) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 16375628 * (5 : ZMod 7512352185857) ^ 16375628 := by rw [pow_add]
          _ = 3062743527597 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 7512352185857) ^ 65502512 = 3486483229706 := by
        calc
          (5 : ZMod 7512352185857) ^ 65502512 = (5 : ZMod 7512352185857) ^ (32751256 + 32751256) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 32751256 * (5 : ZMod 7512352185857) ^ 32751256 := by rw [pow_add]
          _ = 3486483229706 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 7512352185857) ^ 131005025 = 4355586243466 := by
        calc
          (5 : ZMod 7512352185857) ^ 131005025 = (5 : ZMod 7512352185857) ^ (65502512 + 65502512 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 65502512 * (5 : ZMod 7512352185857) ^ 65502512) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4355586243466 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 7512352185857) ^ 262010051 = 6667374497904 := by
        calc
          (5 : ZMod 7512352185857) ^ 262010051 = (5 : ZMod 7512352185857) ^ (131005025 + 131005025 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 131005025 * (5 : ZMod 7512352185857) ^ 131005025) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6667374497904 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 7512352185857) ^ 524020102 = 5467788865770 := by
        calc
          (5 : ZMod 7512352185857) ^ 524020102 = (5 : ZMod 7512352185857) ^ (262010051 + 262010051) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 262010051 * (5 : ZMod 7512352185857) ^ 262010051 := by rw [pow_add]
          _ = 5467788865770 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 7512352185857) ^ 1048040204 = 1187483780972 := by
        calc
          (5 : ZMod 7512352185857) ^ 1048040204 = (5 : ZMod 7512352185857) ^ (524020102 + 524020102) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 524020102 * (5 : ZMod 7512352185857) ^ 524020102 := by rw [pow_add]
          _ = 1187483780972 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 7512352185857) ^ 2096080409 = 4197814280715 := by
        calc
          (5 : ZMod 7512352185857) ^ 2096080409 = (5 : ZMod 7512352185857) ^ (1048040204 + 1048040204 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1048040204 * (5 : ZMod 7512352185857) ^ 1048040204) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4197814280715 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 7512352185857) ^ 4192160818 = 4802314104543 := by
        calc
          (5 : ZMod 7512352185857) ^ 4192160818 = (5 : ZMod 7512352185857) ^ (2096080409 + 2096080409) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 2096080409 * (5 : ZMod 7512352185857) ^ 2096080409 := by rw [pow_add]
          _ = 4802314104543 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 7512352185857) ^ 8384321636 = 2239340193560 := by
        calc
          (5 : ZMod 7512352185857) ^ 8384321636 = (5 : ZMod 7512352185857) ^ (4192160818 + 4192160818) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 4192160818 * (5 : ZMod 7512352185857) ^ 4192160818 := by rw [pow_add]
          _ = 2239340193560 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 7512352185857) ^ 16768643272 = 2519725500700 := by
        calc
          (5 : ZMod 7512352185857) ^ 16768643272 = (5 : ZMod 7512352185857) ^ (8384321636 + 8384321636) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 8384321636 * (5 : ZMod 7512352185857) ^ 8384321636 := by rw [pow_add]
          _ = 2519725500700 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 7512352185857) ^ 33537286544 = 2336329229051 := by
        calc
          (5 : ZMod 7512352185857) ^ 33537286544 = (5 : ZMod 7512352185857) ^ (16768643272 + 16768643272) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 16768643272 * (5 : ZMod 7512352185857) ^ 16768643272 := by rw [pow_add]
          _ = 2336329229051 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 7512352185857) ^ 67074573088 = 4420215009704 := by
        calc
          (5 : ZMod 7512352185857) ^ 67074573088 = (5 : ZMod 7512352185857) ^ (33537286544 + 33537286544) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 33537286544 * (5 : ZMod 7512352185857) ^ 33537286544 := by rw [pow_add]
          _ = 4420215009704 := by rw [factor_1_34]; decide
      have factor_1_36 : (5 : ZMod 7512352185857) ^ 134149146176 = 2234444955502 := by
        calc
          (5 : ZMod 7512352185857) ^ 134149146176 = (5 : ZMod 7512352185857) ^ (67074573088 + 67074573088) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 67074573088 * (5 : ZMod 7512352185857) ^ 67074573088 := by rw [pow_add]
          _ = 2234444955502 := by rw [factor_1_35]; decide
      have factor_1_37 : (5 : ZMod 7512352185857) ^ 268298292352 = 4867701520364 := by
        calc
          (5 : ZMod 7512352185857) ^ 268298292352 = (5 : ZMod 7512352185857) ^ (134149146176 + 134149146176) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 134149146176 * (5 : ZMod 7512352185857) ^ 134149146176 := by rw [pow_add]
          _ = 4867701520364 := by rw [factor_1_36]; decide
      have factor_1_38 : (5 : ZMod 7512352185857) ^ 536596584704 = 1607014222830 := by
        calc
          (5 : ZMod 7512352185857) ^ 536596584704 = (5 : ZMod 7512352185857) ^ (268298292352 + 268298292352) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 268298292352 * (5 : ZMod 7512352185857) ^ 268298292352 := by rw [pow_add]
          _ = 1607014222830 := by rw [factor_1_37]; decide
      have factor_1_39 : (5 : ZMod 7512352185857) ^ 1073193169408 = 3028392494951 := by
        calc
          (5 : ZMod 7512352185857) ^ 1073193169408 = (5 : ZMod 7512352185857) ^ (536596584704 + 536596584704) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 536596584704 * (5 : ZMod 7512352185857) ^ 536596584704 := by rw [pow_add]
          _ = 3028392494951 := by rw [factor_1_38]; decide
      change (5 : ZMod 7512352185857) ^ 1073193169408 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (5 : ZMod 7512352185857) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 7512352185857) ^ 3 = 125 := by
        calc
          (5 : ZMod 7512352185857) ^ 3 = (5 : ZMod 7512352185857) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1 * (5 : ZMod 7512352185857) ^ 1) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 7512352185857) ^ 6 = 15625 := by
        calc
          (5 : ZMod 7512352185857) ^ 6 = (5 : ZMod 7512352185857) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3 * (5 : ZMod 7512352185857) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 7512352185857) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 7512352185857) ^ 12 = (5 : ZMod 7512352185857) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 6 * (5 : ZMod 7512352185857) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 7512352185857) ^ 25 = 700311820078 := by
        calc
          (5 : ZMod 7512352185857) ^ 25 = (5 : ZMod 7512352185857) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 12 * (5 : ZMod 7512352185857) ^ 12) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 700311820078 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 7512352185857) ^ 51 = 1190095307452 := by
        calc
          (5 : ZMod 7512352185857) ^ 51 = (5 : ZMod 7512352185857) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 25 * (5 : ZMod 7512352185857) ^ 25) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1190095307452 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 7512352185857) ^ 102 = 64009556690 := by
        calc
          (5 : ZMod 7512352185857) ^ 102 = (5 : ZMod 7512352185857) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 51 * (5 : ZMod 7512352185857) ^ 51 := by rw [pow_add]
          _ = 64009556690 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 7512352185857) ^ 204 = 2742554870414 := by
        calc
          (5 : ZMod 7512352185857) ^ 204 = (5 : ZMod 7512352185857) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 102 * (5 : ZMod 7512352185857) ^ 102 := by rw [pow_add]
          _ = 2742554870414 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 7512352185857) ^ 408 = 5768931174849 := by
        calc
          (5 : ZMod 7512352185857) ^ 408 = (5 : ZMod 7512352185857) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 204 * (5 : ZMod 7512352185857) ^ 204 := by rw [pow_add]
          _ = 5768931174849 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 7512352185857) ^ 817 = 4861246182251 := by
        calc
          (5 : ZMod 7512352185857) ^ 817 = (5 : ZMod 7512352185857) ^ (408 + 408 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 408 * (5 : ZMod 7512352185857) ^ 408) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4861246182251 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 7512352185857) ^ 1634 = 5443369397773 := by
        calc
          (5 : ZMod 7512352185857) ^ 1634 = (5 : ZMod 7512352185857) ^ (817 + 817) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 817 * (5 : ZMod 7512352185857) ^ 817 := by rw [pow_add]
          _ = 5443369397773 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 7512352185857) ^ 3268 = 2034243395347 := by
        calc
          (5 : ZMod 7512352185857) ^ 3268 = (5 : ZMod 7512352185857) ^ (1634 + 1634) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1634 * (5 : ZMod 7512352185857) ^ 1634 := by rw [pow_add]
          _ = 2034243395347 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 7512352185857) ^ 6536 = 5376478609251 := by
        calc
          (5 : ZMod 7512352185857) ^ 6536 = (5 : ZMod 7512352185857) ^ (3268 + 3268) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3268 * (5 : ZMod 7512352185857) ^ 3268 := by rw [pow_add]
          _ = 5376478609251 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 7512352185857) ^ 13073 = 1549353197392 := by
        calc
          (5 : ZMod 7512352185857) ^ 13073 = (5 : ZMod 7512352185857) ^ (6536 + 6536 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 6536 * (5 : ZMod 7512352185857) ^ 6536) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1549353197392 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 7512352185857) ^ 26147 = 3739138312327 := by
        calc
          (5 : ZMod 7512352185857) ^ 26147 = (5 : ZMod 7512352185857) ^ (13073 + 13073 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 13073 * (5 : ZMod 7512352185857) ^ 13073) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3739138312327 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 7512352185857) ^ 52294 = 718472510503 := by
        calc
          (5 : ZMod 7512352185857) ^ 52294 = (5 : ZMod 7512352185857) ^ (26147 + 26147) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 26147 * (5 : ZMod 7512352185857) ^ 26147 := by rw [pow_add]
          _ = 718472510503 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 7512352185857) ^ 104588 = 6240664285617 := by
        calc
          (5 : ZMod 7512352185857) ^ 104588 = (5 : ZMod 7512352185857) ^ (52294 + 52294) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 52294 * (5 : ZMod 7512352185857) ^ 52294 := by rw [pow_add]
          _ = 6240664285617 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 7512352185857) ^ 209177 = 6486944587962 := by
        calc
          (5 : ZMod 7512352185857) ^ 209177 = (5 : ZMod 7512352185857) ^ (104588 + 104588 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 104588 * (5 : ZMod 7512352185857) ^ 104588) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6486944587962 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 7512352185857) ^ 418355 = 5139653206638 := by
        calc
          (5 : ZMod 7512352185857) ^ 418355 = (5 : ZMod 7512352185857) ^ (209177 + 209177 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 209177 * (5 : ZMod 7512352185857) ^ 209177) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5139653206638 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 7512352185857) ^ 836710 = 4996455528398 := by
        calc
          (5 : ZMod 7512352185857) ^ 836710 = (5 : ZMod 7512352185857) ^ (418355 + 418355) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 418355 * (5 : ZMod 7512352185857) ^ 418355 := by rw [pow_add]
          _ = 4996455528398 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 7512352185857) ^ 1673421 = 1536820437258 := by
        calc
          (5 : ZMod 7512352185857) ^ 1673421 = (5 : ZMod 7512352185857) ^ (836710 + 836710 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 836710 * (5 : ZMod 7512352185857) ^ 836710) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1536820437258 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 7512352185857) ^ 3346843 = 5745568507528 := by
        calc
          (5 : ZMod 7512352185857) ^ 3346843 = (5 : ZMod 7512352185857) ^ (1673421 + 1673421 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1673421 * (5 : ZMod 7512352185857) ^ 1673421) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5745568507528 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 7512352185857) ^ 6693687 = 4479900435483 := by
        calc
          (5 : ZMod 7512352185857) ^ 6693687 = (5 : ZMod 7512352185857) ^ (3346843 + 3346843 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 3346843 * (5 : ZMod 7512352185857) ^ 3346843) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4479900435483 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 7512352185857) ^ 13387374 = 2713114204982 := by
        calc
          (5 : ZMod 7512352185857) ^ 13387374 = (5 : ZMod 7512352185857) ^ (6693687 + 6693687) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 6693687 * (5 : ZMod 7512352185857) ^ 6693687 := by rw [pow_add]
          _ = 2713114204982 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 7512352185857) ^ 26774749 = 4948217046464 := by
        calc
          (5 : ZMod 7512352185857) ^ 26774749 = (5 : ZMod 7512352185857) ^ (13387374 + 13387374 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 13387374 * (5 : ZMod 7512352185857) ^ 13387374) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4948217046464 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 7512352185857) ^ 53549499 = 437523319298 := by
        calc
          (5 : ZMod 7512352185857) ^ 53549499 = (5 : ZMod 7512352185857) ^ (26774749 + 26774749 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 26774749 * (5 : ZMod 7512352185857) ^ 26774749) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 437523319298 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 7512352185857) ^ 107098999 = 4573636380223 := by
        calc
          (5 : ZMod 7512352185857) ^ 107098999 = (5 : ZMod 7512352185857) ^ (53549499 + 53549499 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 53549499 * (5 : ZMod 7512352185857) ^ 53549499) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4573636380223 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 7512352185857) ^ 214197998 = 5212536209560 := by
        calc
          (5 : ZMod 7512352185857) ^ 214197998 = (5 : ZMod 7512352185857) ^ (107098999 + 107098999) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 107098999 * (5 : ZMod 7512352185857) ^ 107098999 := by rw [pow_add]
          _ = 5212536209560 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 7512352185857) ^ 428395996 = 6799110970087 := by
        calc
          (5 : ZMod 7512352185857) ^ 428395996 = (5 : ZMod 7512352185857) ^ (214197998 + 214197998) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 214197998 * (5 : ZMod 7512352185857) ^ 214197998 := by rw [pow_add]
          _ = 6799110970087 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 7512352185857) ^ 856791992 = 403087805527 := by
        calc
          (5 : ZMod 7512352185857) ^ 856791992 = (5 : ZMod 7512352185857) ^ (428395996 + 428395996) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 428395996 * (5 : ZMod 7512352185857) ^ 428395996 := by rw [pow_add]
          _ = 403087805527 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 7512352185857) ^ 1713583984 = 6249626920235 := by
        calc
          (5 : ZMod 7512352185857) ^ 1713583984 = (5 : ZMod 7512352185857) ^ (856791992 + 856791992) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 856791992 * (5 : ZMod 7512352185857) ^ 856791992 := by rw [pow_add]
          _ = 6249626920235 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 7512352185857) ^ 3427167968 = 752578018943 := by
        calc
          (5 : ZMod 7512352185857) ^ 3427167968 = (5 : ZMod 7512352185857) ^ (1713583984 + 1713583984) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1713583984 * (5 : ZMod 7512352185857) ^ 1713583984 := by rw [pow_add]
          _ = 752578018943 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 7512352185857) ^ 6854335936 = 5765638361956 := by
        calc
          (5 : ZMod 7512352185857) ^ 6854335936 = (5 : ZMod 7512352185857) ^ (3427167968 + 3427167968) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 3427167968 * (5 : ZMod 7512352185857) ^ 3427167968 := by rw [pow_add]
          _ = 5765638361956 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 7512352185857) ^ 13708671872 = 3441080764857 := by
        calc
          (5 : ZMod 7512352185857) ^ 13708671872 = (5 : ZMod 7512352185857) ^ (6854335936 + 6854335936) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 6854335936 * (5 : ZMod 7512352185857) ^ 6854335936 := by rw [pow_add]
          _ = 3441080764857 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 7512352185857) ^ 27417343744 = 968462501244 := by
        calc
          (5 : ZMod 7512352185857) ^ 27417343744 = (5 : ZMod 7512352185857) ^ (13708671872 + 13708671872) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 13708671872 * (5 : ZMod 7512352185857) ^ 13708671872 := by rw [pow_add]
          _ = 968462501244 := by rw [factor_2_33]; decide
      have factor_2_35 : (5 : ZMod 7512352185857) ^ 54834687488 = 2351819296191 := by
        calc
          (5 : ZMod 7512352185857) ^ 54834687488 = (5 : ZMod 7512352185857) ^ (27417343744 + 27417343744) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 27417343744 * (5 : ZMod 7512352185857) ^ 27417343744 := by rw [pow_add]
          _ = 2351819296191 := by rw [factor_2_34]; decide
      change (5 : ZMod 7512352185857) ^ 54834687488 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (5 : ZMod 7512352185857) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 7512352185857) ^ 2 = 25 := by
        calc
          (5 : ZMod 7512352185857) ^ 2 = (5 : ZMod 7512352185857) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1 * (5 : ZMod 7512352185857) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 7512352185857) ^ 5 = 3125 := by
        calc
          (5 : ZMod 7512352185857) ^ 5 = (5 : ZMod 7512352185857) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 2 * (5 : ZMod 7512352185857) ^ 2) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 7512352185857) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 7512352185857) ^ 11 = (5 : ZMod 7512352185857) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 5 * (5 : ZMod 7512352185857) ^ 5) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 7512352185857) ^ 22 = 2770148098956 := by
        calc
          (5 : ZMod 7512352185857) ^ 22 = (5 : ZMod 7512352185857) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 11 * (5 : ZMod 7512352185857) ^ 11 := by rw [pow_add]
          _ = 2770148098956 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 7512352185857) ^ 44 = 1554314890592 := by
        calc
          (5 : ZMod 7512352185857) ^ 44 = (5 : ZMod 7512352185857) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 22 * (5 : ZMod 7512352185857) ^ 22 := by rw [pow_add]
          _ = 1554314890592 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 7512352185857) ^ 88 = 3603227335633 := by
        calc
          (5 : ZMod 7512352185857) ^ 88 = (5 : ZMod 7512352185857) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 44 * (5 : ZMod 7512352185857) ^ 44 := by rw [pow_add]
          _ = 3603227335633 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 7512352185857) ^ 177 = 5812741160745 := by
        calc
          (5 : ZMod 7512352185857) ^ 177 = (5 : ZMod 7512352185857) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 88 * (5 : ZMod 7512352185857) ^ 88) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5812741160745 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 7512352185857) ^ 354 = 2491304307795 := by
        calc
          (5 : ZMod 7512352185857) ^ 354 = (5 : ZMod 7512352185857) ^ (177 + 177) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 177 * (5 : ZMod 7512352185857) ^ 177 := by rw [pow_add]
          _ = 2491304307795 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 7512352185857) ^ 709 = 3851873393937 := by
        calc
          (5 : ZMod 7512352185857) ^ 709 = (5 : ZMod 7512352185857) ^ (354 + 354 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 354 * (5 : ZMod 7512352185857) ^ 354) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3851873393937 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 7512352185857) ^ 1419 = 3479956000318 := by
        calc
          (5 : ZMod 7512352185857) ^ 1419 = (5 : ZMod 7512352185857) ^ (709 + 709 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 709 * (5 : ZMod 7512352185857) ^ 709) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3479956000318 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 7512352185857) ^ 2838 = 5086922982433 := by
        calc
          (5 : ZMod 7512352185857) ^ 2838 = (5 : ZMod 7512352185857) ^ (1419 + 1419) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1419 * (5 : ZMod 7512352185857) ^ 1419 := by rw [pow_add]
          _ = 5086922982433 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 7512352185857) ^ 5676 = 4653234250624 := by
        calc
          (5 : ZMod 7512352185857) ^ 5676 = (5 : ZMod 7512352185857) ^ (2838 + 2838) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 2838 * (5 : ZMod 7512352185857) ^ 2838 := by rw [pow_add]
          _ = 4653234250624 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 7512352185857) ^ 11353 = 3150677034832 := by
        calc
          (5 : ZMod 7512352185857) ^ 11353 = (5 : ZMod 7512352185857) ^ (5676 + 5676 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 5676 * (5 : ZMod 7512352185857) ^ 5676) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3150677034832 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 7512352185857) ^ 22707 = 7377278301183 := by
        calc
          (5 : ZMod 7512352185857) ^ 22707 = (5 : ZMod 7512352185857) ^ (11353 + 11353 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 11353 * (5 : ZMod 7512352185857) ^ 11353) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 7377278301183 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 7512352185857) ^ 45415 = 4505790365004 := by
        calc
          (5 : ZMod 7512352185857) ^ 45415 = (5 : ZMod 7512352185857) ^ (22707 + 22707 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 22707 * (5 : ZMod 7512352185857) ^ 22707) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 4505790365004 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 7512352185857) ^ 90831 = 2379288451258 := by
        calc
          (5 : ZMod 7512352185857) ^ 90831 = (5 : ZMod 7512352185857) ^ (45415 + 45415 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 45415 * (5 : ZMod 7512352185857) ^ 45415) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2379288451258 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 7512352185857) ^ 181663 = 3114843951982 := by
        calc
          (5 : ZMod 7512352185857) ^ 181663 = (5 : ZMod 7512352185857) ^ (90831 + 90831 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 90831 * (5 : ZMod 7512352185857) ^ 90831) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3114843951982 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 7512352185857) ^ 363326 = 4192378618085 := by
        calc
          (5 : ZMod 7512352185857) ^ 363326 = (5 : ZMod 7512352185857) ^ (181663 + 181663) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 181663 * (5 : ZMod 7512352185857) ^ 181663 := by rw [pow_add]
          _ = 4192378618085 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 7512352185857) ^ 726652 = 3222570296402 := by
        calc
          (5 : ZMod 7512352185857) ^ 726652 = (5 : ZMod 7512352185857) ^ (363326 + 363326) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 363326 * (5 : ZMod 7512352185857) ^ 363326 := by rw [pow_add]
          _ = 3222570296402 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 7512352185857) ^ 1453304 = 3969431855553 := by
        calc
          (5 : ZMod 7512352185857) ^ 1453304 = (5 : ZMod 7512352185857) ^ (726652 + 726652) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 726652 * (5 : ZMod 7512352185857) ^ 726652 := by rw [pow_add]
          _ = 3969431855553 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 7512352185857) ^ 2906609 = 5618919711780 := by
        calc
          (5 : ZMod 7512352185857) ^ 2906609 = (5 : ZMod 7512352185857) ^ (1453304 + 1453304 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1453304 * (5 : ZMod 7512352185857) ^ 1453304) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5618919711780 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 7512352185857) ^ 5813218 = 3464497564262 := by
        calc
          (5 : ZMod 7512352185857) ^ 5813218 = (5 : ZMod 7512352185857) ^ (2906609 + 2906609) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 2906609 * (5 : ZMod 7512352185857) ^ 2906609 := by rw [pow_add]
          _ = 3464497564262 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 7512352185857) ^ 11626436 = 251473611563 := by
        calc
          (5 : ZMod 7512352185857) ^ 11626436 = (5 : ZMod 7512352185857) ^ (5813218 + 5813218) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 5813218 * (5 : ZMod 7512352185857) ^ 5813218 := by rw [pow_add]
          _ = 251473611563 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 7512352185857) ^ 23252873 = 326085622380 := by
        calc
          (5 : ZMod 7512352185857) ^ 23252873 = (5 : ZMod 7512352185857) ^ (11626436 + 11626436 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 11626436 * (5 : ZMod 7512352185857) ^ 11626436) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 326085622380 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 7512352185857) ^ 46505746 = 364859464438 := by
        calc
          (5 : ZMod 7512352185857) ^ 46505746 = (5 : ZMod 7512352185857) ^ (23252873 + 23252873) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 23252873 * (5 : ZMod 7512352185857) ^ 23252873 := by rw [pow_add]
          _ = 364859464438 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 7512352185857) ^ 93011492 = 2710175138172 := by
        calc
          (5 : ZMod 7512352185857) ^ 93011492 = (5 : ZMod 7512352185857) ^ (46505746 + 46505746) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 46505746 * (5 : ZMod 7512352185857) ^ 46505746 := by rw [pow_add]
          _ = 2710175138172 := by rw [factor_3_25]; decide
      have factor_3_27 : (5 : ZMod 7512352185857) ^ 186022984 = 7069070004613 := by
        calc
          (5 : ZMod 7512352185857) ^ 186022984 = (5 : ZMod 7512352185857) ^ (93011492 + 93011492) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 93011492 * (5 : ZMod 7512352185857) ^ 93011492 := by rw [pow_add]
          _ = 7069070004613 := by rw [factor_3_26]; decide
      have factor_3_28 : (5 : ZMod 7512352185857) ^ 372045968 = 3298059657937 := by
        calc
          (5 : ZMod 7512352185857) ^ 372045968 = (5 : ZMod 7512352185857) ^ (186022984 + 186022984) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 186022984 * (5 : ZMod 7512352185857) ^ 186022984 := by rw [pow_add]
          _ = 3298059657937 := by rw [factor_3_27]; decide
      have factor_3_29 : (5 : ZMod 7512352185857) ^ 744091936 = 2413606295763 := by
        calc
          (5 : ZMod 7512352185857) ^ 744091936 = (5 : ZMod 7512352185857) ^ (372045968 + 372045968) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 372045968 * (5 : ZMod 7512352185857) ^ 372045968 := by rw [pow_add]
          _ = 2413606295763 := by rw [factor_3_28]; decide
      have factor_3_30 : (5 : ZMod 7512352185857) ^ 1488183872 = 2207763960114 := by
        calc
          (5 : ZMod 7512352185857) ^ 1488183872 = (5 : ZMod 7512352185857) ^ (744091936 + 744091936) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 744091936 * (5 : ZMod 7512352185857) ^ 744091936 := by rw [pow_add]
          _ = 2207763960114 := by rw [factor_3_29]; decide
      have factor_3_31 : (5 : ZMod 7512352185857) ^ 2976367744 = 1541826597311 := by
        calc
          (5 : ZMod 7512352185857) ^ 2976367744 = (5 : ZMod 7512352185857) ^ (1488183872 + 1488183872) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1488183872 * (5 : ZMod 7512352185857) ^ 1488183872 := by rw [pow_add]
          _ = 1541826597311 := by rw [factor_3_30]; decide
      have factor_3_32 : (5 : ZMod 7512352185857) ^ 5952735488 = 5788152578849 := by
        calc
          (5 : ZMod 7512352185857) ^ 5952735488 = (5 : ZMod 7512352185857) ^ (2976367744 + 2976367744) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 2976367744 * (5 : ZMod 7512352185857) ^ 2976367744 := by rw [pow_add]
          _ = 5788152578849 := by rw [factor_3_31]; decide
      have factor_3_33 : (5 : ZMod 7512352185857) ^ 11905470976 = 1900619226443 := by
        calc
          (5 : ZMod 7512352185857) ^ 11905470976 = (5 : ZMod 7512352185857) ^ (5952735488 + 5952735488) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 5952735488 * (5 : ZMod 7512352185857) ^ 5952735488 := by rw [pow_add]
          _ = 1900619226443 := by rw [factor_3_32]; decide
      change (5 : ZMod 7512352185857) ^ 11905470976 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (5 : ZMod 7512352185857) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 7512352185857) ^ 2 = 25 := by
        calc
          (5 : ZMod 7512352185857) ^ 2 = (5 : ZMod 7512352185857) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1 * (5 : ZMod 7512352185857) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 7512352185857) ^ 4 = 625 := by
        calc
          (5 : ZMod 7512352185857) ^ 4 = (5 : ZMod 7512352185857) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 2 * (5 : ZMod 7512352185857) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 7512352185857) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 7512352185857) ^ 9 = (5 : ZMod 7512352185857) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 4 * (5 : ZMod 7512352185857) ^ 4) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 7512352185857) ^ 18 = 3814697265625 := by
        calc
          (5 : ZMod 7512352185857) ^ 18 = (5 : ZMod 7512352185857) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 9 * (5 : ZMod 7512352185857) ^ 9 := by rw [pow_add]
          _ = 3814697265625 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 7512352185857) ^ 36 = 601357554725 := by
        calc
          (5 : ZMod 7512352185857) ^ 36 = (5 : ZMod 7512352185857) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 18 * (5 : ZMod 7512352185857) ^ 18 := by rw [pow_add]
          _ = 601357554725 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 7512352185857) ^ 73 = 7504483174074 := by
        calc
          (5 : ZMod 7512352185857) ^ 73 = (5 : ZMod 7512352185857) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 36 * (5 : ZMod 7512352185857) ^ 36) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 7504483174074 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 7512352185857) ^ 147 = 3809843751448 := by
        calc
          (5 : ZMod 7512352185857) ^ 147 = (5 : ZMod 7512352185857) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 73 * (5 : ZMod 7512352185857) ^ 73) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3809843751448 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 7512352185857) ^ 295 = 2766110147201 := by
        calc
          (5 : ZMod 7512352185857) ^ 295 = (5 : ZMod 7512352185857) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 147 * (5 : ZMod 7512352185857) ^ 147) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2766110147201 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 7512352185857) ^ 590 = 2691444627795 := by
        calc
          (5 : ZMod 7512352185857) ^ 590 = (5 : ZMod 7512352185857) ^ (295 + 295) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 295 * (5 : ZMod 7512352185857) ^ 295 := by rw [pow_add]
          _ = 2691444627795 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 7512352185857) ^ 1181 = 2659342732326 := by
        calc
          (5 : ZMod 7512352185857) ^ 1181 = (5 : ZMod 7512352185857) ^ (590 + 590 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 590 * (5 : ZMod 7512352185857) ^ 590) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 2659342732326 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 7512352185857) ^ 2363 = 3299538054868 := by
        calc
          (5 : ZMod 7512352185857) ^ 2363 = (5 : ZMod 7512352185857) ^ (1181 + 1181 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 1181 * (5 : ZMod 7512352185857) ^ 1181) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3299538054868 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 7512352185857) ^ 4727 = 5915473106796 := by
        calc
          (5 : ZMod 7512352185857) ^ 4727 = (5 : ZMod 7512352185857) ^ (2363 + 2363 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 2363 * (5 : ZMod 7512352185857) ^ 2363) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 5915473106796 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 7512352185857) ^ 9455 = 6892091719786 := by
        calc
          (5 : ZMod 7512352185857) ^ 9455 = (5 : ZMod 7512352185857) ^ (4727 + 4727 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 4727 * (5 : ZMod 7512352185857) ^ 4727) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 6892091719786 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 7512352185857) ^ 18910 = 5404626574324 := by
        calc
          (5 : ZMod 7512352185857) ^ 18910 = (5 : ZMod 7512352185857) ^ (9455 + 9455) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 9455 * (5 : ZMod 7512352185857) ^ 9455 := by rw [pow_add]
          _ = 5404626574324 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 7512352185857) ^ 37820 = 4535356998908 := by
        calc
          (5 : ZMod 7512352185857) ^ 37820 = (5 : ZMod 7512352185857) ^ (18910 + 18910) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 18910 * (5 : ZMod 7512352185857) ^ 18910 := by rw [pow_add]
          _ = 4535356998908 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 7512352185857) ^ 75641 = 386792082292 := by
        calc
          (5 : ZMod 7512352185857) ^ 75641 = (5 : ZMod 7512352185857) ^ (37820 + 37820 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 37820 * (5 : ZMod 7512352185857) ^ 37820) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 386792082292 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 7512352185857) ^ 151282 = 5384582113488 := by
        calc
          (5 : ZMod 7512352185857) ^ 151282 = (5 : ZMod 7512352185857) ^ (75641 + 75641) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 75641 * (5 : ZMod 7512352185857) ^ 75641 := by rw [pow_add]
          _ = 5384582113488 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 7512352185857) ^ 302564 = 4961987021855 := by
        calc
          (5 : ZMod 7512352185857) ^ 302564 = (5 : ZMod 7512352185857) ^ (151282 + 151282) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 151282 * (5 : ZMod 7512352185857) ^ 151282 := by rw [pow_add]
          _ = 4961987021855 := by rw [factor_4_17]; decide
      have factor_4_19 : (5 : ZMod 7512352185857) ^ 605129 = 3461296516124 := by
        calc
          (5 : ZMod 7512352185857) ^ 605129 = (5 : ZMod 7512352185857) ^ (302564 + 302564 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = ((5 : ZMod 7512352185857) ^ 302564 * (5 : ZMod 7512352185857) ^ 302564) * (5 : ZMod 7512352185857) := by rw [pow_succ, pow_add]
          _ = 3461296516124 := by rw [factor_4_18]; decide
      have factor_4_20 : (5 : ZMod 7512352185857) ^ 1210258 = 3907920132294 := by
        calc
          (5 : ZMod 7512352185857) ^ 1210258 = (5 : ZMod 7512352185857) ^ (605129 + 605129) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 605129 * (5 : ZMod 7512352185857) ^ 605129 := by rw [pow_add]
          _ = 3907920132294 := by rw [factor_4_19]; decide
      have factor_4_21 : (5 : ZMod 7512352185857) ^ 2420516 = 1419686126270 := by
        calc
          (5 : ZMod 7512352185857) ^ 2420516 = (5 : ZMod 7512352185857) ^ (1210258 + 1210258) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 1210258 * (5 : ZMod 7512352185857) ^ 1210258 := by rw [pow_add]
          _ = 1419686126270 := by rw [factor_4_20]; decide
      have factor_4_22 : (5 : ZMod 7512352185857) ^ 4841032 = 238086512076 := by
        calc
          (5 : ZMod 7512352185857) ^ 4841032 = (5 : ZMod 7512352185857) ^ (2420516 + 2420516) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 2420516 * (5 : ZMod 7512352185857) ^ 2420516 := by rw [pow_add]
          _ = 238086512076 := by rw [factor_4_21]; decide
      have factor_4_23 : (5 : ZMod 7512352185857) ^ 9682064 = 57433632159 := by
        calc
          (5 : ZMod 7512352185857) ^ 9682064 = (5 : ZMod 7512352185857) ^ (4841032 + 4841032) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 4841032 * (5 : ZMod 7512352185857) ^ 4841032 := by rw [pow_add]
          _ = 57433632159 := by rw [factor_4_22]; decide
      have factor_4_24 : (5 : ZMod 7512352185857) ^ 19364128 = 3247366484297 := by
        calc
          (5 : ZMod 7512352185857) ^ 19364128 = (5 : ZMod 7512352185857) ^ (9682064 + 9682064) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 9682064 * (5 : ZMod 7512352185857) ^ 9682064 := by rw [pow_add]
          _ = 3247366484297 := by rw [factor_4_23]; decide
      have factor_4_25 : (5 : ZMod 7512352185857) ^ 38728256 = 6728209519185 := by
        calc
          (5 : ZMod 7512352185857) ^ 38728256 = (5 : ZMod 7512352185857) ^ (19364128 + 19364128) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 19364128 * (5 : ZMod 7512352185857) ^ 19364128 := by rw [pow_add]
          _ = 6728209519185 := by rw [factor_4_24]; decide
      have factor_4_26 : (5 : ZMod 7512352185857) ^ 77456512 = 2114773485263 := by
        calc
          (5 : ZMod 7512352185857) ^ 77456512 = (5 : ZMod 7512352185857) ^ (38728256 + 38728256) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 38728256 * (5 : ZMod 7512352185857) ^ 38728256 := by rw [pow_add]
          _ = 2114773485263 := by rw [factor_4_25]; decide
      have factor_4_27 : (5 : ZMod 7512352185857) ^ 154913024 = 1891422121096 := by
        calc
          (5 : ZMod 7512352185857) ^ 154913024 = (5 : ZMod 7512352185857) ^ (77456512 + 77456512) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 77456512 * (5 : ZMod 7512352185857) ^ 77456512 := by rw [pow_add]
          _ = 1891422121096 := by rw [factor_4_26]; decide
      have factor_4_28 : (5 : ZMod 7512352185857) ^ 309826048 = 2186092358972 := by
        calc
          (5 : ZMod 7512352185857) ^ 309826048 = (5 : ZMod 7512352185857) ^ (154913024 + 154913024) :=
            congrArg (fun n : ℕ => (5 : ZMod 7512352185857) ^ n) (by norm_num)
          _ = (5 : ZMod 7512352185857) ^ 154913024 * (5 : ZMod 7512352185857) ^ 154913024 := by rw [pow_add]
          _ = 2186092358972 := by rw [factor_4_27]; decide
      change (5 : ZMod 7512352185857) ^ 309826048 ≠ 1
      rw [factor_4_28]
      decide

#print axioms prime_lucas_7512352185857

end TotientTailPeriodKiller
end Erdos249257
