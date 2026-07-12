import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3058504461911 : Nat.Prime 3058504461911 := by
  apply lucas_primality 3058504461911 (13 : ZMod 3058504461911)
  ·
      have fermat_0 : (13 : ZMod 3058504461911) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 3058504461911) ^ 2 = 169 := by
        calc
          (13 : ZMod 3058504461911) ^ 2 = (13 : ZMod 3058504461911) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1 * (13 : ZMod 3058504461911) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 3058504461911) ^ 5 = 371293 := by
        calc
          (13 : ZMod 3058504461911) ^ 5 = (13 : ZMod 3058504461911) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 2 * (13 : ZMod 3058504461911) ^ 2) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 3058504461911) ^ 11 = 1792160394037 := by
        calc
          (13 : ZMod 3058504461911) ^ 11 = (13 : ZMod 3058504461911) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 5 * (13 : ZMod 3058504461911) ^ 5) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1792160394037 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 3058504461911) ^ 22 = 831899614366 := by
        calc
          (13 : ZMod 3058504461911) ^ 22 = (13 : ZMod 3058504461911) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 11 * (13 : ZMod 3058504461911) ^ 11 := by rw [pow_add]
          _ = 831899614366 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 3058504461911) ^ 44 = 1676422010641 := by
        calc
          (13 : ZMod 3058504461911) ^ 44 = (13 : ZMod 3058504461911) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 22 * (13 : ZMod 3058504461911) ^ 22 := by rw [pow_add]
          _ = 1676422010641 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 3058504461911) ^ 89 = 1360975475918 := by
        calc
          (13 : ZMod 3058504461911) ^ 89 = (13 : ZMod 3058504461911) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 44 * (13 : ZMod 3058504461911) ^ 44) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1360975475918 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 3058504461911) ^ 178 = 1846825321239 := by
        calc
          (13 : ZMod 3058504461911) ^ 178 = (13 : ZMod 3058504461911) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 89 * (13 : ZMod 3058504461911) ^ 89 := by rw [pow_add]
          _ = 1846825321239 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 3058504461911) ^ 356 = 1562966305541 := by
        calc
          (13 : ZMod 3058504461911) ^ 356 = (13 : ZMod 3058504461911) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 178 * (13 : ZMod 3058504461911) ^ 178 := by rw [pow_add]
          _ = 1562966305541 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 3058504461911) ^ 712 = 1451861506491 := by
        calc
          (13 : ZMod 3058504461911) ^ 712 = (13 : ZMod 3058504461911) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 356 * (13 : ZMod 3058504461911) ^ 356 := by rw [pow_add]
          _ = 1451861506491 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 3058504461911) ^ 1424 = 1835588680235 := by
        calc
          (13 : ZMod 3058504461911) ^ 1424 = (13 : ZMod 3058504461911) ^ (712 + 712) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 712 * (13 : ZMod 3058504461911) ^ 712 := by rw [pow_add]
          _ = 1835588680235 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 3058504461911) ^ 2848 = 194515894 := by
        calc
          (13 : ZMod 3058504461911) ^ 2848 = (13 : ZMod 3058504461911) ^ (1424 + 1424) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1424 * (13 : ZMod 3058504461911) ^ 1424 := by rw [pow_add]
          _ = 194515894 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 3058504461911) ^ 5696 = 2732824780166 := by
        calc
          (13 : ZMod 3058504461911) ^ 5696 = (13 : ZMod 3058504461911) ^ (2848 + 2848) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 2848 * (13 : ZMod 3058504461911) ^ 2848 := by rw [pow_add]
          _ = 2732824780166 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 3058504461911) ^ 11393 = 2210078506080 := by
        calc
          (13 : ZMod 3058504461911) ^ 11393 = (13 : ZMod 3058504461911) ^ (5696 + 5696 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 5696 * (13 : ZMod 3058504461911) ^ 5696) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2210078506080 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 3058504461911) ^ 22787 = 2402500142202 := by
        calc
          (13 : ZMod 3058504461911) ^ 22787 = (13 : ZMod 3058504461911) ^ (11393 + 11393 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 11393 * (13 : ZMod 3058504461911) ^ 11393) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2402500142202 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 3058504461911) ^ 45575 = 2697516046635 := by
        calc
          (13 : ZMod 3058504461911) ^ 45575 = (13 : ZMod 3058504461911) ^ (22787 + 22787 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 22787 * (13 : ZMod 3058504461911) ^ 22787) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2697516046635 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 3058504461911) ^ 91150 = 1757058558913 := by
        calc
          (13 : ZMod 3058504461911) ^ 91150 = (13 : ZMod 3058504461911) ^ (45575 + 45575) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 45575 * (13 : ZMod 3058504461911) ^ 45575 := by rw [pow_add]
          _ = 1757058558913 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 3058504461911) ^ 182301 = 1536870362536 := by
        calc
          (13 : ZMod 3058504461911) ^ 182301 = (13 : ZMod 3058504461911) ^ (91150 + 91150 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 91150 * (13 : ZMod 3058504461911) ^ 91150) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1536870362536 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 3058504461911) ^ 364602 = 2991002835865 := by
        calc
          (13 : ZMod 3058504461911) ^ 364602 = (13 : ZMod 3058504461911) ^ (182301 + 182301) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 182301 * (13 : ZMod 3058504461911) ^ 182301 := by rw [pow_add]
          _ = 2991002835865 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 3058504461911) ^ 729204 = 2300443116653 := by
        calc
          (13 : ZMod 3058504461911) ^ 729204 = (13 : ZMod 3058504461911) ^ (364602 + 364602) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 364602 * (13 : ZMod 3058504461911) ^ 364602 := by rw [pow_add]
          _ = 2300443116653 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 3058504461911) ^ 1458408 = 909955157850 := by
        calc
          (13 : ZMod 3058504461911) ^ 1458408 = (13 : ZMod 3058504461911) ^ (729204 + 729204) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 729204 * (13 : ZMod 3058504461911) ^ 729204 := by rw [pow_add]
          _ = 909955157850 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 3058504461911) ^ 2916817 = 2866085690957 := by
        calc
          (13 : ZMod 3058504461911) ^ 2916817 = (13 : ZMod 3058504461911) ^ (1458408 + 1458408 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1458408 * (13 : ZMod 3058504461911) ^ 1458408) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2866085690957 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 3058504461911) ^ 5833634 = 309927725565 := by
        calc
          (13 : ZMod 3058504461911) ^ 5833634 = (13 : ZMod 3058504461911) ^ (2916817 + 2916817) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 2916817 * (13 : ZMod 3058504461911) ^ 2916817 := by rw [pow_add]
          _ = 309927725565 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 3058504461911) ^ 11667268 = 2428610450058 := by
        calc
          (13 : ZMod 3058504461911) ^ 11667268 = (13 : ZMod 3058504461911) ^ (5833634 + 5833634) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 5833634 * (13 : ZMod 3058504461911) ^ 5833634 := by rw [pow_add]
          _ = 2428610450058 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 3058504461911) ^ 23334537 = 2284618492603 := by
        calc
          (13 : ZMod 3058504461911) ^ 23334537 = (13 : ZMod 3058504461911) ^ (11667268 + 11667268 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 11667268 * (13 : ZMod 3058504461911) ^ 11667268) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2284618492603 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 3058504461911) ^ 46669074 = 412235504541 := by
        calc
          (13 : ZMod 3058504461911) ^ 46669074 = (13 : ZMod 3058504461911) ^ (23334537 + 23334537) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 23334537 * (13 : ZMod 3058504461911) ^ 23334537 := by rw [pow_add]
          _ = 412235504541 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 3058504461911) ^ 93338148 = 2055070584498 := by
        calc
          (13 : ZMod 3058504461911) ^ 93338148 = (13 : ZMod 3058504461911) ^ (46669074 + 46669074) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 46669074 * (13 : ZMod 3058504461911) ^ 46669074 := by rw [pow_add]
          _ = 2055070584498 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 3058504461911) ^ 186676297 = 2110676608119 := by
        calc
          (13 : ZMod 3058504461911) ^ 186676297 = (13 : ZMod 3058504461911) ^ (93338148 + 93338148 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 93338148 * (13 : ZMod 3058504461911) ^ 93338148) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2110676608119 := by rw [fermat_26]; decide
      have fermat_28 : (13 : ZMod 3058504461911) ^ 373352595 = 1447532881443 := by
        calc
          (13 : ZMod 3058504461911) ^ 373352595 = (13 : ZMod 3058504461911) ^ (186676297 + 186676297 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 186676297 * (13 : ZMod 3058504461911) ^ 186676297) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1447532881443 := by rw [fermat_27]; decide
      have fermat_29 : (13 : ZMod 3058504461911) ^ 746705190 = 385285962233 := by
        calc
          (13 : ZMod 3058504461911) ^ 746705190 = (13 : ZMod 3058504461911) ^ (373352595 + 373352595) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 373352595 * (13 : ZMod 3058504461911) ^ 373352595 := by rw [pow_add]
          _ = 385285962233 := by rw [fermat_28]; decide
      have fermat_30 : (13 : ZMod 3058504461911) ^ 1493410381 = 2831541777283 := by
        calc
          (13 : ZMod 3058504461911) ^ 1493410381 = (13 : ZMod 3058504461911) ^ (746705190 + 746705190 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 746705190 * (13 : ZMod 3058504461911) ^ 746705190) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2831541777283 := by rw [fermat_29]; decide
      have fermat_31 : (13 : ZMod 3058504461911) ^ 2986820763 = 1487688312659 := by
        calc
          (13 : ZMod 3058504461911) ^ 2986820763 = (13 : ZMod 3058504461911) ^ (1493410381 + 1493410381 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1493410381 * (13 : ZMod 3058504461911) ^ 1493410381) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1487688312659 := by rw [fermat_30]; decide
      have fermat_32 : (13 : ZMod 3058504461911) ^ 5973641527 = 2979810449824 := by
        calc
          (13 : ZMod 3058504461911) ^ 5973641527 = (13 : ZMod 3058504461911) ^ (2986820763 + 2986820763 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 2986820763 * (13 : ZMod 3058504461911) ^ 2986820763) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2979810449824 := by rw [fermat_31]; decide
      have fermat_33 : (13 : ZMod 3058504461911) ^ 11947283054 = 2979837281756 := by
        calc
          (13 : ZMod 3058504461911) ^ 11947283054 = (13 : ZMod 3058504461911) ^ (5973641527 + 5973641527) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 5973641527 * (13 : ZMod 3058504461911) ^ 5973641527 := by rw [pow_add]
          _ = 2979837281756 := by rw [fermat_32]; decide
      have fermat_34 : (13 : ZMod 3058504461911) ^ 23894566108 = 281882688644 := by
        calc
          (13 : ZMod 3058504461911) ^ 23894566108 = (13 : ZMod 3058504461911) ^ (11947283054 + 11947283054) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 11947283054 * (13 : ZMod 3058504461911) ^ 11947283054 := by rw [pow_add]
          _ = 281882688644 := by rw [fermat_33]; decide
      have fermat_35 : (13 : ZMod 3058504461911) ^ 47789132217 = 2692429346332 := by
        calc
          (13 : ZMod 3058504461911) ^ 47789132217 = (13 : ZMod 3058504461911) ^ (23894566108 + 23894566108 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 23894566108 * (13 : ZMod 3058504461911) ^ 23894566108) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2692429346332 := by rw [fermat_34]; decide
      have fermat_36 : (13 : ZMod 3058504461911) ^ 95578264434 = 2700065790944 := by
        calc
          (13 : ZMod 3058504461911) ^ 95578264434 = (13 : ZMod 3058504461911) ^ (47789132217 + 47789132217) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 47789132217 * (13 : ZMod 3058504461911) ^ 47789132217 := by rw [pow_add]
          _ = 2700065790944 := by rw [fermat_35]; decide
      have fermat_37 : (13 : ZMod 3058504461911) ^ 191156528869 = 1550474343767 := by
        calc
          (13 : ZMod 3058504461911) ^ 191156528869 = (13 : ZMod 3058504461911) ^ (95578264434 + 95578264434 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 95578264434 * (13 : ZMod 3058504461911) ^ 95578264434) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1550474343767 := by rw [fermat_36]; decide
      have fermat_38 : (13 : ZMod 3058504461911) ^ 382313057738 = 1730376796715 := by
        calc
          (13 : ZMod 3058504461911) ^ 382313057738 = (13 : ZMod 3058504461911) ^ (191156528869 + 191156528869) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 191156528869 * (13 : ZMod 3058504461911) ^ 191156528869 := by rw [pow_add]
          _ = 1730376796715 := by rw [fermat_37]; decide
      have fermat_39 : (13 : ZMod 3058504461911) ^ 764626115477 = 831941996777 := by
        calc
          (13 : ZMod 3058504461911) ^ 764626115477 = (13 : ZMod 3058504461911) ^ (382313057738 + 382313057738 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 382313057738 * (13 : ZMod 3058504461911) ^ 382313057738) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 831941996777 := by rw [fermat_38]; decide
      have fermat_40 : (13 : ZMod 3058504461911) ^ 1529252230955 = 3058504461910 := by
        calc
          (13 : ZMod 3058504461911) ^ 1529252230955 = (13 : ZMod 3058504461911) ^ (764626115477 + 764626115477 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 764626115477 * (13 : ZMod 3058504461911) ^ 764626115477) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 3058504461910 := by rw [fermat_39]; decide
      have fermat_41 : (13 : ZMod 3058504461911) ^ 3058504461910 = 1 := by
        calc
          (13 : ZMod 3058504461911) ^ 3058504461910 = (13 : ZMod 3058504461911) ^ (1529252230955 + 1529252230955) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1529252230955 * (13 : ZMod 3058504461911) ^ 1529252230955 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (211, 1), (1667, 1), (869543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (211, 1), (1667, 1), (869543, 1)] : List FactorBlock).map factorBlockValue).prod = 3058504461911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 3058504461911) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 3058504461911) ^ 2 = 169 := by
        calc
          (13 : ZMod 3058504461911) ^ 2 = (13 : ZMod 3058504461911) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1 * (13 : ZMod 3058504461911) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 3058504461911) ^ 5 = 371293 := by
        calc
          (13 : ZMod 3058504461911) ^ 5 = (13 : ZMod 3058504461911) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 2 * (13 : ZMod 3058504461911) ^ 2) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 3058504461911) ^ 11 = 1792160394037 := by
        calc
          (13 : ZMod 3058504461911) ^ 11 = (13 : ZMod 3058504461911) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 5 * (13 : ZMod 3058504461911) ^ 5) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1792160394037 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 3058504461911) ^ 22 = 831899614366 := by
        calc
          (13 : ZMod 3058504461911) ^ 22 = (13 : ZMod 3058504461911) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 11 * (13 : ZMod 3058504461911) ^ 11 := by rw [pow_add]
          _ = 831899614366 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 3058504461911) ^ 44 = 1676422010641 := by
        calc
          (13 : ZMod 3058504461911) ^ 44 = (13 : ZMod 3058504461911) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 22 * (13 : ZMod 3058504461911) ^ 22 := by rw [pow_add]
          _ = 1676422010641 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 3058504461911) ^ 89 = 1360975475918 := by
        calc
          (13 : ZMod 3058504461911) ^ 89 = (13 : ZMod 3058504461911) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 44 * (13 : ZMod 3058504461911) ^ 44) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1360975475918 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 3058504461911) ^ 178 = 1846825321239 := by
        calc
          (13 : ZMod 3058504461911) ^ 178 = (13 : ZMod 3058504461911) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 89 * (13 : ZMod 3058504461911) ^ 89 := by rw [pow_add]
          _ = 1846825321239 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 3058504461911) ^ 356 = 1562966305541 := by
        calc
          (13 : ZMod 3058504461911) ^ 356 = (13 : ZMod 3058504461911) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 178 * (13 : ZMod 3058504461911) ^ 178 := by rw [pow_add]
          _ = 1562966305541 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 3058504461911) ^ 712 = 1451861506491 := by
        calc
          (13 : ZMod 3058504461911) ^ 712 = (13 : ZMod 3058504461911) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 356 * (13 : ZMod 3058504461911) ^ 356 := by rw [pow_add]
          _ = 1451861506491 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 3058504461911) ^ 1424 = 1835588680235 := by
        calc
          (13 : ZMod 3058504461911) ^ 1424 = (13 : ZMod 3058504461911) ^ (712 + 712) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 712 * (13 : ZMod 3058504461911) ^ 712 := by rw [pow_add]
          _ = 1835588680235 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 3058504461911) ^ 2848 = 194515894 := by
        calc
          (13 : ZMod 3058504461911) ^ 2848 = (13 : ZMod 3058504461911) ^ (1424 + 1424) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1424 * (13 : ZMod 3058504461911) ^ 1424 := by rw [pow_add]
          _ = 194515894 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 3058504461911) ^ 5696 = 2732824780166 := by
        calc
          (13 : ZMod 3058504461911) ^ 5696 = (13 : ZMod 3058504461911) ^ (2848 + 2848) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 2848 * (13 : ZMod 3058504461911) ^ 2848 := by rw [pow_add]
          _ = 2732824780166 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 3058504461911) ^ 11393 = 2210078506080 := by
        calc
          (13 : ZMod 3058504461911) ^ 11393 = (13 : ZMod 3058504461911) ^ (5696 + 5696 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 5696 * (13 : ZMod 3058504461911) ^ 5696) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2210078506080 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 3058504461911) ^ 22787 = 2402500142202 := by
        calc
          (13 : ZMod 3058504461911) ^ 22787 = (13 : ZMod 3058504461911) ^ (11393 + 11393 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 11393 * (13 : ZMod 3058504461911) ^ 11393) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2402500142202 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 3058504461911) ^ 45575 = 2697516046635 := by
        calc
          (13 : ZMod 3058504461911) ^ 45575 = (13 : ZMod 3058504461911) ^ (22787 + 22787 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 22787 * (13 : ZMod 3058504461911) ^ 22787) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2697516046635 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 3058504461911) ^ 91150 = 1757058558913 := by
        calc
          (13 : ZMod 3058504461911) ^ 91150 = (13 : ZMod 3058504461911) ^ (45575 + 45575) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 45575 * (13 : ZMod 3058504461911) ^ 45575 := by rw [pow_add]
          _ = 1757058558913 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 3058504461911) ^ 182301 = 1536870362536 := by
        calc
          (13 : ZMod 3058504461911) ^ 182301 = (13 : ZMod 3058504461911) ^ (91150 + 91150 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 91150 * (13 : ZMod 3058504461911) ^ 91150) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1536870362536 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 3058504461911) ^ 364602 = 2991002835865 := by
        calc
          (13 : ZMod 3058504461911) ^ 364602 = (13 : ZMod 3058504461911) ^ (182301 + 182301) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 182301 * (13 : ZMod 3058504461911) ^ 182301 := by rw [pow_add]
          _ = 2991002835865 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 3058504461911) ^ 729204 = 2300443116653 := by
        calc
          (13 : ZMod 3058504461911) ^ 729204 = (13 : ZMod 3058504461911) ^ (364602 + 364602) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 364602 * (13 : ZMod 3058504461911) ^ 364602 := by rw [pow_add]
          _ = 2300443116653 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 3058504461911) ^ 1458408 = 909955157850 := by
        calc
          (13 : ZMod 3058504461911) ^ 1458408 = (13 : ZMod 3058504461911) ^ (729204 + 729204) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 729204 * (13 : ZMod 3058504461911) ^ 729204 := by rw [pow_add]
          _ = 909955157850 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 3058504461911) ^ 2916817 = 2866085690957 := by
        calc
          (13 : ZMod 3058504461911) ^ 2916817 = (13 : ZMod 3058504461911) ^ (1458408 + 1458408 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1458408 * (13 : ZMod 3058504461911) ^ 1458408) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2866085690957 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 3058504461911) ^ 5833634 = 309927725565 := by
        calc
          (13 : ZMod 3058504461911) ^ 5833634 = (13 : ZMod 3058504461911) ^ (2916817 + 2916817) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 2916817 * (13 : ZMod 3058504461911) ^ 2916817 := by rw [pow_add]
          _ = 309927725565 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 3058504461911) ^ 11667268 = 2428610450058 := by
        calc
          (13 : ZMod 3058504461911) ^ 11667268 = (13 : ZMod 3058504461911) ^ (5833634 + 5833634) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 5833634 * (13 : ZMod 3058504461911) ^ 5833634 := by rw [pow_add]
          _ = 2428610450058 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 3058504461911) ^ 23334537 = 2284618492603 := by
        calc
          (13 : ZMod 3058504461911) ^ 23334537 = (13 : ZMod 3058504461911) ^ (11667268 + 11667268 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 11667268 * (13 : ZMod 3058504461911) ^ 11667268) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2284618492603 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 3058504461911) ^ 46669074 = 412235504541 := by
        calc
          (13 : ZMod 3058504461911) ^ 46669074 = (13 : ZMod 3058504461911) ^ (23334537 + 23334537) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 23334537 * (13 : ZMod 3058504461911) ^ 23334537 := by rw [pow_add]
          _ = 412235504541 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 3058504461911) ^ 93338148 = 2055070584498 := by
        calc
          (13 : ZMod 3058504461911) ^ 93338148 = (13 : ZMod 3058504461911) ^ (46669074 + 46669074) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 46669074 * (13 : ZMod 3058504461911) ^ 46669074 := by rw [pow_add]
          _ = 2055070584498 := by rw [factor_0_25]; decide
      have factor_0_27 : (13 : ZMod 3058504461911) ^ 186676297 = 2110676608119 := by
        calc
          (13 : ZMod 3058504461911) ^ 186676297 = (13 : ZMod 3058504461911) ^ (93338148 + 93338148 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 93338148 * (13 : ZMod 3058504461911) ^ 93338148) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2110676608119 := by rw [factor_0_26]; decide
      have factor_0_28 : (13 : ZMod 3058504461911) ^ 373352595 = 1447532881443 := by
        calc
          (13 : ZMod 3058504461911) ^ 373352595 = (13 : ZMod 3058504461911) ^ (186676297 + 186676297 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 186676297 * (13 : ZMod 3058504461911) ^ 186676297) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1447532881443 := by rw [factor_0_27]; decide
      have factor_0_29 : (13 : ZMod 3058504461911) ^ 746705190 = 385285962233 := by
        calc
          (13 : ZMod 3058504461911) ^ 746705190 = (13 : ZMod 3058504461911) ^ (373352595 + 373352595) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 373352595 * (13 : ZMod 3058504461911) ^ 373352595 := by rw [pow_add]
          _ = 385285962233 := by rw [factor_0_28]; decide
      have factor_0_30 : (13 : ZMod 3058504461911) ^ 1493410381 = 2831541777283 := by
        calc
          (13 : ZMod 3058504461911) ^ 1493410381 = (13 : ZMod 3058504461911) ^ (746705190 + 746705190 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 746705190 * (13 : ZMod 3058504461911) ^ 746705190) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2831541777283 := by rw [factor_0_29]; decide
      have factor_0_31 : (13 : ZMod 3058504461911) ^ 2986820763 = 1487688312659 := by
        calc
          (13 : ZMod 3058504461911) ^ 2986820763 = (13 : ZMod 3058504461911) ^ (1493410381 + 1493410381 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1493410381 * (13 : ZMod 3058504461911) ^ 1493410381) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1487688312659 := by rw [factor_0_30]; decide
      have factor_0_32 : (13 : ZMod 3058504461911) ^ 5973641527 = 2979810449824 := by
        calc
          (13 : ZMod 3058504461911) ^ 5973641527 = (13 : ZMod 3058504461911) ^ (2986820763 + 2986820763 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 2986820763 * (13 : ZMod 3058504461911) ^ 2986820763) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2979810449824 := by rw [factor_0_31]; decide
      have factor_0_33 : (13 : ZMod 3058504461911) ^ 11947283054 = 2979837281756 := by
        calc
          (13 : ZMod 3058504461911) ^ 11947283054 = (13 : ZMod 3058504461911) ^ (5973641527 + 5973641527) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 5973641527 * (13 : ZMod 3058504461911) ^ 5973641527 := by rw [pow_add]
          _ = 2979837281756 := by rw [factor_0_32]; decide
      have factor_0_34 : (13 : ZMod 3058504461911) ^ 23894566108 = 281882688644 := by
        calc
          (13 : ZMod 3058504461911) ^ 23894566108 = (13 : ZMod 3058504461911) ^ (11947283054 + 11947283054) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 11947283054 * (13 : ZMod 3058504461911) ^ 11947283054 := by rw [pow_add]
          _ = 281882688644 := by rw [factor_0_33]; decide
      have factor_0_35 : (13 : ZMod 3058504461911) ^ 47789132217 = 2692429346332 := by
        calc
          (13 : ZMod 3058504461911) ^ 47789132217 = (13 : ZMod 3058504461911) ^ (23894566108 + 23894566108 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 23894566108 * (13 : ZMod 3058504461911) ^ 23894566108) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2692429346332 := by rw [factor_0_34]; decide
      have factor_0_36 : (13 : ZMod 3058504461911) ^ 95578264434 = 2700065790944 := by
        calc
          (13 : ZMod 3058504461911) ^ 95578264434 = (13 : ZMod 3058504461911) ^ (47789132217 + 47789132217) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 47789132217 * (13 : ZMod 3058504461911) ^ 47789132217 := by rw [pow_add]
          _ = 2700065790944 := by rw [factor_0_35]; decide
      have factor_0_37 : (13 : ZMod 3058504461911) ^ 191156528869 = 1550474343767 := by
        calc
          (13 : ZMod 3058504461911) ^ 191156528869 = (13 : ZMod 3058504461911) ^ (95578264434 + 95578264434 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 95578264434 * (13 : ZMod 3058504461911) ^ 95578264434) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1550474343767 := by rw [factor_0_36]; decide
      have factor_0_38 : (13 : ZMod 3058504461911) ^ 382313057738 = 1730376796715 := by
        calc
          (13 : ZMod 3058504461911) ^ 382313057738 = (13 : ZMod 3058504461911) ^ (191156528869 + 191156528869) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 191156528869 * (13 : ZMod 3058504461911) ^ 191156528869 := by rw [pow_add]
          _ = 1730376796715 := by rw [factor_0_37]; decide
      have factor_0_39 : (13 : ZMod 3058504461911) ^ 764626115477 = 831941996777 := by
        calc
          (13 : ZMod 3058504461911) ^ 764626115477 = (13 : ZMod 3058504461911) ^ (382313057738 + 382313057738 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 382313057738 * (13 : ZMod 3058504461911) ^ 382313057738) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 831941996777 := by rw [factor_0_38]; decide
      have factor_0_40 : (13 : ZMod 3058504461911) ^ 1529252230955 = 3058504461910 := by
        calc
          (13 : ZMod 3058504461911) ^ 1529252230955 = (13 : ZMod 3058504461911) ^ (764626115477 + 764626115477 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 764626115477 * (13 : ZMod 3058504461911) ^ 764626115477) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 3058504461910 := by rw [factor_0_39]; decide
      change (13 : ZMod 3058504461911) ^ 1529252230955 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (13 : ZMod 3058504461911) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 3058504461911) ^ 2 = 169 := by
        calc
          (13 : ZMod 3058504461911) ^ 2 = (13 : ZMod 3058504461911) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1 * (13 : ZMod 3058504461911) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 3058504461911) ^ 4 = 28561 := by
        calc
          (13 : ZMod 3058504461911) ^ 4 = (13 : ZMod 3058504461911) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 2 * (13 : ZMod 3058504461911) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 3058504461911) ^ 8 = 815730721 := by
        calc
          (13 : ZMod 3058504461911) ^ 8 = (13 : ZMod 3058504461911) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 4 * (13 : ZMod 3058504461911) ^ 4 := by rw [pow_add]
          _ = 815730721 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 3058504461911) ^ 17 = 1872191527968 := by
        calc
          (13 : ZMod 3058504461911) ^ 17 = (13 : ZMod 3058504461911) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 8 * (13 : ZMod 3058504461911) ^ 8) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1872191527968 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 3058504461911) ^ 35 = 2460627131754 := by
        calc
          (13 : ZMod 3058504461911) ^ 35 = (13 : ZMod 3058504461911) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 17 * (13 : ZMod 3058504461911) ^ 17) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2460627131754 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 3058504461911) ^ 71 = 1221964994743 := by
        calc
          (13 : ZMod 3058504461911) ^ 71 = (13 : ZMod 3058504461911) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 35 * (13 : ZMod 3058504461911) ^ 35) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1221964994743 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 3058504461911) ^ 142 = 2409930481432 := by
        calc
          (13 : ZMod 3058504461911) ^ 142 = (13 : ZMod 3058504461911) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 71 * (13 : ZMod 3058504461911) ^ 71 := by rw [pow_add]
          _ = 2409930481432 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 3058504461911) ^ 284 = 1184119902280 := by
        calc
          (13 : ZMod 3058504461911) ^ 284 = (13 : ZMod 3058504461911) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 142 * (13 : ZMod 3058504461911) ^ 142 := by rw [pow_add]
          _ = 1184119902280 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 3058504461911) ^ 569 = 600230476091 := by
        calc
          (13 : ZMod 3058504461911) ^ 569 = (13 : ZMod 3058504461911) ^ (284 + 284 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 284 * (13 : ZMod 3058504461911) ^ 284) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 600230476091 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 3058504461911) ^ 1139 = 1194883925678 := by
        calc
          (13 : ZMod 3058504461911) ^ 1139 = (13 : ZMod 3058504461911) ^ (569 + 569 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 569 * (13 : ZMod 3058504461911) ^ 569) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1194883925678 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 3058504461911) ^ 2278 = 2830142312011 := by
        calc
          (13 : ZMod 3058504461911) ^ 2278 = (13 : ZMod 3058504461911) ^ (1139 + 1139) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1139 * (13 : ZMod 3058504461911) ^ 1139 := by rw [pow_add]
          _ = 2830142312011 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 3058504461911) ^ 4557 = 798353349502 := by
        calc
          (13 : ZMod 3058504461911) ^ 4557 = (13 : ZMod 3058504461911) ^ (2278 + 2278 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 2278 * (13 : ZMod 3058504461911) ^ 2278) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 798353349502 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 3058504461911) ^ 9115 = 728805205923 := by
        calc
          (13 : ZMod 3058504461911) ^ 9115 = (13 : ZMod 3058504461911) ^ (4557 + 4557 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 4557 * (13 : ZMod 3058504461911) ^ 4557) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 728805205923 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 3058504461911) ^ 18230 = 712069692766 := by
        calc
          (13 : ZMod 3058504461911) ^ 18230 = (13 : ZMod 3058504461911) ^ (9115 + 9115) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 9115 * (13 : ZMod 3058504461911) ^ 9115 := by rw [pow_add]
          _ = 712069692766 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 3058504461911) ^ 36460 = 1414188283079 := by
        calc
          (13 : ZMod 3058504461911) ^ 36460 = (13 : ZMod 3058504461911) ^ (18230 + 18230) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 18230 * (13 : ZMod 3058504461911) ^ 18230 := by rw [pow_add]
          _ = 1414188283079 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 3058504461911) ^ 72920 = 784104804081 := by
        calc
          (13 : ZMod 3058504461911) ^ 72920 = (13 : ZMod 3058504461911) ^ (36460 + 36460) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 36460 * (13 : ZMod 3058504461911) ^ 36460 := by rw [pow_add]
          _ = 784104804081 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 3058504461911) ^ 145840 = 1098219743032 := by
        calc
          (13 : ZMod 3058504461911) ^ 145840 = (13 : ZMod 3058504461911) ^ (72920 + 72920) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 72920 * (13 : ZMod 3058504461911) ^ 72920 := by rw [pow_add]
          _ = 1098219743032 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 3058504461911) ^ 291681 = 1001625397926 := by
        calc
          (13 : ZMod 3058504461911) ^ 291681 = (13 : ZMod 3058504461911) ^ (145840 + 145840 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 145840 * (13 : ZMod 3058504461911) ^ 145840) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1001625397926 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 3058504461911) ^ 583363 = 1085680500764 := by
        calc
          (13 : ZMod 3058504461911) ^ 583363 = (13 : ZMod 3058504461911) ^ (291681 + 291681 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 291681 * (13 : ZMod 3058504461911) ^ 291681) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1085680500764 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 3058504461911) ^ 1166726 = 2246819156951 := by
        calc
          (13 : ZMod 3058504461911) ^ 1166726 = (13 : ZMod 3058504461911) ^ (583363 + 583363) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 583363 * (13 : ZMod 3058504461911) ^ 583363 := by rw [pow_add]
          _ = 2246819156951 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 3058504461911) ^ 2333453 = 2273700054832 := by
        calc
          (13 : ZMod 3058504461911) ^ 2333453 = (13 : ZMod 3058504461911) ^ (1166726 + 1166726 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1166726 * (13 : ZMod 3058504461911) ^ 1166726) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2273700054832 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 3058504461911) ^ 4666907 = 26436646589 := by
        calc
          (13 : ZMod 3058504461911) ^ 4666907 = (13 : ZMod 3058504461911) ^ (2333453 + 2333453 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 2333453 * (13 : ZMod 3058504461911) ^ 2333453) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 26436646589 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 3058504461911) ^ 9333814 = 482655192072 := by
        calc
          (13 : ZMod 3058504461911) ^ 9333814 = (13 : ZMod 3058504461911) ^ (4666907 + 4666907) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 4666907 * (13 : ZMod 3058504461911) ^ 4666907 := by rw [pow_add]
          _ = 482655192072 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 3058504461911) ^ 18667629 = 232366263873 := by
        calc
          (13 : ZMod 3058504461911) ^ 18667629 = (13 : ZMod 3058504461911) ^ (9333814 + 9333814 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 9333814 * (13 : ZMod 3058504461911) ^ 9333814) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 232366263873 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 3058504461911) ^ 37335259 = 304898524836 := by
        calc
          (13 : ZMod 3058504461911) ^ 37335259 = (13 : ZMod 3058504461911) ^ (18667629 + 18667629 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 18667629 * (13 : ZMod 3058504461911) ^ 18667629) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 304898524836 := by rw [factor_1_24]; decide
      have factor_1_26 : (13 : ZMod 3058504461911) ^ 74670519 = 1711981676946 := by
        calc
          (13 : ZMod 3058504461911) ^ 74670519 = (13 : ZMod 3058504461911) ^ (37335259 + 37335259 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 37335259 * (13 : ZMod 3058504461911) ^ 37335259) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1711981676946 := by rw [factor_1_25]; decide
      have factor_1_27 : (13 : ZMod 3058504461911) ^ 149341038 = 990162284412 := by
        calc
          (13 : ZMod 3058504461911) ^ 149341038 = (13 : ZMod 3058504461911) ^ (74670519 + 74670519) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 74670519 * (13 : ZMod 3058504461911) ^ 74670519 := by rw [pow_add]
          _ = 990162284412 := by rw [factor_1_26]; decide
      have factor_1_28 : (13 : ZMod 3058504461911) ^ 298682076 = 2225627637699 := by
        calc
          (13 : ZMod 3058504461911) ^ 298682076 = (13 : ZMod 3058504461911) ^ (149341038 + 149341038) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 149341038 * (13 : ZMod 3058504461911) ^ 149341038 := by rw [pow_add]
          _ = 2225627637699 := by rw [factor_1_27]; decide
      have factor_1_29 : (13 : ZMod 3058504461911) ^ 597364152 = 2662808676039 := by
        calc
          (13 : ZMod 3058504461911) ^ 597364152 = (13 : ZMod 3058504461911) ^ (298682076 + 298682076) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 298682076 * (13 : ZMod 3058504461911) ^ 298682076 := by rw [pow_add]
          _ = 2662808676039 := by rw [factor_1_28]; decide
      have factor_1_30 : (13 : ZMod 3058504461911) ^ 1194728305 = 741995464266 := by
        calc
          (13 : ZMod 3058504461911) ^ 1194728305 = (13 : ZMod 3058504461911) ^ (597364152 + 597364152 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 597364152 * (13 : ZMod 3058504461911) ^ 597364152) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 741995464266 := by rw [factor_1_29]; decide
      have factor_1_31 : (13 : ZMod 3058504461911) ^ 2389456610 = 2644083577378 := by
        calc
          (13 : ZMod 3058504461911) ^ 2389456610 = (13 : ZMod 3058504461911) ^ (1194728305 + 1194728305) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1194728305 * (13 : ZMod 3058504461911) ^ 1194728305 := by rw [pow_add]
          _ = 2644083577378 := by rw [factor_1_30]; decide
      have factor_1_32 : (13 : ZMod 3058504461911) ^ 4778913221 = 828153490988 := by
        calc
          (13 : ZMod 3058504461911) ^ 4778913221 = (13 : ZMod 3058504461911) ^ (2389456610 + 2389456610 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 2389456610 * (13 : ZMod 3058504461911) ^ 2389456610) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 828153490988 := by rw [factor_1_31]; decide
      have factor_1_33 : (13 : ZMod 3058504461911) ^ 9557826443 = 966835116432 := by
        calc
          (13 : ZMod 3058504461911) ^ 9557826443 = (13 : ZMod 3058504461911) ^ (4778913221 + 4778913221 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 4778913221 * (13 : ZMod 3058504461911) ^ 4778913221) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 966835116432 := by rw [factor_1_32]; decide
      have factor_1_34 : (13 : ZMod 3058504461911) ^ 19115652886 = 1508346609909 := by
        calc
          (13 : ZMod 3058504461911) ^ 19115652886 = (13 : ZMod 3058504461911) ^ (9557826443 + 9557826443) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 9557826443 * (13 : ZMod 3058504461911) ^ 9557826443 := by rw [pow_add]
          _ = 1508346609909 := by rw [factor_1_33]; decide
      have factor_1_35 : (13 : ZMod 3058504461911) ^ 38231305773 = 1016885838163 := by
        calc
          (13 : ZMod 3058504461911) ^ 38231305773 = (13 : ZMod 3058504461911) ^ (19115652886 + 19115652886 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 19115652886 * (13 : ZMod 3058504461911) ^ 19115652886) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1016885838163 := by rw [factor_1_34]; decide
      have factor_1_36 : (13 : ZMod 3058504461911) ^ 76462611547 = 2858735409821 := by
        calc
          (13 : ZMod 3058504461911) ^ 76462611547 = (13 : ZMod 3058504461911) ^ (38231305773 + 38231305773 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 38231305773 * (13 : ZMod 3058504461911) ^ 38231305773) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2858735409821 := by rw [factor_1_35]; decide
      have factor_1_37 : (13 : ZMod 3058504461911) ^ 152925223095 = 2160896000960 := by
        calc
          (13 : ZMod 3058504461911) ^ 152925223095 = (13 : ZMod 3058504461911) ^ (76462611547 + 76462611547 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 76462611547 * (13 : ZMod 3058504461911) ^ 76462611547) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2160896000960 := by rw [factor_1_36]; decide
      have factor_1_38 : (13 : ZMod 3058504461911) ^ 305850446191 = 388726797033 := by
        calc
          (13 : ZMod 3058504461911) ^ 305850446191 = (13 : ZMod 3058504461911) ^ (152925223095 + 152925223095 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 152925223095 * (13 : ZMod 3058504461911) ^ 152925223095) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 388726797033 := by rw [factor_1_37]; decide
      have factor_1_39 : (13 : ZMod 3058504461911) ^ 611700892382 = 1357494279441 := by
        calc
          (13 : ZMod 3058504461911) ^ 611700892382 = (13 : ZMod 3058504461911) ^ (305850446191 + 305850446191) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 305850446191 * (13 : ZMod 3058504461911) ^ 305850446191 := by rw [pow_add]
          _ = 1357494279441 := by rw [factor_1_38]; decide
      change (13 : ZMod 3058504461911) ^ 611700892382 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (13 : ZMod 3058504461911) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 3058504461911) ^ 3 = 2197 := by
        calc
          (13 : ZMod 3058504461911) ^ 3 = (13 : ZMod 3058504461911) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1 * (13 : ZMod 3058504461911) ^ 1) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 3058504461911) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 3058504461911) ^ 6 = (13 : ZMod 3058504461911) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 3 * (13 : ZMod 3058504461911) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 3058504461911) ^ 13 = 83164863064 := by
        calc
          (13 : ZMod 3058504461911) ^ 13 = (13 : ZMod 3058504461911) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 6 * (13 : ZMod 3058504461911) ^ 6) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 83164863064 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 3058504461911) ^ 26 = 1422225782678 := by
        calc
          (13 : ZMod 3058504461911) ^ 26 = (13 : ZMod 3058504461911) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 13 * (13 : ZMod 3058504461911) ^ 13 := by rw [pow_add]
          _ = 1422225782678 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 3058504461911) ^ 53 = 1785161760191 := by
        calc
          (13 : ZMod 3058504461911) ^ 53 = (13 : ZMod 3058504461911) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 26 * (13 : ZMod 3058504461911) ^ 26) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1785161760191 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 3058504461911) ^ 107 = 530640278428 := by
        calc
          (13 : ZMod 3058504461911) ^ 107 = (13 : ZMod 3058504461911) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 53 * (13 : ZMod 3058504461911) ^ 53) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 530640278428 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 3058504461911) ^ 215 = 1870557811129 := by
        calc
          (13 : ZMod 3058504461911) ^ 215 = (13 : ZMod 3058504461911) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 107 * (13 : ZMod 3058504461911) ^ 107) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1870557811129 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 3058504461911) ^ 431 = 2263103157260 := by
        calc
          (13 : ZMod 3058504461911) ^ 431 = (13 : ZMod 3058504461911) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 215 * (13 : ZMod 3058504461911) ^ 215) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2263103157260 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 3058504461911) ^ 863 = 2895852446256 := by
        calc
          (13 : ZMod 3058504461911) ^ 863 = (13 : ZMod 3058504461911) ^ (431 + 431 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 431 * (13 : ZMod 3058504461911) ^ 431) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2895852446256 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 3058504461911) ^ 1727 = 2508428288912 := by
        calc
          (13 : ZMod 3058504461911) ^ 1727 = (13 : ZMod 3058504461911) ^ (863 + 863 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 863 * (13 : ZMod 3058504461911) ^ 863) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2508428288912 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 3058504461911) ^ 3455 = 1414749452857 := by
        calc
          (13 : ZMod 3058504461911) ^ 3455 = (13 : ZMod 3058504461911) ^ (1727 + 1727 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1727 * (13 : ZMod 3058504461911) ^ 1727) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1414749452857 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 3058504461911) ^ 6911 = 1640082795789 := by
        calc
          (13 : ZMod 3058504461911) ^ 6911 = (13 : ZMod 3058504461911) ^ (3455 + 3455 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 3455 * (13 : ZMod 3058504461911) ^ 3455) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1640082795789 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 3058504461911) ^ 13823 = 2939147836909 := by
        calc
          (13 : ZMod 3058504461911) ^ 13823 = (13 : ZMod 3058504461911) ^ (6911 + 6911 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 6911 * (13 : ZMod 3058504461911) ^ 6911) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2939147836909 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 3058504461911) ^ 27647 = 511364980508 := by
        calc
          (13 : ZMod 3058504461911) ^ 27647 = (13 : ZMod 3058504461911) ^ (13823 + 13823 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 13823 * (13 : ZMod 3058504461911) ^ 13823) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 511364980508 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 3058504461911) ^ 55295 = 2043939375609 := by
        calc
          (13 : ZMod 3058504461911) ^ 55295 = (13 : ZMod 3058504461911) ^ (27647 + 27647 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 27647 * (13 : ZMod 3058504461911) ^ 27647) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2043939375609 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 3058504461911) ^ 110590 = 2004661369694 := by
        calc
          (13 : ZMod 3058504461911) ^ 110590 = (13 : ZMod 3058504461911) ^ (55295 + 55295) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 55295 * (13 : ZMod 3058504461911) ^ 55295 := by rw [pow_add]
          _ = 2004661369694 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 3058504461911) ^ 221180 = 952616833974 := by
        calc
          (13 : ZMod 3058504461911) ^ 221180 = (13 : ZMod 3058504461911) ^ (110590 + 110590) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 110590 * (13 : ZMod 3058504461911) ^ 110590 := by rw [pow_add]
          _ = 952616833974 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 3058504461911) ^ 442360 = 935903596960 := by
        calc
          (13 : ZMod 3058504461911) ^ 442360 = (13 : ZMod 3058504461911) ^ (221180 + 221180) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 221180 * (13 : ZMod 3058504461911) ^ 221180 := by rw [pow_add]
          _ = 935903596960 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 3058504461911) ^ 884721 = 2227349423742 := by
        calc
          (13 : ZMod 3058504461911) ^ 884721 = (13 : ZMod 3058504461911) ^ (442360 + 442360 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 442360 * (13 : ZMod 3058504461911) ^ 442360) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2227349423742 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 3058504461911) ^ 1769443 = 1262409327980 := by
        calc
          (13 : ZMod 3058504461911) ^ 1769443 = (13 : ZMod 3058504461911) ^ (884721 + 884721 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 884721 * (13 : ZMod 3058504461911) ^ 884721) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1262409327980 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 3058504461911) ^ 3538887 = 1487037688495 := by
        calc
          (13 : ZMod 3058504461911) ^ 3538887 = (13 : ZMod 3058504461911) ^ (1769443 + 1769443 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1769443 * (13 : ZMod 3058504461911) ^ 1769443) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1487037688495 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 3058504461911) ^ 7077774 = 896317093649 := by
        calc
          (13 : ZMod 3058504461911) ^ 7077774 = (13 : ZMod 3058504461911) ^ (3538887 + 3538887) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 3538887 * (13 : ZMod 3058504461911) ^ 3538887 := by rw [pow_add]
          _ = 896317093649 := by rw [factor_2_21]; decide
      have factor_2_23 : (13 : ZMod 3058504461911) ^ 14155548 = 1745930495398 := by
        calc
          (13 : ZMod 3058504461911) ^ 14155548 = (13 : ZMod 3058504461911) ^ (7077774 + 7077774) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 7077774 * (13 : ZMod 3058504461911) ^ 7077774 := by rw [pow_add]
          _ = 1745930495398 := by rw [factor_2_22]; decide
      have factor_2_24 : (13 : ZMod 3058504461911) ^ 28311097 = 1930812569103 := by
        calc
          (13 : ZMod 3058504461911) ^ 28311097 = (13 : ZMod 3058504461911) ^ (14155548 + 14155548 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 14155548 * (13 : ZMod 3058504461911) ^ 14155548) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1930812569103 := by rw [factor_2_23]; decide
      have factor_2_25 : (13 : ZMod 3058504461911) ^ 56622194 = 386113167385 := by
        calc
          (13 : ZMod 3058504461911) ^ 56622194 = (13 : ZMod 3058504461911) ^ (28311097 + 28311097) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 28311097 * (13 : ZMod 3058504461911) ^ 28311097 := by rw [pow_add]
          _ = 386113167385 := by rw [factor_2_24]; decide
      have factor_2_26 : (13 : ZMod 3058504461911) ^ 113244389 = 2365790124516 := by
        calc
          (13 : ZMod 3058504461911) ^ 113244389 = (13 : ZMod 3058504461911) ^ (56622194 + 56622194 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 56622194 * (13 : ZMod 3058504461911) ^ 56622194) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2365790124516 := by rw [factor_2_25]; decide
      have factor_2_27 : (13 : ZMod 3058504461911) ^ 226488778 = 1866360731131 := by
        calc
          (13 : ZMod 3058504461911) ^ 226488778 = (13 : ZMod 3058504461911) ^ (113244389 + 113244389) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 113244389 * (13 : ZMod 3058504461911) ^ 113244389 := by rw [pow_add]
          _ = 1866360731131 := by rw [factor_2_26]; decide
      have factor_2_28 : (13 : ZMod 3058504461911) ^ 452977556 = 758302200916 := by
        calc
          (13 : ZMod 3058504461911) ^ 452977556 = (13 : ZMod 3058504461911) ^ (226488778 + 226488778) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 226488778 * (13 : ZMod 3058504461911) ^ 226488778 := by rw [pow_add]
          _ = 758302200916 := by rw [factor_2_27]; decide
      have factor_2_29 : (13 : ZMod 3058504461911) ^ 905955113 = 2270567054121 := by
        calc
          (13 : ZMod 3058504461911) ^ 905955113 = (13 : ZMod 3058504461911) ^ (452977556 + 452977556 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 452977556 * (13 : ZMod 3058504461911) ^ 452977556) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2270567054121 := by rw [factor_2_28]; decide
      have factor_2_30 : (13 : ZMod 3058504461911) ^ 1811910226 = 2359544050467 := by
        calc
          (13 : ZMod 3058504461911) ^ 1811910226 = (13 : ZMod 3058504461911) ^ (905955113 + 905955113) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 905955113 * (13 : ZMod 3058504461911) ^ 905955113 := by rw [pow_add]
          _ = 2359544050467 := by rw [factor_2_29]; decide
      have factor_2_31 : (13 : ZMod 3058504461911) ^ 3623820452 = 1236011795182 := by
        calc
          (13 : ZMod 3058504461911) ^ 3623820452 = (13 : ZMod 3058504461911) ^ (1811910226 + 1811910226) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1811910226 * (13 : ZMod 3058504461911) ^ 1811910226 := by rw [pow_add]
          _ = 1236011795182 := by rw [factor_2_30]; decide
      have factor_2_32 : (13 : ZMod 3058504461911) ^ 7247640905 = 628705782852 := by
        calc
          (13 : ZMod 3058504461911) ^ 7247640905 = (13 : ZMod 3058504461911) ^ (3623820452 + 3623820452 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 3623820452 * (13 : ZMod 3058504461911) ^ 3623820452) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 628705782852 := by rw [factor_2_31]; decide
      have factor_2_33 : (13 : ZMod 3058504461911) ^ 14495281810 = 2756589899822 := by
        calc
          (13 : ZMod 3058504461911) ^ 14495281810 = (13 : ZMod 3058504461911) ^ (7247640905 + 7247640905) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 7247640905 * (13 : ZMod 3058504461911) ^ 7247640905 := by rw [pow_add]
          _ = 2756589899822 := by rw [factor_2_32]; decide
      change (13 : ZMod 3058504461911) ^ 14495281810 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (13 : ZMod 3058504461911) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 3058504461911) ^ 3 = 2197 := by
        calc
          (13 : ZMod 3058504461911) ^ 3 = (13 : ZMod 3058504461911) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1 * (13 : ZMod 3058504461911) ^ 1) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 3058504461911) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 3058504461911) ^ 6 = (13 : ZMod 3058504461911) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 3 * (13 : ZMod 3058504461911) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 3058504461911) ^ 13 = 83164863064 := by
        calc
          (13 : ZMod 3058504461911) ^ 13 = (13 : ZMod 3058504461911) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 6 * (13 : ZMod 3058504461911) ^ 6) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 83164863064 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 3058504461911) ^ 27 = 137908403348 := by
        calc
          (13 : ZMod 3058504461911) ^ 27 = (13 : ZMod 3058504461911) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 13 * (13 : ZMod 3058504461911) ^ 13) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 137908403348 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 3058504461911) ^ 54 = 1797571649106 := by
        calc
          (13 : ZMod 3058504461911) ^ 54 = (13 : ZMod 3058504461911) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 27 * (13 : ZMod 3058504461911) ^ 27 := by rw [pow_add]
          _ = 1797571649106 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 3058504461911) ^ 109 = 981577658913 := by
        calc
          (13 : ZMod 3058504461911) ^ 109 = (13 : ZMod 3058504461911) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 54 * (13 : ZMod 3058504461911) ^ 54) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 981577658913 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 3058504461911) ^ 218 = 2044018703940 := by
        calc
          (13 : ZMod 3058504461911) ^ 218 = (13 : ZMod 3058504461911) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 109 * (13 : ZMod 3058504461911) ^ 109 := by rw [pow_add]
          _ = 2044018703940 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 3058504461911) ^ 437 = 1778506294222 := by
        calc
          (13 : ZMod 3058504461911) ^ 437 = (13 : ZMod 3058504461911) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 218 * (13 : ZMod 3058504461911) ^ 218) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1778506294222 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 3058504461911) ^ 874 = 326678074735 := by
        calc
          (13 : ZMod 3058504461911) ^ 874 = (13 : ZMod 3058504461911) ^ (437 + 437) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 437 * (13 : ZMod 3058504461911) ^ 437 := by rw [pow_add]
          _ = 326678074735 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 3058504461911) ^ 1749 = 293826076854 := by
        calc
          (13 : ZMod 3058504461911) ^ 1749 = (13 : ZMod 3058504461911) ^ (874 + 874 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 874 * (13 : ZMod 3058504461911) ^ 874) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 293826076854 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 3058504461911) ^ 3499 = 1695456435516 := by
        calc
          (13 : ZMod 3058504461911) ^ 3499 = (13 : ZMod 3058504461911) ^ (1749 + 1749 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1749 * (13 : ZMod 3058504461911) ^ 1749) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1695456435516 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 3058504461911) ^ 6998 = 1244387266716 := by
        calc
          (13 : ZMod 3058504461911) ^ 6998 = (13 : ZMod 3058504461911) ^ (3499 + 3499) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 3499 * (13 : ZMod 3058504461911) ^ 3499 := by rw [pow_add]
          _ = 1244387266716 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 3058504461911) ^ 13997 = 2510525632189 := by
        calc
          (13 : ZMod 3058504461911) ^ 13997 = (13 : ZMod 3058504461911) ^ (6998 + 6998 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 6998 * (13 : ZMod 3058504461911) ^ 6998) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2510525632189 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 3058504461911) ^ 27995 = 2969032165608 := by
        calc
          (13 : ZMod 3058504461911) ^ 27995 = (13 : ZMod 3058504461911) ^ (13997 + 13997 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 13997 * (13 : ZMod 3058504461911) ^ 13997) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2969032165608 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 3058504461911) ^ 55991 = 1646057616389 := by
        calc
          (13 : ZMod 3058504461911) ^ 55991 = (13 : ZMod 3058504461911) ^ (27995 + 27995 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 27995 * (13 : ZMod 3058504461911) ^ 27995) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1646057616389 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 3058504461911) ^ 111983 = 17239013672 := by
        calc
          (13 : ZMod 3058504461911) ^ 111983 = (13 : ZMod 3058504461911) ^ (55991 + 55991 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 55991 * (13 : ZMod 3058504461911) ^ 55991) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 17239013672 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 3058504461911) ^ 223966 = 2759479967085 := by
        calc
          (13 : ZMod 3058504461911) ^ 223966 = (13 : ZMod 3058504461911) ^ (111983 + 111983) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 111983 * (13 : ZMod 3058504461911) ^ 111983 := by rw [pow_add]
          _ = 2759479967085 := by rw [factor_3_16]; decide
      have factor_3_18 : (13 : ZMod 3058504461911) ^ 447933 = 1094171668300 := by
        calc
          (13 : ZMod 3058504461911) ^ 447933 = (13 : ZMod 3058504461911) ^ (223966 + 223966 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 223966 * (13 : ZMod 3058504461911) ^ 223966) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1094171668300 := by rw [factor_3_17]; decide
      have factor_3_19 : (13 : ZMod 3058504461911) ^ 895867 = 2338142351300 := by
        calc
          (13 : ZMod 3058504461911) ^ 895867 = (13 : ZMod 3058504461911) ^ (447933 + 447933 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 447933 * (13 : ZMod 3058504461911) ^ 447933) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2338142351300 := by rw [factor_3_18]; decide
      have factor_3_20 : (13 : ZMod 3058504461911) ^ 1791734 = 432379593403 := by
        calc
          (13 : ZMod 3058504461911) ^ 1791734 = (13 : ZMod 3058504461911) ^ (895867 + 895867) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 895867 * (13 : ZMod 3058504461911) ^ 895867 := by rw [pow_add]
          _ = 432379593403 := by rw [factor_3_19]; decide
      have factor_3_21 : (13 : ZMod 3058504461911) ^ 3583468 = 465171267472 := by
        calc
          (13 : ZMod 3058504461911) ^ 3583468 = (13 : ZMod 3058504461911) ^ (1791734 + 1791734) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1791734 * (13 : ZMod 3058504461911) ^ 1791734 := by rw [pow_add]
          _ = 465171267472 := by rw [factor_3_20]; decide
      have factor_3_22 : (13 : ZMod 3058504461911) ^ 7166936 = 885214453095 := by
        calc
          (13 : ZMod 3058504461911) ^ 7166936 = (13 : ZMod 3058504461911) ^ (3583468 + 3583468) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 3583468 * (13 : ZMod 3058504461911) ^ 3583468 := by rw [pow_add]
          _ = 885214453095 := by rw [factor_3_21]; decide
      have factor_3_23 : (13 : ZMod 3058504461911) ^ 14333872 = 1377001960643 := by
        calc
          (13 : ZMod 3058504461911) ^ 14333872 = (13 : ZMod 3058504461911) ^ (7166936 + 7166936) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 7166936 * (13 : ZMod 3058504461911) ^ 7166936 := by rw [pow_add]
          _ = 1377001960643 := by rw [factor_3_22]; decide
      have factor_3_24 : (13 : ZMod 3058504461911) ^ 28667745 = 2217709866068 := by
        calc
          (13 : ZMod 3058504461911) ^ 28667745 = (13 : ZMod 3058504461911) ^ (14333872 + 14333872 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 14333872 * (13 : ZMod 3058504461911) ^ 14333872) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2217709866068 := by rw [factor_3_23]; decide
      have factor_3_25 : (13 : ZMod 3058504461911) ^ 57335491 = 1386672958757 := by
        calc
          (13 : ZMod 3058504461911) ^ 57335491 = (13 : ZMod 3058504461911) ^ (28667745 + 28667745 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 28667745 * (13 : ZMod 3058504461911) ^ 28667745) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1386672958757 := by rw [factor_3_24]; decide
      have factor_3_26 : (13 : ZMod 3058504461911) ^ 114670983 = 1101319232949 := by
        calc
          (13 : ZMod 3058504461911) ^ 114670983 = (13 : ZMod 3058504461911) ^ (57335491 + 57335491 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 57335491 * (13 : ZMod 3058504461911) ^ 57335491) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1101319232949 := by rw [factor_3_25]; decide
      have factor_3_27 : (13 : ZMod 3058504461911) ^ 229341966 = 770295829841 := by
        calc
          (13 : ZMod 3058504461911) ^ 229341966 = (13 : ZMod 3058504461911) ^ (114670983 + 114670983) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 114670983 * (13 : ZMod 3058504461911) ^ 114670983 := by rw [pow_add]
          _ = 770295829841 := by rw [factor_3_26]; decide
      have factor_3_28 : (13 : ZMod 3058504461911) ^ 458683932 = 2397181946426 := by
        calc
          (13 : ZMod 3058504461911) ^ 458683932 = (13 : ZMod 3058504461911) ^ (229341966 + 229341966) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 229341966 * (13 : ZMod 3058504461911) ^ 229341966 := by rw [pow_add]
          _ = 2397181946426 := by rw [factor_3_27]; decide
      have factor_3_29 : (13 : ZMod 3058504461911) ^ 917367865 = 204061170227 := by
        calc
          (13 : ZMod 3058504461911) ^ 917367865 = (13 : ZMod 3058504461911) ^ (458683932 + 458683932 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 458683932 * (13 : ZMod 3058504461911) ^ 458683932) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 204061170227 := by rw [factor_3_28]; decide
      have factor_3_30 : (13 : ZMod 3058504461911) ^ 1834735730 = 2706748365632 := by
        calc
          (13 : ZMod 3058504461911) ^ 1834735730 = (13 : ZMod 3058504461911) ^ (917367865 + 917367865) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 917367865 * (13 : ZMod 3058504461911) ^ 917367865 := by rw [pow_add]
          _ = 2706748365632 := by rw [factor_3_29]; decide
      change (13 : ZMod 3058504461911) ^ 1834735730 ≠ 1
      rw [factor_3_30]
      decide
    ·
      have factor_4_0 : (13 : ZMod 3058504461911) ^ 1 = 13 := by norm_num
      have factor_4_1 : (13 : ZMod 3058504461911) ^ 3 = 2197 := by
        calc
          (13 : ZMod 3058504461911) ^ 3 = (13 : ZMod 3058504461911) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 1 * (13 : ZMod 3058504461911) ^ 1) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_4_0]; decide
      have factor_4_2 : (13 : ZMod 3058504461911) ^ 6 = 4826809 := by
        calc
          (13 : ZMod 3058504461911) ^ 6 = (13 : ZMod 3058504461911) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 3 * (13 : ZMod 3058504461911) ^ 3 := by rw [pow_add]
          _ = 4826809 := by rw [factor_4_1]; decide
      have factor_4_3 : (13 : ZMod 3058504461911) ^ 13 = 83164863064 := by
        calc
          (13 : ZMod 3058504461911) ^ 13 = (13 : ZMod 3058504461911) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 6 * (13 : ZMod 3058504461911) ^ 6) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 83164863064 := by rw [factor_4_2]; decide
      have factor_4_4 : (13 : ZMod 3058504461911) ^ 26 = 1422225782678 := by
        calc
          (13 : ZMod 3058504461911) ^ 26 = (13 : ZMod 3058504461911) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 13 * (13 : ZMod 3058504461911) ^ 13 := by rw [pow_add]
          _ = 1422225782678 := by rw [factor_4_3]; decide
      have factor_4_5 : (13 : ZMod 3058504461911) ^ 53 = 1785161760191 := by
        calc
          (13 : ZMod 3058504461911) ^ 53 = (13 : ZMod 3058504461911) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 26 * (13 : ZMod 3058504461911) ^ 26) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1785161760191 := by rw [factor_4_4]; decide
      have factor_4_6 : (13 : ZMod 3058504461911) ^ 107 = 530640278428 := by
        calc
          (13 : ZMod 3058504461911) ^ 107 = (13 : ZMod 3058504461911) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 53 * (13 : ZMod 3058504461911) ^ 53) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 530640278428 := by rw [factor_4_5]; decide
      have factor_4_7 : (13 : ZMod 3058504461911) ^ 214 = 849697784374 := by
        calc
          (13 : ZMod 3058504461911) ^ 214 = (13 : ZMod 3058504461911) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 107 * (13 : ZMod 3058504461911) ^ 107 := by rw [pow_add]
          _ = 849697784374 := by rw [factor_4_6]; decide
      have factor_4_8 : (13 : ZMod 3058504461911) ^ 429 = 393441993239 := by
        calc
          (13 : ZMod 3058504461911) ^ 429 = (13 : ZMod 3058504461911) ^ (214 + 214 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 214 * (13 : ZMod 3058504461911) ^ 214) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 393441993239 := by rw [factor_4_7]; decide
      have factor_4_9 : (13 : ZMod 3058504461911) ^ 858 = 1219445727164 := by
        calc
          (13 : ZMod 3058504461911) ^ 858 = (13 : ZMod 3058504461911) ^ (429 + 429) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 429 * (13 : ZMod 3058504461911) ^ 429 := by rw [pow_add]
          _ = 1219445727164 := by rw [factor_4_8]; decide
      have factor_4_10 : (13 : ZMod 3058504461911) ^ 1717 = 1396751421874 := by
        calc
          (13 : ZMod 3058504461911) ^ 1717 = (13 : ZMod 3058504461911) ^ (858 + 858 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 858 * (13 : ZMod 3058504461911) ^ 858) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1396751421874 := by rw [factor_4_9]; decide
      have factor_4_11 : (13 : ZMod 3058504461911) ^ 3434 = 2213102732512 := by
        calc
          (13 : ZMod 3058504461911) ^ 3434 = (13 : ZMod 3058504461911) ^ (1717 + 1717) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1717 * (13 : ZMod 3058504461911) ^ 1717 := by rw [pow_add]
          _ = 2213102732512 := by rw [factor_4_10]; decide
      have factor_4_12 : (13 : ZMod 3058504461911) ^ 6869 = 1072088915834 := by
        calc
          (13 : ZMod 3058504461911) ^ 6869 = (13 : ZMod 3058504461911) ^ (3434 + 3434 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 3434 * (13 : ZMod 3058504461911) ^ 3434) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1072088915834 := by rw [factor_4_11]; decide
      have factor_4_13 : (13 : ZMod 3058504461911) ^ 13739 = 149342554174 := by
        calc
          (13 : ZMod 3058504461911) ^ 13739 = (13 : ZMod 3058504461911) ^ (6869 + 6869 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 6869 * (13 : ZMod 3058504461911) ^ 6869) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 149342554174 := by rw [factor_4_12]; decide
      have factor_4_14 : (13 : ZMod 3058504461911) ^ 27479 = 1468780492038 := by
        calc
          (13 : ZMod 3058504461911) ^ 27479 = (13 : ZMod 3058504461911) ^ (13739 + 13739 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 13739 * (13 : ZMod 3058504461911) ^ 13739) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 1468780492038 := by rw [factor_4_13]; decide
      have factor_4_15 : (13 : ZMod 3058504461911) ^ 54958 = 2967638598398 := by
        calc
          (13 : ZMod 3058504461911) ^ 54958 = (13 : ZMod 3058504461911) ^ (27479 + 27479) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 27479 * (13 : ZMod 3058504461911) ^ 27479 := by rw [pow_add]
          _ = 2967638598398 := by rw [factor_4_14]; decide
      have factor_4_16 : (13 : ZMod 3058504461911) ^ 109917 = 2487937849974 := by
        calc
          (13 : ZMod 3058504461911) ^ 109917 = (13 : ZMod 3058504461911) ^ (54958 + 54958 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 54958 * (13 : ZMod 3058504461911) ^ 54958) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2487937849974 := by rw [factor_4_15]; decide
      have factor_4_17 : (13 : ZMod 3058504461911) ^ 219835 = 2230773341223 := by
        calc
          (13 : ZMod 3058504461911) ^ 219835 = (13 : ZMod 3058504461911) ^ (109917 + 109917 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 109917 * (13 : ZMod 3058504461911) ^ 109917) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2230773341223 := by rw [factor_4_16]; decide
      have factor_4_18 : (13 : ZMod 3058504461911) ^ 439671 = 2609347763462 := by
        calc
          (13 : ZMod 3058504461911) ^ 439671 = (13 : ZMod 3058504461911) ^ (219835 + 219835 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 219835 * (13 : ZMod 3058504461911) ^ 219835) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2609347763462 := by rw [factor_4_17]; decide
      have factor_4_19 : (13 : ZMod 3058504461911) ^ 879342 = 538789572037 := by
        calc
          (13 : ZMod 3058504461911) ^ 879342 = (13 : ZMod 3058504461911) ^ (439671 + 439671) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 439671 * (13 : ZMod 3058504461911) ^ 439671 := by rw [pow_add]
          _ = 538789572037 := by rw [factor_4_18]; decide
      have factor_4_20 : (13 : ZMod 3058504461911) ^ 1758685 = 2268574017692 := by
        calc
          (13 : ZMod 3058504461911) ^ 1758685 = (13 : ZMod 3058504461911) ^ (879342 + 879342 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = ((13 : ZMod 3058504461911) ^ 879342 * (13 : ZMod 3058504461911) ^ 879342) * (13 : ZMod 3058504461911) := by rw [pow_succ, pow_add]
          _ = 2268574017692 := by rw [factor_4_19]; decide
      have factor_4_21 : (13 : ZMod 3058504461911) ^ 3517370 = 2003584746548 := by
        calc
          (13 : ZMod 3058504461911) ^ 3517370 = (13 : ZMod 3058504461911) ^ (1758685 + 1758685) :=
            congrArg (fun n : ℕ => (13 : ZMod 3058504461911) ^ n) (by norm_num)
          _ = (13 : ZMod 3058504461911) ^ 1758685 * (13 : ZMod 3058504461911) ^ 1758685 := by rw [pow_add]
          _ = 2003584746548 := by rw [factor_4_20]; decide
      change (13 : ZMod 3058504461911) ^ 3517370 ≠ 1
      rw [factor_4_21]
      decide

#print axioms prime_lucas_3058504461911

end TotientTailPeriodKiller
end Erdos249257
