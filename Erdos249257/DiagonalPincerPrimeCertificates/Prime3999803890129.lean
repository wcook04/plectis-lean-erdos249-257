import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3999803890129 : Nat.Prime 3999803890129 := by
  apply lucas_primality 3999803890129 (13 : ZMod 3999803890129)
  ·
      have fermat_0 : (13 : ZMod 3999803890129) ^ 1 = 13 := by norm_num
      have fermat_1 : (13 : ZMod 3999803890129) ^ 3 = 2197 := by
        calc
          (13 : ZMod 3999803890129) ^ 3 = (13 : ZMod 3999803890129) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 1 * (13 : ZMod 3999803890129) ^ 1) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [fermat_0]; decide
      have fermat_2 : (13 : ZMod 3999803890129) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 3999803890129) ^ 7 = (13 : ZMod 3999803890129) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 3 * (13 : ZMod 3999803890129) ^ 3) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [fermat_1]; decide
      have fermat_3 : (13 : ZMod 3999803890129) ^ 14 = 1569357812353 := by
        calc
          (13 : ZMod 3999803890129) ^ 14 = (13 : ZMod 3999803890129) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 7 * (13 : ZMod 3999803890129) ^ 7 := by rw [pow_add]
          _ = 1569357812353 := by rw [fermat_2]; decide
      have fermat_4 : (13 : ZMod 3999803890129) ^ 29 = 2361118877296 := by
        calc
          (13 : ZMod 3999803890129) ^ 29 = (13 : ZMod 3999803890129) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 14 * (13 : ZMod 3999803890129) ^ 14) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2361118877296 := by rw [fermat_3]; decide
      have fermat_5 : (13 : ZMod 3999803890129) ^ 58 = 1242078737878 := by
        calc
          (13 : ZMod 3999803890129) ^ 58 = (13 : ZMod 3999803890129) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 29 * (13 : ZMod 3999803890129) ^ 29 := by rw [pow_add]
          _ = 1242078737878 := by rw [fermat_4]; decide
      have fermat_6 : (13 : ZMod 3999803890129) ^ 116 = 1205094478242 := by
        calc
          (13 : ZMod 3999803890129) ^ 116 = (13 : ZMod 3999803890129) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 58 * (13 : ZMod 3999803890129) ^ 58 := by rw [pow_add]
          _ = 1205094478242 := by rw [fermat_5]; decide
      have fermat_7 : (13 : ZMod 3999803890129) ^ 232 = 785507896187 := by
        calc
          (13 : ZMod 3999803890129) ^ 232 = (13 : ZMod 3999803890129) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 116 * (13 : ZMod 3999803890129) ^ 116 := by rw [pow_add]
          _ = 785507896187 := by rw [fermat_6]; decide
      have fermat_8 : (13 : ZMod 3999803890129) ^ 465 = 1449127421546 := by
        calc
          (13 : ZMod 3999803890129) ^ 465 = (13 : ZMod 3999803890129) ^ (232 + 232 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 232 * (13 : ZMod 3999803890129) ^ 232) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1449127421546 := by rw [fermat_7]; decide
      have fermat_9 : (13 : ZMod 3999803890129) ^ 931 = 148890432435 := by
        calc
          (13 : ZMod 3999803890129) ^ 931 = (13 : ZMod 3999803890129) ^ (465 + 465 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 465 * (13 : ZMod 3999803890129) ^ 465) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 148890432435 := by rw [fermat_8]; decide
      have fermat_10 : (13 : ZMod 3999803890129) ^ 1862 = 2567369288320 := by
        calc
          (13 : ZMod 3999803890129) ^ 1862 = (13 : ZMod 3999803890129) ^ (931 + 931) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 931 * (13 : ZMod 3999803890129) ^ 931 := by rw [pow_add]
          _ = 2567369288320 := by rw [fermat_9]; decide
      have fermat_11 : (13 : ZMod 3999803890129) ^ 3725 = 989699353118 := by
        calc
          (13 : ZMod 3999803890129) ^ 3725 = (13 : ZMod 3999803890129) ^ (1862 + 1862 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 1862 * (13 : ZMod 3999803890129) ^ 1862) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 989699353118 := by rw [fermat_10]; decide
      have fermat_12 : (13 : ZMod 3999803890129) ^ 7450 = 1193271697493 := by
        calc
          (13 : ZMod 3999803890129) ^ 7450 = (13 : ZMod 3999803890129) ^ (3725 + 3725) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 3725 * (13 : ZMod 3999803890129) ^ 3725 := by rw [pow_add]
          _ = 1193271697493 := by rw [fermat_11]; decide
      have fermat_13 : (13 : ZMod 3999803890129) ^ 14900 = 1719054004384 := by
        calc
          (13 : ZMod 3999803890129) ^ 14900 = (13 : ZMod 3999803890129) ^ (7450 + 7450) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 7450 * (13 : ZMod 3999803890129) ^ 7450 := by rw [pow_add]
          _ = 1719054004384 := by rw [fermat_12]; decide
      have fermat_14 : (13 : ZMod 3999803890129) ^ 29800 = 2337202715008 := by
        calc
          (13 : ZMod 3999803890129) ^ 29800 = (13 : ZMod 3999803890129) ^ (14900 + 14900) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 14900 * (13 : ZMod 3999803890129) ^ 14900 := by rw [pow_add]
          _ = 2337202715008 := by rw [fermat_13]; decide
      have fermat_15 : (13 : ZMod 3999803890129) ^ 59601 = 842742878637 := by
        calc
          (13 : ZMod 3999803890129) ^ 59601 = (13 : ZMod 3999803890129) ^ (29800 + 29800 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 29800 * (13 : ZMod 3999803890129) ^ 29800) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 842742878637 := by rw [fermat_14]; decide
      have fermat_16 : (13 : ZMod 3999803890129) ^ 119203 = 3513354663227 := by
        calc
          (13 : ZMod 3999803890129) ^ 119203 = (13 : ZMod 3999803890129) ^ (59601 + 59601 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 59601 * (13 : ZMod 3999803890129) ^ 59601) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3513354663227 := by rw [fermat_15]; decide
      have fermat_17 : (13 : ZMod 3999803890129) ^ 238406 = 3813110696801 := by
        calc
          (13 : ZMod 3999803890129) ^ 238406 = (13 : ZMod 3999803890129) ^ (119203 + 119203) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 119203 * (13 : ZMod 3999803890129) ^ 119203 := by rw [pow_add]
          _ = 3813110696801 := by rw [fermat_16]; decide
      have fermat_18 : (13 : ZMod 3999803890129) ^ 476813 = 2029876983184 := by
        calc
          (13 : ZMod 3999803890129) ^ 476813 = (13 : ZMod 3999803890129) ^ (238406 + 238406 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 238406 * (13 : ZMod 3999803890129) ^ 238406) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2029876983184 := by rw [fermat_17]; decide
      have fermat_19 : (13 : ZMod 3999803890129) ^ 953627 = 3720763874712 := by
        calc
          (13 : ZMod 3999803890129) ^ 953627 = (13 : ZMod 3999803890129) ^ (476813 + 476813 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 476813 * (13 : ZMod 3999803890129) ^ 476813) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3720763874712 := by rw [fermat_18]; decide
      have fermat_20 : (13 : ZMod 3999803890129) ^ 1907255 = 983890431604 := by
        calc
          (13 : ZMod 3999803890129) ^ 1907255 = (13 : ZMod 3999803890129) ^ (953627 + 953627 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 953627 * (13 : ZMod 3999803890129) ^ 953627) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 983890431604 := by rw [fermat_19]; decide
      have fermat_21 : (13 : ZMod 3999803890129) ^ 3814510 = 1470791174270 := by
        calc
          (13 : ZMod 3999803890129) ^ 3814510 = (13 : ZMod 3999803890129) ^ (1907255 + 1907255) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1907255 * (13 : ZMod 3999803890129) ^ 1907255 := by rw [pow_add]
          _ = 1470791174270 := by rw [fermat_20]; decide
      have fermat_22 : (13 : ZMod 3999803890129) ^ 7629020 = 719171624489 := by
        calc
          (13 : ZMod 3999803890129) ^ 7629020 = (13 : ZMod 3999803890129) ^ (3814510 + 3814510) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 3814510 * (13 : ZMod 3999803890129) ^ 3814510 := by rw [pow_add]
          _ = 719171624489 := by rw [fermat_21]; decide
      have fermat_23 : (13 : ZMod 3999803890129) ^ 15258040 = 3399917073896 := by
        calc
          (13 : ZMod 3999803890129) ^ 15258040 = (13 : ZMod 3999803890129) ^ (7629020 + 7629020) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 7629020 * (13 : ZMod 3999803890129) ^ 7629020 := by rw [pow_add]
          _ = 3399917073896 := by rw [fermat_22]; decide
      have fermat_24 : (13 : ZMod 3999803890129) ^ 30516081 = 799899849249 := by
        calc
          (13 : ZMod 3999803890129) ^ 30516081 = (13 : ZMod 3999803890129) ^ (15258040 + 15258040 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 15258040 * (13 : ZMod 3999803890129) ^ 15258040) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 799899849249 := by rw [fermat_23]; decide
      have fermat_25 : (13 : ZMod 3999803890129) ^ 61032163 = 1352070979216 := by
        calc
          (13 : ZMod 3999803890129) ^ 61032163 = (13 : ZMod 3999803890129) ^ (30516081 + 30516081 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 30516081 * (13 : ZMod 3999803890129) ^ 30516081) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1352070979216 := by rw [fermat_24]; decide
      have fermat_26 : (13 : ZMod 3999803890129) ^ 122064327 = 1704228371995 := by
        calc
          (13 : ZMod 3999803890129) ^ 122064327 = (13 : ZMod 3999803890129) ^ (61032163 + 61032163 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 61032163 * (13 : ZMod 3999803890129) ^ 61032163) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1704228371995 := by rw [fermat_25]; decide
      have fermat_27 : (13 : ZMod 3999803890129) ^ 244128655 = 2823241792276 := by
        calc
          (13 : ZMod 3999803890129) ^ 244128655 = (13 : ZMod 3999803890129) ^ (122064327 + 122064327 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 122064327 * (13 : ZMod 3999803890129) ^ 122064327) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2823241792276 := by rw [fermat_26]; decide
      have fermat_28 : (13 : ZMod 3999803890129) ^ 488257310 = 3539720882787 := by
        calc
          (13 : ZMod 3999803890129) ^ 488257310 = (13 : ZMod 3999803890129) ^ (244128655 + 244128655) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 244128655 * (13 : ZMod 3999803890129) ^ 244128655 := by rw [pow_add]
          _ = 3539720882787 := by rw [fermat_27]; decide
      have fermat_29 : (13 : ZMod 3999803890129) ^ 976514621 = 1523113322350 := by
        calc
          (13 : ZMod 3999803890129) ^ 976514621 = (13 : ZMod 3999803890129) ^ (488257310 + 488257310 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 488257310 * (13 : ZMod 3999803890129) ^ 488257310) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1523113322350 := by rw [fermat_28]; decide
      have fermat_30 : (13 : ZMod 3999803890129) ^ 1953029243 = 2885953325904 := by
        calc
          (13 : ZMod 3999803890129) ^ 1953029243 = (13 : ZMod 3999803890129) ^ (976514621 + 976514621 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 976514621 * (13 : ZMod 3999803890129) ^ 976514621) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2885953325904 := by rw [fermat_29]; decide
      have fermat_31 : (13 : ZMod 3999803890129) ^ 3906058486 = 3784628516278 := by
        calc
          (13 : ZMod 3999803890129) ^ 3906058486 = (13 : ZMod 3999803890129) ^ (1953029243 + 1953029243) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1953029243 * (13 : ZMod 3999803890129) ^ 1953029243 := by rw [pow_add]
          _ = 3784628516278 := by rw [fermat_30]; decide
      have fermat_32 : (13 : ZMod 3999803890129) ^ 7812116972 = 618105560585 := by
        calc
          (13 : ZMod 3999803890129) ^ 7812116972 = (13 : ZMod 3999803890129) ^ (3906058486 + 3906058486) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 3906058486 * (13 : ZMod 3999803890129) ^ 3906058486 := by rw [pow_add]
          _ = 618105560585 := by rw [fermat_31]; decide
      have fermat_33 : (13 : ZMod 3999803890129) ^ 15624233945 = 913926915517 := by
        calc
          (13 : ZMod 3999803890129) ^ 15624233945 = (13 : ZMod 3999803890129) ^ (7812116972 + 7812116972 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 7812116972 * (13 : ZMod 3999803890129) ^ 7812116972) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 913926915517 := by rw [fermat_32]; decide
      have fermat_34 : (13 : ZMod 3999803890129) ^ 31248467891 = 2317992374340 := by
        calc
          (13 : ZMod 3999803890129) ^ 31248467891 = (13 : ZMod 3999803890129) ^ (15624233945 + 15624233945 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 15624233945 * (13 : ZMod 3999803890129) ^ 15624233945) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2317992374340 := by rw [fermat_33]; decide
      have fermat_35 : (13 : ZMod 3999803890129) ^ 62496935783 = 585572905070 := by
        calc
          (13 : ZMod 3999803890129) ^ 62496935783 = (13 : ZMod 3999803890129) ^ (31248467891 + 31248467891 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 31248467891 * (13 : ZMod 3999803890129) ^ 31248467891) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 585572905070 := by rw [fermat_34]; decide
      have fermat_36 : (13 : ZMod 3999803890129) ^ 124993871566 = 677105738120 := by
        calc
          (13 : ZMod 3999803890129) ^ 124993871566 = (13 : ZMod 3999803890129) ^ (62496935783 + 62496935783) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 62496935783 * (13 : ZMod 3999803890129) ^ 62496935783 := by rw [pow_add]
          _ = 677105738120 := by rw [fermat_35]; decide
      have fermat_37 : (13 : ZMod 3999803890129) ^ 249987743133 = 1062181962398 := by
        calc
          (13 : ZMod 3999803890129) ^ 249987743133 = (13 : ZMod 3999803890129) ^ (124993871566 + 124993871566 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 124993871566 * (13 : ZMod 3999803890129) ^ 124993871566) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1062181962398 := by rw [fermat_36]; decide
      have fermat_38 : (13 : ZMod 3999803890129) ^ 499975486266 = 1213379227164 := by
        calc
          (13 : ZMod 3999803890129) ^ 499975486266 = (13 : ZMod 3999803890129) ^ (249987743133 + 249987743133) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 249987743133 * (13 : ZMod 3999803890129) ^ 249987743133 := by rw [pow_add]
          _ = 1213379227164 := by rw [fermat_37]; decide
      have fermat_39 : (13 : ZMod 3999803890129) ^ 999950972532 = 976916577211 := by
        calc
          (13 : ZMod 3999803890129) ^ 999950972532 = (13 : ZMod 3999803890129) ^ (499975486266 + 499975486266) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 499975486266 * (13 : ZMod 3999803890129) ^ 499975486266 := by rw [pow_add]
          _ = 976916577211 := by rw [fermat_38]; decide
      have fermat_40 : (13 : ZMod 3999803890129) ^ 1999901945064 = 3999803890128 := by
        calc
          (13 : ZMod 3999803890129) ^ 1999901945064 = (13 : ZMod 3999803890129) ^ (999950972532 + 999950972532) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 999950972532 * (13 : ZMod 3999803890129) ^ 999950972532 := by rw [pow_add]
          _ = 3999803890128 := by rw [fermat_39]; decide
      have fermat_41 : (13 : ZMod 3999803890129) ^ 3999803890128 = 1 := by
        calc
          (13 : ZMod 3999803890129) ^ 3999803890128 = (13 : ZMod 3999803890129) ^ (1999901945064 + 1999901945064) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1999901945064 * (13 : ZMod 3999803890129) ^ 1999901945064 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5923, 1), (14068757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5923, 1), (14068757, 1)] : List FactorBlock).map factorBlockValue).prod = 3999803890129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (13 : ZMod 3999803890129) ^ 1 = 13 := by norm_num
      have factor_0_1 : (13 : ZMod 3999803890129) ^ 3 = 2197 := by
        calc
          (13 : ZMod 3999803890129) ^ 3 = (13 : ZMod 3999803890129) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 1 * (13 : ZMod 3999803890129) ^ 1) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2197 := by rw [factor_0_0]; decide
      have factor_0_2 : (13 : ZMod 3999803890129) ^ 7 = 62748517 := by
        calc
          (13 : ZMod 3999803890129) ^ 7 = (13 : ZMod 3999803890129) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 3 * (13 : ZMod 3999803890129) ^ 3) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 62748517 := by rw [factor_0_1]; decide
      have factor_0_3 : (13 : ZMod 3999803890129) ^ 14 = 1569357812353 := by
        calc
          (13 : ZMod 3999803890129) ^ 14 = (13 : ZMod 3999803890129) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 7 * (13 : ZMod 3999803890129) ^ 7 := by rw [pow_add]
          _ = 1569357812353 := by rw [factor_0_2]; decide
      have factor_0_4 : (13 : ZMod 3999803890129) ^ 29 = 2361118877296 := by
        calc
          (13 : ZMod 3999803890129) ^ 29 = (13 : ZMod 3999803890129) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 14 * (13 : ZMod 3999803890129) ^ 14) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2361118877296 := by rw [factor_0_3]; decide
      have factor_0_5 : (13 : ZMod 3999803890129) ^ 58 = 1242078737878 := by
        calc
          (13 : ZMod 3999803890129) ^ 58 = (13 : ZMod 3999803890129) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 29 * (13 : ZMod 3999803890129) ^ 29 := by rw [pow_add]
          _ = 1242078737878 := by rw [factor_0_4]; decide
      have factor_0_6 : (13 : ZMod 3999803890129) ^ 116 = 1205094478242 := by
        calc
          (13 : ZMod 3999803890129) ^ 116 = (13 : ZMod 3999803890129) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 58 * (13 : ZMod 3999803890129) ^ 58 := by rw [pow_add]
          _ = 1205094478242 := by rw [factor_0_5]; decide
      have factor_0_7 : (13 : ZMod 3999803890129) ^ 232 = 785507896187 := by
        calc
          (13 : ZMod 3999803890129) ^ 232 = (13 : ZMod 3999803890129) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 116 * (13 : ZMod 3999803890129) ^ 116 := by rw [pow_add]
          _ = 785507896187 := by rw [factor_0_6]; decide
      have factor_0_8 : (13 : ZMod 3999803890129) ^ 465 = 1449127421546 := by
        calc
          (13 : ZMod 3999803890129) ^ 465 = (13 : ZMod 3999803890129) ^ (232 + 232 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 232 * (13 : ZMod 3999803890129) ^ 232) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1449127421546 := by rw [factor_0_7]; decide
      have factor_0_9 : (13 : ZMod 3999803890129) ^ 931 = 148890432435 := by
        calc
          (13 : ZMod 3999803890129) ^ 931 = (13 : ZMod 3999803890129) ^ (465 + 465 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 465 * (13 : ZMod 3999803890129) ^ 465) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 148890432435 := by rw [factor_0_8]; decide
      have factor_0_10 : (13 : ZMod 3999803890129) ^ 1862 = 2567369288320 := by
        calc
          (13 : ZMod 3999803890129) ^ 1862 = (13 : ZMod 3999803890129) ^ (931 + 931) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 931 * (13 : ZMod 3999803890129) ^ 931 := by rw [pow_add]
          _ = 2567369288320 := by rw [factor_0_9]; decide
      have factor_0_11 : (13 : ZMod 3999803890129) ^ 3725 = 989699353118 := by
        calc
          (13 : ZMod 3999803890129) ^ 3725 = (13 : ZMod 3999803890129) ^ (1862 + 1862 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 1862 * (13 : ZMod 3999803890129) ^ 1862) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 989699353118 := by rw [factor_0_10]; decide
      have factor_0_12 : (13 : ZMod 3999803890129) ^ 7450 = 1193271697493 := by
        calc
          (13 : ZMod 3999803890129) ^ 7450 = (13 : ZMod 3999803890129) ^ (3725 + 3725) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 3725 * (13 : ZMod 3999803890129) ^ 3725 := by rw [pow_add]
          _ = 1193271697493 := by rw [factor_0_11]; decide
      have factor_0_13 : (13 : ZMod 3999803890129) ^ 14900 = 1719054004384 := by
        calc
          (13 : ZMod 3999803890129) ^ 14900 = (13 : ZMod 3999803890129) ^ (7450 + 7450) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 7450 * (13 : ZMod 3999803890129) ^ 7450 := by rw [pow_add]
          _ = 1719054004384 := by rw [factor_0_12]; decide
      have factor_0_14 : (13 : ZMod 3999803890129) ^ 29800 = 2337202715008 := by
        calc
          (13 : ZMod 3999803890129) ^ 29800 = (13 : ZMod 3999803890129) ^ (14900 + 14900) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 14900 * (13 : ZMod 3999803890129) ^ 14900 := by rw [pow_add]
          _ = 2337202715008 := by rw [factor_0_13]; decide
      have factor_0_15 : (13 : ZMod 3999803890129) ^ 59601 = 842742878637 := by
        calc
          (13 : ZMod 3999803890129) ^ 59601 = (13 : ZMod 3999803890129) ^ (29800 + 29800 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 29800 * (13 : ZMod 3999803890129) ^ 29800) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 842742878637 := by rw [factor_0_14]; decide
      have factor_0_16 : (13 : ZMod 3999803890129) ^ 119203 = 3513354663227 := by
        calc
          (13 : ZMod 3999803890129) ^ 119203 = (13 : ZMod 3999803890129) ^ (59601 + 59601 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 59601 * (13 : ZMod 3999803890129) ^ 59601) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3513354663227 := by rw [factor_0_15]; decide
      have factor_0_17 : (13 : ZMod 3999803890129) ^ 238406 = 3813110696801 := by
        calc
          (13 : ZMod 3999803890129) ^ 238406 = (13 : ZMod 3999803890129) ^ (119203 + 119203) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 119203 * (13 : ZMod 3999803890129) ^ 119203 := by rw [pow_add]
          _ = 3813110696801 := by rw [factor_0_16]; decide
      have factor_0_18 : (13 : ZMod 3999803890129) ^ 476813 = 2029876983184 := by
        calc
          (13 : ZMod 3999803890129) ^ 476813 = (13 : ZMod 3999803890129) ^ (238406 + 238406 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 238406 * (13 : ZMod 3999803890129) ^ 238406) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2029876983184 := by rw [factor_0_17]; decide
      have factor_0_19 : (13 : ZMod 3999803890129) ^ 953627 = 3720763874712 := by
        calc
          (13 : ZMod 3999803890129) ^ 953627 = (13 : ZMod 3999803890129) ^ (476813 + 476813 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 476813 * (13 : ZMod 3999803890129) ^ 476813) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3720763874712 := by rw [factor_0_18]; decide
      have factor_0_20 : (13 : ZMod 3999803890129) ^ 1907255 = 983890431604 := by
        calc
          (13 : ZMod 3999803890129) ^ 1907255 = (13 : ZMod 3999803890129) ^ (953627 + 953627 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 953627 * (13 : ZMod 3999803890129) ^ 953627) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 983890431604 := by rw [factor_0_19]; decide
      have factor_0_21 : (13 : ZMod 3999803890129) ^ 3814510 = 1470791174270 := by
        calc
          (13 : ZMod 3999803890129) ^ 3814510 = (13 : ZMod 3999803890129) ^ (1907255 + 1907255) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1907255 * (13 : ZMod 3999803890129) ^ 1907255 := by rw [pow_add]
          _ = 1470791174270 := by rw [factor_0_20]; decide
      have factor_0_22 : (13 : ZMod 3999803890129) ^ 7629020 = 719171624489 := by
        calc
          (13 : ZMod 3999803890129) ^ 7629020 = (13 : ZMod 3999803890129) ^ (3814510 + 3814510) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 3814510 * (13 : ZMod 3999803890129) ^ 3814510 := by rw [pow_add]
          _ = 719171624489 := by rw [factor_0_21]; decide
      have factor_0_23 : (13 : ZMod 3999803890129) ^ 15258040 = 3399917073896 := by
        calc
          (13 : ZMod 3999803890129) ^ 15258040 = (13 : ZMod 3999803890129) ^ (7629020 + 7629020) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 7629020 * (13 : ZMod 3999803890129) ^ 7629020 := by rw [pow_add]
          _ = 3399917073896 := by rw [factor_0_22]; decide
      have factor_0_24 : (13 : ZMod 3999803890129) ^ 30516081 = 799899849249 := by
        calc
          (13 : ZMod 3999803890129) ^ 30516081 = (13 : ZMod 3999803890129) ^ (15258040 + 15258040 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 15258040 * (13 : ZMod 3999803890129) ^ 15258040) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 799899849249 := by rw [factor_0_23]; decide
      have factor_0_25 : (13 : ZMod 3999803890129) ^ 61032163 = 1352070979216 := by
        calc
          (13 : ZMod 3999803890129) ^ 61032163 = (13 : ZMod 3999803890129) ^ (30516081 + 30516081 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 30516081 * (13 : ZMod 3999803890129) ^ 30516081) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1352070979216 := by rw [factor_0_24]; decide
      have factor_0_26 : (13 : ZMod 3999803890129) ^ 122064327 = 1704228371995 := by
        calc
          (13 : ZMod 3999803890129) ^ 122064327 = (13 : ZMod 3999803890129) ^ (61032163 + 61032163 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 61032163 * (13 : ZMod 3999803890129) ^ 61032163) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1704228371995 := by rw [factor_0_25]; decide
      have factor_0_27 : (13 : ZMod 3999803890129) ^ 244128655 = 2823241792276 := by
        calc
          (13 : ZMod 3999803890129) ^ 244128655 = (13 : ZMod 3999803890129) ^ (122064327 + 122064327 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 122064327 * (13 : ZMod 3999803890129) ^ 122064327) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2823241792276 := by rw [factor_0_26]; decide
      have factor_0_28 : (13 : ZMod 3999803890129) ^ 488257310 = 3539720882787 := by
        calc
          (13 : ZMod 3999803890129) ^ 488257310 = (13 : ZMod 3999803890129) ^ (244128655 + 244128655) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 244128655 * (13 : ZMod 3999803890129) ^ 244128655 := by rw [pow_add]
          _ = 3539720882787 := by rw [factor_0_27]; decide
      have factor_0_29 : (13 : ZMod 3999803890129) ^ 976514621 = 1523113322350 := by
        calc
          (13 : ZMod 3999803890129) ^ 976514621 = (13 : ZMod 3999803890129) ^ (488257310 + 488257310 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 488257310 * (13 : ZMod 3999803890129) ^ 488257310) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1523113322350 := by rw [factor_0_28]; decide
      have factor_0_30 : (13 : ZMod 3999803890129) ^ 1953029243 = 2885953325904 := by
        calc
          (13 : ZMod 3999803890129) ^ 1953029243 = (13 : ZMod 3999803890129) ^ (976514621 + 976514621 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 976514621 * (13 : ZMod 3999803890129) ^ 976514621) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2885953325904 := by rw [factor_0_29]; decide
      have factor_0_31 : (13 : ZMod 3999803890129) ^ 3906058486 = 3784628516278 := by
        calc
          (13 : ZMod 3999803890129) ^ 3906058486 = (13 : ZMod 3999803890129) ^ (1953029243 + 1953029243) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1953029243 * (13 : ZMod 3999803890129) ^ 1953029243 := by rw [pow_add]
          _ = 3784628516278 := by rw [factor_0_30]; decide
      have factor_0_32 : (13 : ZMod 3999803890129) ^ 7812116972 = 618105560585 := by
        calc
          (13 : ZMod 3999803890129) ^ 7812116972 = (13 : ZMod 3999803890129) ^ (3906058486 + 3906058486) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 3906058486 * (13 : ZMod 3999803890129) ^ 3906058486 := by rw [pow_add]
          _ = 618105560585 := by rw [factor_0_31]; decide
      have factor_0_33 : (13 : ZMod 3999803890129) ^ 15624233945 = 913926915517 := by
        calc
          (13 : ZMod 3999803890129) ^ 15624233945 = (13 : ZMod 3999803890129) ^ (7812116972 + 7812116972 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 7812116972 * (13 : ZMod 3999803890129) ^ 7812116972) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 913926915517 := by rw [factor_0_32]; decide
      have factor_0_34 : (13 : ZMod 3999803890129) ^ 31248467891 = 2317992374340 := by
        calc
          (13 : ZMod 3999803890129) ^ 31248467891 = (13 : ZMod 3999803890129) ^ (15624233945 + 15624233945 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 15624233945 * (13 : ZMod 3999803890129) ^ 15624233945) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2317992374340 := by rw [factor_0_33]; decide
      have factor_0_35 : (13 : ZMod 3999803890129) ^ 62496935783 = 585572905070 := by
        calc
          (13 : ZMod 3999803890129) ^ 62496935783 = (13 : ZMod 3999803890129) ^ (31248467891 + 31248467891 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 31248467891 * (13 : ZMod 3999803890129) ^ 31248467891) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 585572905070 := by rw [factor_0_34]; decide
      have factor_0_36 : (13 : ZMod 3999803890129) ^ 124993871566 = 677105738120 := by
        calc
          (13 : ZMod 3999803890129) ^ 124993871566 = (13 : ZMod 3999803890129) ^ (62496935783 + 62496935783) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 62496935783 * (13 : ZMod 3999803890129) ^ 62496935783 := by rw [pow_add]
          _ = 677105738120 := by rw [factor_0_35]; decide
      have factor_0_37 : (13 : ZMod 3999803890129) ^ 249987743133 = 1062181962398 := by
        calc
          (13 : ZMod 3999803890129) ^ 249987743133 = (13 : ZMod 3999803890129) ^ (124993871566 + 124993871566 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 124993871566 * (13 : ZMod 3999803890129) ^ 124993871566) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1062181962398 := by rw [factor_0_36]; decide
      have factor_0_38 : (13 : ZMod 3999803890129) ^ 499975486266 = 1213379227164 := by
        calc
          (13 : ZMod 3999803890129) ^ 499975486266 = (13 : ZMod 3999803890129) ^ (249987743133 + 249987743133) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 249987743133 * (13 : ZMod 3999803890129) ^ 249987743133 := by rw [pow_add]
          _ = 1213379227164 := by rw [factor_0_37]; decide
      have factor_0_39 : (13 : ZMod 3999803890129) ^ 999950972532 = 976916577211 := by
        calc
          (13 : ZMod 3999803890129) ^ 999950972532 = (13 : ZMod 3999803890129) ^ (499975486266 + 499975486266) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 499975486266 * (13 : ZMod 3999803890129) ^ 499975486266 := by rw [pow_add]
          _ = 976916577211 := by rw [factor_0_38]; decide
      have factor_0_40 : (13 : ZMod 3999803890129) ^ 1999901945064 = 3999803890128 := by
        calc
          (13 : ZMod 3999803890129) ^ 1999901945064 = (13 : ZMod 3999803890129) ^ (999950972532 + 999950972532) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 999950972532 * (13 : ZMod 3999803890129) ^ 999950972532 := by rw [pow_add]
          _ = 3999803890128 := by rw [factor_0_39]; decide
      change (13 : ZMod 3999803890129) ^ 1999901945064 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (13 : ZMod 3999803890129) ^ 1 = 13 := by norm_num
      have factor_1_1 : (13 : ZMod 3999803890129) ^ 2 = 169 := by
        calc
          (13 : ZMod 3999803890129) ^ 2 = (13 : ZMod 3999803890129) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1 * (13 : ZMod 3999803890129) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_1_0]; decide
      have factor_1_2 : (13 : ZMod 3999803890129) ^ 4 = 28561 := by
        calc
          (13 : ZMod 3999803890129) ^ 4 = (13 : ZMod 3999803890129) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 2 * (13 : ZMod 3999803890129) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_1_1]; decide
      have factor_1_3 : (13 : ZMod 3999803890129) ^ 9 = 10604499373 := by
        calc
          (13 : ZMod 3999803890129) ^ 9 = (13 : ZMod 3999803890129) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 4 * (13 : ZMod 3999803890129) ^ 4) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 10604499373 := by rw [factor_1_2]; decide
      have factor_1_4 : (13 : ZMod 3999803890129) ^ 19 = 139507989709 := by
        calc
          (13 : ZMod 3999803890129) ^ 19 = (13 : ZMod 3999803890129) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 9 * (13 : ZMod 3999803890129) ^ 9) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 139507989709 := by rw [factor_1_3]; decide
      have factor_1_5 : (13 : ZMod 3999803890129) ^ 38 = 3501341556499 := by
        calc
          (13 : ZMod 3999803890129) ^ 38 = (13 : ZMod 3999803890129) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 19 * (13 : ZMod 3999803890129) ^ 19 := by rw [pow_add]
          _ = 3501341556499 := by rw [factor_1_4]; decide
      have factor_1_6 : (13 : ZMod 3999803890129) ^ 77 = 1274210459080 := by
        calc
          (13 : ZMod 3999803890129) ^ 77 = (13 : ZMod 3999803890129) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 38 * (13 : ZMod 3999803890129) ^ 38) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1274210459080 := by rw [factor_1_5]; decide
      have factor_1_7 : (13 : ZMod 3999803890129) ^ 155 = 359157284796 := by
        calc
          (13 : ZMod 3999803890129) ^ 155 = (13 : ZMod 3999803890129) ^ (77 + 77 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 77 * (13 : ZMod 3999803890129) ^ 77) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 359157284796 := by rw [factor_1_6]; decide
      have factor_1_8 : (13 : ZMod 3999803890129) ^ 310 = 3091511578840 := by
        calc
          (13 : ZMod 3999803890129) ^ 310 = (13 : ZMod 3999803890129) ^ (155 + 155) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 155 * (13 : ZMod 3999803890129) ^ 155 := by rw [pow_add]
          _ = 3091511578840 := by rw [factor_1_7]; decide
      have factor_1_9 : (13 : ZMod 3999803890129) ^ 620 = 1813879940006 := by
        calc
          (13 : ZMod 3999803890129) ^ 620 = (13 : ZMod 3999803890129) ^ (310 + 310) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 310 * (13 : ZMod 3999803890129) ^ 310 := by rw [pow_add]
          _ = 1813879940006 := by rw [factor_1_8]; decide
      have factor_1_10 : (13 : ZMod 3999803890129) ^ 1241 = 1368441377272 := by
        calc
          (13 : ZMod 3999803890129) ^ 1241 = (13 : ZMod 3999803890129) ^ (620 + 620 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 620 * (13 : ZMod 3999803890129) ^ 620) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1368441377272 := by rw [factor_1_9]; decide
      have factor_1_11 : (13 : ZMod 3999803890129) ^ 2483 = 1320480109994 := by
        calc
          (13 : ZMod 3999803890129) ^ 2483 = (13 : ZMod 3999803890129) ^ (1241 + 1241 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 1241 * (13 : ZMod 3999803890129) ^ 1241) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1320480109994 := by rw [factor_1_10]; decide
      have factor_1_12 : (13 : ZMod 3999803890129) ^ 4966 = 2165554600719 := by
        calc
          (13 : ZMod 3999803890129) ^ 4966 = (13 : ZMod 3999803890129) ^ (2483 + 2483) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 2483 * (13 : ZMod 3999803890129) ^ 2483 := by rw [pow_add]
          _ = 2165554600719 := by rw [factor_1_11]; decide
      have factor_1_13 : (13 : ZMod 3999803890129) ^ 9933 = 224431879480 := by
        calc
          (13 : ZMod 3999803890129) ^ 9933 = (13 : ZMod 3999803890129) ^ (4966 + 4966 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 4966 * (13 : ZMod 3999803890129) ^ 4966) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 224431879480 := by rw [factor_1_12]; decide
      have factor_1_14 : (13 : ZMod 3999803890129) ^ 19867 = 947565917812 := by
        calc
          (13 : ZMod 3999803890129) ^ 19867 = (13 : ZMod 3999803890129) ^ (9933 + 9933 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 9933 * (13 : ZMod 3999803890129) ^ 9933) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 947565917812 := by rw [factor_1_13]; decide
      have factor_1_15 : (13 : ZMod 3999803890129) ^ 39734 = 1270824328373 := by
        calc
          (13 : ZMod 3999803890129) ^ 39734 = (13 : ZMod 3999803890129) ^ (19867 + 19867) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 19867 * (13 : ZMod 3999803890129) ^ 19867 := by rw [pow_add]
          _ = 1270824328373 := by rw [factor_1_14]; decide
      have factor_1_16 : (13 : ZMod 3999803890129) ^ 79468 = 297206693198 := by
        calc
          (13 : ZMod 3999803890129) ^ 79468 = (13 : ZMod 3999803890129) ^ (39734 + 39734) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 39734 * (13 : ZMod 3999803890129) ^ 39734 := by rw [pow_add]
          _ = 297206693198 := by rw [factor_1_15]; decide
      have factor_1_17 : (13 : ZMod 3999803890129) ^ 158937 = 264433576345 := by
        calc
          (13 : ZMod 3999803890129) ^ 158937 = (13 : ZMod 3999803890129) ^ (79468 + 79468 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 79468 * (13 : ZMod 3999803890129) ^ 79468) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 264433576345 := by rw [factor_1_16]; decide
      have factor_1_18 : (13 : ZMod 3999803890129) ^ 317875 = 3012728524368 := by
        calc
          (13 : ZMod 3999803890129) ^ 317875 = (13 : ZMod 3999803890129) ^ (158937 + 158937 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 158937 * (13 : ZMod 3999803890129) ^ 158937) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3012728524368 := by rw [factor_1_17]; decide
      have factor_1_19 : (13 : ZMod 3999803890129) ^ 635751 = 246109715418 := by
        calc
          (13 : ZMod 3999803890129) ^ 635751 = (13 : ZMod 3999803890129) ^ (317875 + 317875 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 317875 * (13 : ZMod 3999803890129) ^ 317875) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 246109715418 := by rw [factor_1_18]; decide
      have factor_1_20 : (13 : ZMod 3999803890129) ^ 1271503 = 2757221532758 := by
        calc
          (13 : ZMod 3999803890129) ^ 1271503 = (13 : ZMod 3999803890129) ^ (635751 + 635751 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 635751 * (13 : ZMod 3999803890129) ^ 635751) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2757221532758 := by rw [factor_1_19]; decide
      have factor_1_21 : (13 : ZMod 3999803890129) ^ 2543006 = 2514441977137 := by
        calc
          (13 : ZMod 3999803890129) ^ 2543006 = (13 : ZMod 3999803890129) ^ (1271503 + 1271503) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1271503 * (13 : ZMod 3999803890129) ^ 1271503 := by rw [pow_add]
          _ = 2514441977137 := by rw [factor_1_20]; decide
      have factor_1_22 : (13 : ZMod 3999803890129) ^ 5086013 = 3418749054455 := by
        calc
          (13 : ZMod 3999803890129) ^ 5086013 = (13 : ZMod 3999803890129) ^ (2543006 + 2543006 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 2543006 * (13 : ZMod 3999803890129) ^ 2543006) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3418749054455 := by rw [factor_1_21]; decide
      have factor_1_23 : (13 : ZMod 3999803890129) ^ 10172027 = 3665801574627 := by
        calc
          (13 : ZMod 3999803890129) ^ 10172027 = (13 : ZMod 3999803890129) ^ (5086013 + 5086013 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 5086013 * (13 : ZMod 3999803890129) ^ 5086013) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3665801574627 := by rw [factor_1_22]; decide
      have factor_1_24 : (13 : ZMod 3999803890129) ^ 20344054 = 886781562717 := by
        calc
          (13 : ZMod 3999803890129) ^ 20344054 = (13 : ZMod 3999803890129) ^ (10172027 + 10172027) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 10172027 * (13 : ZMod 3999803890129) ^ 10172027 := by rw [pow_add]
          _ = 886781562717 := by rw [factor_1_23]; decide
      have factor_1_25 : (13 : ZMod 3999803890129) ^ 40688109 = 1191921591819 := by
        calc
          (13 : ZMod 3999803890129) ^ 40688109 = (13 : ZMod 3999803890129) ^ (20344054 + 20344054 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 20344054 * (13 : ZMod 3999803890129) ^ 20344054) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1191921591819 := by rw [factor_1_24]; decide
      have factor_1_26 : (13 : ZMod 3999803890129) ^ 81376218 = 3151167511605 := by
        calc
          (13 : ZMod 3999803890129) ^ 81376218 = (13 : ZMod 3999803890129) ^ (40688109 + 40688109) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 40688109 * (13 : ZMod 3999803890129) ^ 40688109 := by rw [pow_add]
          _ = 3151167511605 := by rw [factor_1_25]; decide
      have factor_1_27 : (13 : ZMod 3999803890129) ^ 162752436 = 785547604233 := by
        calc
          (13 : ZMod 3999803890129) ^ 162752436 = (13 : ZMod 3999803890129) ^ (81376218 + 81376218) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 81376218 * (13 : ZMod 3999803890129) ^ 81376218 := by rw [pow_add]
          _ = 785547604233 := by rw [factor_1_26]; decide
      have factor_1_28 : (13 : ZMod 3999803890129) ^ 325504873 = 1022141259495 := by
        calc
          (13 : ZMod 3999803890129) ^ 325504873 = (13 : ZMod 3999803890129) ^ (162752436 + 162752436 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 162752436 * (13 : ZMod 3999803890129) ^ 162752436) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1022141259495 := by rw [factor_1_27]; decide
      have factor_1_29 : (13 : ZMod 3999803890129) ^ 651009747 = 3754790396911 := by
        calc
          (13 : ZMod 3999803890129) ^ 651009747 = (13 : ZMod 3999803890129) ^ (325504873 + 325504873 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 325504873 * (13 : ZMod 3999803890129) ^ 325504873) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3754790396911 := by rw [factor_1_28]; decide
      have factor_1_30 : (13 : ZMod 3999803890129) ^ 1302019495 = 2377101003825 := by
        calc
          (13 : ZMod 3999803890129) ^ 1302019495 = (13 : ZMod 3999803890129) ^ (651009747 + 651009747 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 651009747 * (13 : ZMod 3999803890129) ^ 651009747) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2377101003825 := by rw [factor_1_29]; decide
      have factor_1_31 : (13 : ZMod 3999803890129) ^ 2604038990 = 273308949972 := by
        calc
          (13 : ZMod 3999803890129) ^ 2604038990 = (13 : ZMod 3999803890129) ^ (1302019495 + 1302019495) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1302019495 * (13 : ZMod 3999803890129) ^ 1302019495 := by rw [pow_add]
          _ = 273308949972 := by rw [factor_1_30]; decide
      have factor_1_32 : (13 : ZMod 3999803890129) ^ 5208077981 = 2994388989573 := by
        calc
          (13 : ZMod 3999803890129) ^ 5208077981 = (13 : ZMod 3999803890129) ^ (2604038990 + 2604038990 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 2604038990 * (13 : ZMod 3999803890129) ^ 2604038990) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2994388989573 := by rw [factor_1_31]; decide
      have factor_1_33 : (13 : ZMod 3999803890129) ^ 10416155963 = 499272089955 := by
        calc
          (13 : ZMod 3999803890129) ^ 10416155963 = (13 : ZMod 3999803890129) ^ (5208077981 + 5208077981 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 5208077981 * (13 : ZMod 3999803890129) ^ 5208077981) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 499272089955 := by rw [factor_1_32]; decide
      have factor_1_34 : (13 : ZMod 3999803890129) ^ 20832311927 = 3362201280365 := by
        calc
          (13 : ZMod 3999803890129) ^ 20832311927 = (13 : ZMod 3999803890129) ^ (10416155963 + 10416155963 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 10416155963 * (13 : ZMod 3999803890129) ^ 10416155963) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3362201280365 := by rw [factor_1_33]; decide
      have factor_1_35 : (13 : ZMod 3999803890129) ^ 41664623855 = 3932957805094 := by
        calc
          (13 : ZMod 3999803890129) ^ 41664623855 = (13 : ZMod 3999803890129) ^ (20832311927 + 20832311927 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 20832311927 * (13 : ZMod 3999803890129) ^ 20832311927) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3932957805094 := by rw [factor_1_34]; decide
      have factor_1_36 : (13 : ZMod 3999803890129) ^ 83329247711 = 15385808346 := by
        calc
          (13 : ZMod 3999803890129) ^ 83329247711 = (13 : ZMod 3999803890129) ^ (41664623855 + 41664623855 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 41664623855 * (13 : ZMod 3999803890129) ^ 41664623855) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 15385808346 := by rw [factor_1_35]; decide
      have factor_1_37 : (13 : ZMod 3999803890129) ^ 166658495422 = 962908921512 := by
        calc
          (13 : ZMod 3999803890129) ^ 166658495422 = (13 : ZMod 3999803890129) ^ (83329247711 + 83329247711) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 83329247711 * (13 : ZMod 3999803890129) ^ 83329247711 := by rw [pow_add]
          _ = 962908921512 := by rw [factor_1_36]; decide
      have factor_1_38 : (13 : ZMod 3999803890129) ^ 333316990844 = 2087519931461 := by
        calc
          (13 : ZMod 3999803890129) ^ 333316990844 = (13 : ZMod 3999803890129) ^ (166658495422 + 166658495422) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 166658495422 * (13 : ZMod 3999803890129) ^ 166658495422 := by rw [pow_add]
          _ = 2087519931461 := by rw [factor_1_37]; decide
      have factor_1_39 : (13 : ZMod 3999803890129) ^ 666633981688 = 1163997786744 := by
        calc
          (13 : ZMod 3999803890129) ^ 666633981688 = (13 : ZMod 3999803890129) ^ (333316990844 + 333316990844) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 333316990844 * (13 : ZMod 3999803890129) ^ 333316990844 := by rw [pow_add]
          _ = 1163997786744 := by rw [factor_1_38]; decide
      have factor_1_40 : (13 : ZMod 3999803890129) ^ 1333267963376 = 1163997786743 := by
        calc
          (13 : ZMod 3999803890129) ^ 1333267963376 = (13 : ZMod 3999803890129) ^ (666633981688 + 666633981688) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 666633981688 * (13 : ZMod 3999803890129) ^ 666633981688 := by rw [pow_add]
          _ = 1163997786743 := by rw [factor_1_39]; decide
      change (13 : ZMod 3999803890129) ^ 1333267963376 ≠ 1
      rw [factor_1_40]
      decide
    ·
      have factor_2_0 : (13 : ZMod 3999803890129) ^ 1 = 13 := by norm_num
      have factor_2_1 : (13 : ZMod 3999803890129) ^ 2 = 169 := by
        calc
          (13 : ZMod 3999803890129) ^ 2 = (13 : ZMod 3999803890129) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1 * (13 : ZMod 3999803890129) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_2_0]; decide
      have factor_2_2 : (13 : ZMod 3999803890129) ^ 5 = 371293 := by
        calc
          (13 : ZMod 3999803890129) ^ 5 = (13 : ZMod 3999803890129) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 2 * (13 : ZMod 3999803890129) ^ 2) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 371293 := by rw [factor_2_1]; decide
      have factor_2_3 : (13 : ZMod 3999803890129) ^ 10 = 137858491849 := by
        calc
          (13 : ZMod 3999803890129) ^ 10 = (13 : ZMod 3999803890129) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 5 * (13 : ZMod 3999803890129) ^ 5 := by rw [pow_add]
          _ = 137858491849 := by rw [factor_2_2]; decide
      have factor_2_4 : (13 : ZMod 3999803890129) ^ 20 = 1813603866217 := by
        calc
          (13 : ZMod 3999803890129) ^ 20 = (13 : ZMod 3999803890129) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 10 * (13 : ZMod 3999803890129) ^ 10 := by rw [pow_add]
          _ = 1813603866217 := by rw [factor_2_3]; decide
      have factor_2_5 : (13 : ZMod 3999803890129) ^ 40 = 3755551199368 := by
        calc
          (13 : ZMod 3999803890129) ^ 40 = (13 : ZMod 3999803890129) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 20 * (13 : ZMod 3999803890129) ^ 20 := by rw [pow_add]
          _ = 3755551199368 := by rw [factor_2_4]; decide
      have factor_2_6 : (13 : ZMod 3999803890129) ^ 80 = 3577459398589 := by
        calc
          (13 : ZMod 3999803890129) ^ 80 = (13 : ZMod 3999803890129) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 40 * (13 : ZMod 3999803890129) ^ 40 := by rw [pow_add]
          _ = 3577459398589 := by rw [factor_2_5]; decide
      have factor_2_7 : (13 : ZMod 3999803890129) ^ 161 = 612020855171 := by
        calc
          (13 : ZMod 3999803890129) ^ 161 = (13 : ZMod 3999803890129) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 80 * (13 : ZMod 3999803890129) ^ 80) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 612020855171 := by rw [factor_2_6]; decide
      have factor_2_8 : (13 : ZMod 3999803890129) ^ 322 = 49475063856 := by
        calc
          (13 : ZMod 3999803890129) ^ 322 = (13 : ZMod 3999803890129) ^ (161 + 161) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 161 * (13 : ZMod 3999803890129) ^ 161 := by rw [pow_add]
          _ = 49475063856 := by rw [factor_2_7]; decide
      have factor_2_9 : (13 : ZMod 3999803890129) ^ 644 = 1989480540655 := by
        calc
          (13 : ZMod 3999803890129) ^ 644 = (13 : ZMod 3999803890129) ^ (322 + 322) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 322 * (13 : ZMod 3999803890129) ^ 322 := by rw [pow_add]
          _ = 1989480540655 := by rw [factor_2_8]; decide
      have factor_2_10 : (13 : ZMod 3999803890129) ^ 1288 = 1788302646666 := by
        calc
          (13 : ZMod 3999803890129) ^ 1288 = (13 : ZMod 3999803890129) ^ (644 + 644) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 644 * (13 : ZMod 3999803890129) ^ 644 := by rw [pow_add]
          _ = 1788302646666 := by rw [factor_2_9]; decide
      have factor_2_11 : (13 : ZMod 3999803890129) ^ 2576 = 2105501700289 := by
        calc
          (13 : ZMod 3999803890129) ^ 2576 = (13 : ZMod 3999803890129) ^ (1288 + 1288) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1288 * (13 : ZMod 3999803890129) ^ 1288 := by rw [pow_add]
          _ = 2105501700289 := by rw [factor_2_10]; decide
      have factor_2_12 : (13 : ZMod 3999803890129) ^ 5152 = 1688082567570 := by
        calc
          (13 : ZMod 3999803890129) ^ 5152 = (13 : ZMod 3999803890129) ^ (2576 + 2576) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 2576 * (13 : ZMod 3999803890129) ^ 2576 := by rw [pow_add]
          _ = 1688082567570 := by rw [factor_2_11]; decide
      have factor_2_13 : (13 : ZMod 3999803890129) ^ 10304 = 3393576116832 := by
        calc
          (13 : ZMod 3999803890129) ^ 10304 = (13 : ZMod 3999803890129) ^ (5152 + 5152) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 5152 * (13 : ZMod 3999803890129) ^ 5152 := by rw [pow_add]
          _ = 3393576116832 := by rw [factor_2_12]; decide
      have factor_2_14 : (13 : ZMod 3999803890129) ^ 20608 = 341826657146 := by
        calc
          (13 : ZMod 3999803890129) ^ 20608 = (13 : ZMod 3999803890129) ^ (10304 + 10304) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 10304 * (13 : ZMod 3999803890129) ^ 10304 := by rw [pow_add]
          _ = 341826657146 := by rw [factor_2_13]; decide
      have factor_2_15 : (13 : ZMod 3999803890129) ^ 41217 = 1821770952962 := by
        calc
          (13 : ZMod 3999803890129) ^ 41217 = (13 : ZMod 3999803890129) ^ (20608 + 20608 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 20608 * (13 : ZMod 3999803890129) ^ 20608) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1821770952962 := by rw [factor_2_14]; decide
      have factor_2_16 : (13 : ZMod 3999803890129) ^ 82434 = 131974391378 := by
        calc
          (13 : ZMod 3999803890129) ^ 82434 = (13 : ZMod 3999803890129) ^ (41217 + 41217) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 41217 * (13 : ZMod 3999803890129) ^ 41217 := by rw [pow_add]
          _ = 131974391378 := by rw [factor_2_15]; decide
      have factor_2_17 : (13 : ZMod 3999803890129) ^ 164868 = 632626669190 := by
        calc
          (13 : ZMod 3999803890129) ^ 164868 = (13 : ZMod 3999803890129) ^ (82434 + 82434) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 82434 * (13 : ZMod 3999803890129) ^ 82434 := by rw [pow_add]
          _ = 632626669190 := by rw [factor_2_16]; decide
      have factor_2_18 : (13 : ZMod 3999803890129) ^ 329736 = 2150989350593 := by
        calc
          (13 : ZMod 3999803890129) ^ 329736 = (13 : ZMod 3999803890129) ^ (164868 + 164868) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 164868 * (13 : ZMod 3999803890129) ^ 164868 := by rw [pow_add]
          _ = 2150989350593 := by rw [factor_2_17]; decide
      have factor_2_19 : (13 : ZMod 3999803890129) ^ 659472 = 1024901144323 := by
        calc
          (13 : ZMod 3999803890129) ^ 659472 = (13 : ZMod 3999803890129) ^ (329736 + 329736) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 329736 * (13 : ZMod 3999803890129) ^ 329736 := by rw [pow_add]
          _ = 1024901144323 := by rw [factor_2_18]; decide
      have factor_2_20 : (13 : ZMod 3999803890129) ^ 1318945 = 1086142324327 := by
        calc
          (13 : ZMod 3999803890129) ^ 1318945 = (13 : ZMod 3999803890129) ^ (659472 + 659472 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 659472 * (13 : ZMod 3999803890129) ^ 659472) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1086142324327 := by rw [factor_2_19]; decide
      have factor_2_21 : (13 : ZMod 3999803890129) ^ 2637891 = 2910515996007 := by
        calc
          (13 : ZMod 3999803890129) ^ 2637891 = (13 : ZMod 3999803890129) ^ (1318945 + 1318945 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 1318945 * (13 : ZMod 3999803890129) ^ 1318945) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2910515996007 := by rw [factor_2_20]; decide
      have factor_2_22 : (13 : ZMod 3999803890129) ^ 5275783 = 279206026295 := by
        calc
          (13 : ZMod 3999803890129) ^ 5275783 = (13 : ZMod 3999803890129) ^ (2637891 + 2637891 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 2637891 * (13 : ZMod 3999803890129) ^ 2637891) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 279206026295 := by rw [factor_2_21]; decide
      have factor_2_23 : (13 : ZMod 3999803890129) ^ 10551567 = 713807959025 := by
        calc
          (13 : ZMod 3999803890129) ^ 10551567 = (13 : ZMod 3999803890129) ^ (5275783 + 5275783 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 5275783 * (13 : ZMod 3999803890129) ^ 5275783) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 713807959025 := by rw [factor_2_22]; decide
      have factor_2_24 : (13 : ZMod 3999803890129) ^ 21103135 = 3524048760851 := by
        calc
          (13 : ZMod 3999803890129) ^ 21103135 = (13 : ZMod 3999803890129) ^ (10551567 + 10551567 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 10551567 * (13 : ZMod 3999803890129) ^ 10551567) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3524048760851 := by rw [factor_2_23]; decide
      have factor_2_25 : (13 : ZMod 3999803890129) ^ 42206271 = 776993285271 := by
        calc
          (13 : ZMod 3999803890129) ^ 42206271 = (13 : ZMod 3999803890129) ^ (21103135 + 21103135 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 21103135 * (13 : ZMod 3999803890129) ^ 21103135) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 776993285271 := by rw [factor_2_24]; decide
      have factor_2_26 : (13 : ZMod 3999803890129) ^ 84412542 = 3939465092970 := by
        calc
          (13 : ZMod 3999803890129) ^ 84412542 = (13 : ZMod 3999803890129) ^ (42206271 + 42206271) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 42206271 * (13 : ZMod 3999803890129) ^ 42206271 := by rw [pow_add]
          _ = 3939465092970 := by rw [factor_2_25]; decide
      have factor_2_27 : (13 : ZMod 3999803890129) ^ 168825084 = 1102073937708 := by
        calc
          (13 : ZMod 3999803890129) ^ 168825084 = (13 : ZMod 3999803890129) ^ (84412542 + 84412542) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 84412542 * (13 : ZMod 3999803890129) ^ 84412542 := by rw [pow_add]
          _ = 1102073937708 := by rw [factor_2_26]; decide
      have factor_2_28 : (13 : ZMod 3999803890129) ^ 337650168 = 1471664699153 := by
        calc
          (13 : ZMod 3999803890129) ^ 337650168 = (13 : ZMod 3999803890129) ^ (168825084 + 168825084) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 168825084 * (13 : ZMod 3999803890129) ^ 168825084 := by rw [pow_add]
          _ = 1471664699153 := by rw [factor_2_27]; decide
      have factor_2_29 : (13 : ZMod 3999803890129) ^ 675300336 = 1175467208179 := by
        calc
          (13 : ZMod 3999803890129) ^ 675300336 = (13 : ZMod 3999803890129) ^ (337650168 + 337650168) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 337650168 * (13 : ZMod 3999803890129) ^ 337650168 := by rw [pow_add]
          _ = 1175467208179 := by rw [factor_2_28]; decide
      change (13 : ZMod 3999803890129) ^ 675300336 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (13 : ZMod 3999803890129) ^ 1 = 13 := by norm_num
      have factor_3_1 : (13 : ZMod 3999803890129) ^ 2 = 169 := by
        calc
          (13 : ZMod 3999803890129) ^ 2 = (13 : ZMod 3999803890129) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 1 * (13 : ZMod 3999803890129) ^ 1 := by rw [pow_add]
          _ = 169 := by rw [factor_3_0]; decide
      have factor_3_2 : (13 : ZMod 3999803890129) ^ 4 = 28561 := by
        calc
          (13 : ZMod 3999803890129) ^ 4 = (13 : ZMod 3999803890129) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 2 * (13 : ZMod 3999803890129) ^ 2 := by rw [pow_add]
          _ = 28561 := by rw [factor_3_1]; decide
      have factor_3_3 : (13 : ZMod 3999803890129) ^ 8 = 815730721 := by
        calc
          (13 : ZMod 3999803890129) ^ 8 = (13 : ZMod 3999803890129) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 4 * (13 : ZMod 3999803890129) ^ 4 := by rw [pow_add]
          _ = 815730721 := by rw [factor_3_2]; decide
      have factor_3_4 : (13 : ZMod 3999803890129) ^ 17 = 48160448343 := by
        calc
          (13 : ZMod 3999803890129) ^ 17 = (13 : ZMod 3999803890129) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 8 * (13 : ZMod 3999803890129) ^ 8) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 48160448343 := by rw [factor_3_3]; decide
      have factor_3_5 : (13 : ZMod 3999803890129) ^ 34 = 1894081059895 := by
        calc
          (13 : ZMod 3999803890129) ^ 34 = (13 : ZMod 3999803890129) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 17 * (13 : ZMod 3999803890129) ^ 17 := by rw [pow_add]
          _ = 1894081059895 := by rw [factor_3_4]; decide
      have factor_3_6 : (13 : ZMod 3999803890129) ^ 69 = 2333331726107 := by
        calc
          (13 : ZMod 3999803890129) ^ 69 = (13 : ZMod 3999803890129) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 34 * (13 : ZMod 3999803890129) ^ 34) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2333331726107 := by rw [factor_3_5]; decide
      have factor_3_7 : (13 : ZMod 3999803890129) ^ 138 = 1558077863224 := by
        calc
          (13 : ZMod 3999803890129) ^ 138 = (13 : ZMod 3999803890129) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 69 * (13 : ZMod 3999803890129) ^ 69 := by rw [pow_add]
          _ = 1558077863224 := by rw [factor_3_6]; decide
      have factor_3_8 : (13 : ZMod 3999803890129) ^ 277 = 3781254358114 := by
        calc
          (13 : ZMod 3999803890129) ^ 277 = (13 : ZMod 3999803890129) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 138 * (13 : ZMod 3999803890129) ^ 138) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 3781254358114 := by rw [factor_3_7]; decide
      have factor_3_9 : (13 : ZMod 3999803890129) ^ 555 = 2839942496130 := by
        calc
          (13 : ZMod 3999803890129) ^ 555 = (13 : ZMod 3999803890129) ^ (277 + 277 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 277 * (13 : ZMod 3999803890129) ^ 277) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 2839942496130 := by rw [factor_3_8]; decide
      have factor_3_10 : (13 : ZMod 3999803890129) ^ 1110 = 3081173111260 := by
        calc
          (13 : ZMod 3999803890129) ^ 1110 = (13 : ZMod 3999803890129) ^ (555 + 555) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 555 * (13 : ZMod 3999803890129) ^ 555 := by rw [pow_add]
          _ = 3081173111260 := by rw [factor_3_9]; decide
      have factor_3_11 : (13 : ZMod 3999803890129) ^ 2221 = 1710932590346 := by
        calc
          (13 : ZMod 3999803890129) ^ 2221 = (13 : ZMod 3999803890129) ^ (1110 + 1110 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 1110 * (13 : ZMod 3999803890129) ^ 1110) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1710932590346 := by rw [factor_3_10]; decide
      have factor_3_12 : (13 : ZMod 3999803890129) ^ 4442 = 910102468340 := by
        calc
          (13 : ZMod 3999803890129) ^ 4442 = (13 : ZMod 3999803890129) ^ (2221 + 2221) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 2221 * (13 : ZMod 3999803890129) ^ 2221 := by rw [pow_add]
          _ = 910102468340 := by rw [factor_3_11]; decide
      have factor_3_13 : (13 : ZMod 3999803890129) ^ 8884 = 3411922480194 := by
        calc
          (13 : ZMod 3999803890129) ^ 8884 = (13 : ZMod 3999803890129) ^ (4442 + 4442) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 4442 * (13 : ZMod 3999803890129) ^ 4442 := by rw [pow_add]
          _ = 3411922480194 := by rw [factor_3_12]; decide
      have factor_3_14 : (13 : ZMod 3999803890129) ^ 17769 = 1557895548330 := by
        calc
          (13 : ZMod 3999803890129) ^ 17769 = (13 : ZMod 3999803890129) ^ (8884 + 8884 + 1) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = ((13 : ZMod 3999803890129) ^ 8884 * (13 : ZMod 3999803890129) ^ 8884) * (13 : ZMod 3999803890129) := by rw [pow_succ, pow_add]
          _ = 1557895548330 := by rw [factor_3_13]; decide
      have factor_3_15 : (13 : ZMod 3999803890129) ^ 35538 = 2295507754133 := by
        calc
          (13 : ZMod 3999803890129) ^ 35538 = (13 : ZMod 3999803890129) ^ (17769 + 17769) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 17769 * (13 : ZMod 3999803890129) ^ 17769 := by rw [pow_add]
          _ = 2295507754133 := by rw [factor_3_14]; decide
      have factor_3_16 : (13 : ZMod 3999803890129) ^ 71076 = 1226237376440 := by
        calc
          (13 : ZMod 3999803890129) ^ 71076 = (13 : ZMod 3999803890129) ^ (35538 + 35538) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 35538 * (13 : ZMod 3999803890129) ^ 35538 := by rw [pow_add]
          _ = 1226237376440 := by rw [factor_3_15]; decide
      have factor_3_17 : (13 : ZMod 3999803890129) ^ 142152 = 2133632985435 := by
        calc
          (13 : ZMod 3999803890129) ^ 142152 = (13 : ZMod 3999803890129) ^ (71076 + 71076) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 71076 * (13 : ZMod 3999803890129) ^ 71076 := by rw [pow_add]
          _ = 2133632985435 := by rw [factor_3_16]; decide
      have factor_3_18 : (13 : ZMod 3999803890129) ^ 284304 = 3365628921609 := by
        calc
          (13 : ZMod 3999803890129) ^ 284304 = (13 : ZMod 3999803890129) ^ (142152 + 142152) :=
            congrArg (fun n : ℕ => (13 : ZMod 3999803890129) ^ n) (by norm_num)
          _ = (13 : ZMod 3999803890129) ^ 142152 * (13 : ZMod 3999803890129) ^ 142152 := by rw [pow_add]
          _ = 3365628921609 := by rw [factor_3_17]; decide
      change (13 : ZMod 3999803890129) ^ 284304 ≠ 1
      rw [factor_3_18]
      decide

#print axioms prime_lucas_3999803890129

end TotientTailPeriodKiller
end Erdos249257
