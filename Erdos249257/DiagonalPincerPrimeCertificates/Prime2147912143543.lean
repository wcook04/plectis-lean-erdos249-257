import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime264586369

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2147912143543 : Nat.Prime 2147912143543 := by
  apply lucas_primality 2147912143543 (5 : ZMod 2147912143543)
  ·
      have fermat_0 : (5 : ZMod 2147912143543) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 2147912143543) ^ 3 = 125 := by
        calc
          (5 : ZMod 2147912143543) ^ 3 = (5 : ZMod 2147912143543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1 * (5 : ZMod 2147912143543) ^ 1) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 2147912143543) ^ 7 = 78125 := by
        calc
          (5 : ZMod 2147912143543) ^ 7 = (5 : ZMod 2147912143543) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 3 * (5 : ZMod 2147912143543) ^ 3) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 2147912143543) ^ 15 = 30517578125 := by
        calc
          (5 : ZMod 2147912143543) ^ 15 = (5 : ZMod 2147912143543) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 7 * (5 : ZMod 2147912143543) ^ 7) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 30517578125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 2147912143543) ^ 31 = 767190088902 := by
        calc
          (5 : ZMod 2147912143543) ^ 31 = (5 : ZMod 2147912143543) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 15 * (5 : ZMod 2147912143543) ^ 15) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 767190088902 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 2147912143543) ^ 62 = 466544809909 := by
        calc
          (5 : ZMod 2147912143543) ^ 62 = (5 : ZMod 2147912143543) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 31 * (5 : ZMod 2147912143543) ^ 31 := by rw [pow_add]
          _ = 466544809909 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 2147912143543) ^ 125 = 124087137489 := by
        calc
          (5 : ZMod 2147912143543) ^ 125 = (5 : ZMod 2147912143543) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 62 * (5 : ZMod 2147912143543) ^ 62) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 124087137489 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 2147912143543) ^ 250 = 861054901337 := by
        calc
          (5 : ZMod 2147912143543) ^ 250 = (5 : ZMod 2147912143543) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 125 * (5 : ZMod 2147912143543) ^ 125 := by rw [pow_add]
          _ = 861054901337 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 2147912143543) ^ 500 = 1850330448421 := by
        calc
          (5 : ZMod 2147912143543) ^ 500 = (5 : ZMod 2147912143543) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 250 * (5 : ZMod 2147912143543) ^ 250 := by rw [pow_add]
          _ = 1850330448421 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 2147912143543) ^ 1000 = 1672240783611 := by
        calc
          (5 : ZMod 2147912143543) ^ 1000 = (5 : ZMod 2147912143543) ^ (500 + 500) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 500 * (5 : ZMod 2147912143543) ^ 500 := by rw [pow_add]
          _ = 1672240783611 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 2147912143543) ^ 2000 = 2063597610659 := by
        calc
          (5 : ZMod 2147912143543) ^ 2000 = (5 : ZMod 2147912143543) ^ (1000 + 1000) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1000 * (5 : ZMod 2147912143543) ^ 1000 := by rw [pow_add]
          _ = 2063597610659 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 2147912143543) ^ 4000 = 668238080375 := by
        calc
          (5 : ZMod 2147912143543) ^ 4000 = (5 : ZMod 2147912143543) ^ (2000 + 2000) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 2000 * (5 : ZMod 2147912143543) ^ 2000 := by rw [pow_add]
          _ = 668238080375 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 2147912143543) ^ 8001 = 1180410325727 := by
        calc
          (5 : ZMod 2147912143543) ^ 8001 = (5 : ZMod 2147912143543) ^ (4000 + 4000 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 4000 * (5 : ZMod 2147912143543) ^ 4000) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1180410325727 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 2147912143543) ^ 16003 = 616943923674 := by
        calc
          (5 : ZMod 2147912143543) ^ 16003 = (5 : ZMod 2147912143543) ^ (8001 + 8001 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 8001 * (5 : ZMod 2147912143543) ^ 8001) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 616943923674 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 2147912143543) ^ 32006 = 1914536969868 := by
        calc
          (5 : ZMod 2147912143543) ^ 32006 = (5 : ZMod 2147912143543) ^ (16003 + 16003) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 16003 * (5 : ZMod 2147912143543) ^ 16003 := by rw [pow_add]
          _ = 1914536969868 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 2147912143543) ^ 64012 = 2076125260761 := by
        calc
          (5 : ZMod 2147912143543) ^ 64012 = (5 : ZMod 2147912143543) ^ (32006 + 32006) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 32006 * (5 : ZMod 2147912143543) ^ 32006 := by rw [pow_add]
          _ = 2076125260761 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 2147912143543) ^ 128025 = 1529231861341 := by
        calc
          (5 : ZMod 2147912143543) ^ 128025 = (5 : ZMod 2147912143543) ^ (64012 + 64012 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 64012 * (5 : ZMod 2147912143543) ^ 64012) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1529231861341 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 2147912143543) ^ 256051 = 2001341041725 := by
        calc
          (5 : ZMod 2147912143543) ^ 256051 = (5 : ZMod 2147912143543) ^ (128025 + 128025 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 128025 * (5 : ZMod 2147912143543) ^ 128025) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 2001341041725 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 2147912143543) ^ 512102 = 13088506459 := by
        calc
          (5 : ZMod 2147912143543) ^ 512102 = (5 : ZMod 2147912143543) ^ (256051 + 256051) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 256051 * (5 : ZMod 2147912143543) ^ 256051 := by rw [pow_add]
          _ = 13088506459 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 2147912143543) ^ 1024204 = 123789172273 := by
        calc
          (5 : ZMod 2147912143543) ^ 1024204 = (5 : ZMod 2147912143543) ^ (512102 + 512102) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 512102 * (5 : ZMod 2147912143543) ^ 512102 := by rw [pow_add]
          _ = 123789172273 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 2147912143543) ^ 2048408 = 2048538821001 := by
        calc
          (5 : ZMod 2147912143543) ^ 2048408 = (5 : ZMod 2147912143543) ^ (1024204 + 1024204) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1024204 * (5 : ZMod 2147912143543) ^ 1024204 := by rw [pow_add]
          _ = 2048538821001 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 2147912143543) ^ 4096817 = 1046376614003 := by
        calc
          (5 : ZMod 2147912143543) ^ 4096817 = (5 : ZMod 2147912143543) ^ (2048408 + 2048408 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2048408 * (5 : ZMod 2147912143543) ^ 2048408) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1046376614003 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 2147912143543) ^ 8193634 = 1042769799985 := by
        calc
          (5 : ZMod 2147912143543) ^ 8193634 = (5 : ZMod 2147912143543) ^ (4096817 + 4096817) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 4096817 * (5 : ZMod 2147912143543) ^ 4096817 := by rw [pow_add]
          _ = 1042769799985 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 2147912143543) ^ 16387269 = 761039858999 := by
        calc
          (5 : ZMod 2147912143543) ^ 16387269 = (5 : ZMod 2147912143543) ^ (8193634 + 8193634 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 8193634 * (5 : ZMod 2147912143543) ^ 8193634) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 761039858999 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 2147912143543) ^ 32774538 = 3670365685 := by
        calc
          (5 : ZMod 2147912143543) ^ 32774538 = (5 : ZMod 2147912143543) ^ (16387269 + 16387269) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 16387269 * (5 : ZMod 2147912143543) ^ 16387269 := by rw [pow_add]
          _ = 3670365685 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 2147912143543) ^ 65549076 = 1728316005176 := by
        calc
          (5 : ZMod 2147912143543) ^ 65549076 = (5 : ZMod 2147912143543) ^ (32774538 + 32774538) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 32774538 * (5 : ZMod 2147912143543) ^ 32774538 := by rw [pow_add]
          _ = 1728316005176 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 2147912143543) ^ 131098153 = 1956999988648 := by
        calc
          (5 : ZMod 2147912143543) ^ 131098153 = (5 : ZMod 2147912143543) ^ (65549076 + 65549076 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 65549076 * (5 : ZMod 2147912143543) ^ 65549076) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1956999988648 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 2147912143543) ^ 262196306 = 1791397770246 := by
        calc
          (5 : ZMod 2147912143543) ^ 262196306 = (5 : ZMod 2147912143543) ^ (131098153 + 131098153) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 131098153 * (5 : ZMod 2147912143543) ^ 131098153 := by rw [pow_add]
          _ = 1791397770246 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 2147912143543) ^ 524392613 = 85340489433 := by
        calc
          (5 : ZMod 2147912143543) ^ 524392613 = (5 : ZMod 2147912143543) ^ (262196306 + 262196306 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 262196306 * (5 : ZMod 2147912143543) ^ 262196306) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 85340489433 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 2147912143543) ^ 1048785226 = 880283256948 := by
        calc
          (5 : ZMod 2147912143543) ^ 1048785226 = (5 : ZMod 2147912143543) ^ (524392613 + 524392613) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 524392613 * (5 : ZMod 2147912143543) ^ 524392613 := by rw [pow_add]
          _ = 880283256948 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 2147912143543) ^ 2097570452 = 1453846982483 := by
        calc
          (5 : ZMod 2147912143543) ^ 2097570452 = (5 : ZMod 2147912143543) ^ (1048785226 + 1048785226) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1048785226 * (5 : ZMod 2147912143543) ^ 1048785226 := by rw [pow_add]
          _ = 1453846982483 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 2147912143543) ^ 4195140905 = 1044024153078 := by
        calc
          (5 : ZMod 2147912143543) ^ 4195140905 = (5 : ZMod 2147912143543) ^ (2097570452 + 2097570452 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2097570452 * (5 : ZMod 2147912143543) ^ 2097570452) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1044024153078 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 2147912143543) ^ 8390281810 = 1174648593811 := by
        calc
          (5 : ZMod 2147912143543) ^ 8390281810 = (5 : ZMod 2147912143543) ^ (4195140905 + 4195140905) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 4195140905 * (5 : ZMod 2147912143543) ^ 4195140905 := by rw [pow_add]
          _ = 1174648593811 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 2147912143543) ^ 16780563621 = 237008086443 := by
        calc
          (5 : ZMod 2147912143543) ^ 16780563621 = (5 : ZMod 2147912143543) ^ (8390281810 + 8390281810 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 8390281810 * (5 : ZMod 2147912143543) ^ 8390281810) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 237008086443 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 2147912143543) ^ 33561127242 = 651674593695 := by
        calc
          (5 : ZMod 2147912143543) ^ 33561127242 = (5 : ZMod 2147912143543) ^ (16780563621 + 16780563621) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 16780563621 * (5 : ZMod 2147912143543) ^ 16780563621 := by rw [pow_add]
          _ = 651674593695 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 2147912143543) ^ 67122254485 = 219494480168 := by
        calc
          (5 : ZMod 2147912143543) ^ 67122254485 = (5 : ZMod 2147912143543) ^ (33561127242 + 33561127242 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 33561127242 * (5 : ZMod 2147912143543) ^ 33561127242) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 219494480168 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 2147912143543) ^ 134244508971 = 67195170362 := by
        calc
          (5 : ZMod 2147912143543) ^ 134244508971 = (5 : ZMod 2147912143543) ^ (67122254485 + 67122254485 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 67122254485 * (5 : ZMod 2147912143543) ^ 67122254485) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 67195170362 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 2147912143543) ^ 268489017942 = 527092218734 := by
        calc
          (5 : ZMod 2147912143543) ^ 268489017942 = (5 : ZMod 2147912143543) ^ (134244508971 + 134244508971) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 134244508971 * (5 : ZMod 2147912143543) ^ 134244508971 := by rw [pow_add]
          _ = 527092218734 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 2147912143543) ^ 536978035885 = 907190235990 := by
        calc
          (5 : ZMod 2147912143543) ^ 536978035885 = (5 : ZMod 2147912143543) ^ (268489017942 + 268489017942 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 268489017942 * (5 : ZMod 2147912143543) ^ 268489017942) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 907190235990 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 2147912143543) ^ 1073956071771 = 2147912143542 := by
        calc
          (5 : ZMod 2147912143543) ^ 1073956071771 = (5 : ZMod 2147912143543) ^ (536978035885 + 536978035885 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 536978035885 * (5 : ZMod 2147912143543) ^ 536978035885) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 2147912143542 := by rw [fermat_38]; decide
      have fermat_40 : (5 : ZMod 2147912143543) ^ 2147912143542 = 1 := by
        calc
          (5 : ZMod 2147912143543) ^ 2147912143542 = (5 : ZMod 2147912143543) ^ (1073956071771 + 1073956071771) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1073956071771 * (5 : ZMod 2147912143543) ^ 1073956071771 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (41, 1), (264586369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (41, 1), (264586369, 1)] : List FactorBlock).map factorBlockValue).prod = 2147912143543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_264586369) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 2147912143543) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 2147912143543) ^ 3 = 125 := by
        calc
          (5 : ZMod 2147912143543) ^ 3 = (5 : ZMod 2147912143543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1 * (5 : ZMod 2147912143543) ^ 1) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 2147912143543) ^ 7 = 78125 := by
        calc
          (5 : ZMod 2147912143543) ^ 7 = (5 : ZMod 2147912143543) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 3 * (5 : ZMod 2147912143543) ^ 3) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 2147912143543) ^ 15 = 30517578125 := by
        calc
          (5 : ZMod 2147912143543) ^ 15 = (5 : ZMod 2147912143543) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 7 * (5 : ZMod 2147912143543) ^ 7) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 30517578125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 2147912143543) ^ 31 = 767190088902 := by
        calc
          (5 : ZMod 2147912143543) ^ 31 = (5 : ZMod 2147912143543) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 15 * (5 : ZMod 2147912143543) ^ 15) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 767190088902 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 2147912143543) ^ 62 = 466544809909 := by
        calc
          (5 : ZMod 2147912143543) ^ 62 = (5 : ZMod 2147912143543) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 31 * (5 : ZMod 2147912143543) ^ 31 := by rw [pow_add]
          _ = 466544809909 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 2147912143543) ^ 125 = 124087137489 := by
        calc
          (5 : ZMod 2147912143543) ^ 125 = (5 : ZMod 2147912143543) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 62 * (5 : ZMod 2147912143543) ^ 62) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 124087137489 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 2147912143543) ^ 250 = 861054901337 := by
        calc
          (5 : ZMod 2147912143543) ^ 250 = (5 : ZMod 2147912143543) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 125 * (5 : ZMod 2147912143543) ^ 125 := by rw [pow_add]
          _ = 861054901337 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 2147912143543) ^ 500 = 1850330448421 := by
        calc
          (5 : ZMod 2147912143543) ^ 500 = (5 : ZMod 2147912143543) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 250 * (5 : ZMod 2147912143543) ^ 250 := by rw [pow_add]
          _ = 1850330448421 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 2147912143543) ^ 1000 = 1672240783611 := by
        calc
          (5 : ZMod 2147912143543) ^ 1000 = (5 : ZMod 2147912143543) ^ (500 + 500) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 500 * (5 : ZMod 2147912143543) ^ 500 := by rw [pow_add]
          _ = 1672240783611 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 2147912143543) ^ 2000 = 2063597610659 := by
        calc
          (5 : ZMod 2147912143543) ^ 2000 = (5 : ZMod 2147912143543) ^ (1000 + 1000) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1000 * (5 : ZMod 2147912143543) ^ 1000 := by rw [pow_add]
          _ = 2063597610659 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 2147912143543) ^ 4000 = 668238080375 := by
        calc
          (5 : ZMod 2147912143543) ^ 4000 = (5 : ZMod 2147912143543) ^ (2000 + 2000) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 2000 * (5 : ZMod 2147912143543) ^ 2000 := by rw [pow_add]
          _ = 668238080375 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 2147912143543) ^ 8001 = 1180410325727 := by
        calc
          (5 : ZMod 2147912143543) ^ 8001 = (5 : ZMod 2147912143543) ^ (4000 + 4000 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 4000 * (5 : ZMod 2147912143543) ^ 4000) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1180410325727 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 2147912143543) ^ 16003 = 616943923674 := by
        calc
          (5 : ZMod 2147912143543) ^ 16003 = (5 : ZMod 2147912143543) ^ (8001 + 8001 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 8001 * (5 : ZMod 2147912143543) ^ 8001) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 616943923674 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 2147912143543) ^ 32006 = 1914536969868 := by
        calc
          (5 : ZMod 2147912143543) ^ 32006 = (5 : ZMod 2147912143543) ^ (16003 + 16003) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 16003 * (5 : ZMod 2147912143543) ^ 16003 := by rw [pow_add]
          _ = 1914536969868 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 2147912143543) ^ 64012 = 2076125260761 := by
        calc
          (5 : ZMod 2147912143543) ^ 64012 = (5 : ZMod 2147912143543) ^ (32006 + 32006) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 32006 * (5 : ZMod 2147912143543) ^ 32006 := by rw [pow_add]
          _ = 2076125260761 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 2147912143543) ^ 128025 = 1529231861341 := by
        calc
          (5 : ZMod 2147912143543) ^ 128025 = (5 : ZMod 2147912143543) ^ (64012 + 64012 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 64012 * (5 : ZMod 2147912143543) ^ 64012) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1529231861341 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 2147912143543) ^ 256051 = 2001341041725 := by
        calc
          (5 : ZMod 2147912143543) ^ 256051 = (5 : ZMod 2147912143543) ^ (128025 + 128025 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 128025 * (5 : ZMod 2147912143543) ^ 128025) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 2001341041725 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 2147912143543) ^ 512102 = 13088506459 := by
        calc
          (5 : ZMod 2147912143543) ^ 512102 = (5 : ZMod 2147912143543) ^ (256051 + 256051) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 256051 * (5 : ZMod 2147912143543) ^ 256051 := by rw [pow_add]
          _ = 13088506459 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 2147912143543) ^ 1024204 = 123789172273 := by
        calc
          (5 : ZMod 2147912143543) ^ 1024204 = (5 : ZMod 2147912143543) ^ (512102 + 512102) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 512102 * (5 : ZMod 2147912143543) ^ 512102 := by rw [pow_add]
          _ = 123789172273 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 2147912143543) ^ 2048408 = 2048538821001 := by
        calc
          (5 : ZMod 2147912143543) ^ 2048408 = (5 : ZMod 2147912143543) ^ (1024204 + 1024204) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1024204 * (5 : ZMod 2147912143543) ^ 1024204 := by rw [pow_add]
          _ = 2048538821001 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 2147912143543) ^ 4096817 = 1046376614003 := by
        calc
          (5 : ZMod 2147912143543) ^ 4096817 = (5 : ZMod 2147912143543) ^ (2048408 + 2048408 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2048408 * (5 : ZMod 2147912143543) ^ 2048408) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1046376614003 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 2147912143543) ^ 8193634 = 1042769799985 := by
        calc
          (5 : ZMod 2147912143543) ^ 8193634 = (5 : ZMod 2147912143543) ^ (4096817 + 4096817) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 4096817 * (5 : ZMod 2147912143543) ^ 4096817 := by rw [pow_add]
          _ = 1042769799985 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 2147912143543) ^ 16387269 = 761039858999 := by
        calc
          (5 : ZMod 2147912143543) ^ 16387269 = (5 : ZMod 2147912143543) ^ (8193634 + 8193634 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 8193634 * (5 : ZMod 2147912143543) ^ 8193634) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 761039858999 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 2147912143543) ^ 32774538 = 3670365685 := by
        calc
          (5 : ZMod 2147912143543) ^ 32774538 = (5 : ZMod 2147912143543) ^ (16387269 + 16387269) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 16387269 * (5 : ZMod 2147912143543) ^ 16387269 := by rw [pow_add]
          _ = 3670365685 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 2147912143543) ^ 65549076 = 1728316005176 := by
        calc
          (5 : ZMod 2147912143543) ^ 65549076 = (5 : ZMod 2147912143543) ^ (32774538 + 32774538) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 32774538 * (5 : ZMod 2147912143543) ^ 32774538 := by rw [pow_add]
          _ = 1728316005176 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 2147912143543) ^ 131098153 = 1956999988648 := by
        calc
          (5 : ZMod 2147912143543) ^ 131098153 = (5 : ZMod 2147912143543) ^ (65549076 + 65549076 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 65549076 * (5 : ZMod 2147912143543) ^ 65549076) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1956999988648 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 2147912143543) ^ 262196306 = 1791397770246 := by
        calc
          (5 : ZMod 2147912143543) ^ 262196306 = (5 : ZMod 2147912143543) ^ (131098153 + 131098153) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 131098153 * (5 : ZMod 2147912143543) ^ 131098153 := by rw [pow_add]
          _ = 1791397770246 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 2147912143543) ^ 524392613 = 85340489433 := by
        calc
          (5 : ZMod 2147912143543) ^ 524392613 = (5 : ZMod 2147912143543) ^ (262196306 + 262196306 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 262196306 * (5 : ZMod 2147912143543) ^ 262196306) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 85340489433 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 2147912143543) ^ 1048785226 = 880283256948 := by
        calc
          (5 : ZMod 2147912143543) ^ 1048785226 = (5 : ZMod 2147912143543) ^ (524392613 + 524392613) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 524392613 * (5 : ZMod 2147912143543) ^ 524392613 := by rw [pow_add]
          _ = 880283256948 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 2147912143543) ^ 2097570452 = 1453846982483 := by
        calc
          (5 : ZMod 2147912143543) ^ 2097570452 = (5 : ZMod 2147912143543) ^ (1048785226 + 1048785226) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1048785226 * (5 : ZMod 2147912143543) ^ 1048785226 := by rw [pow_add]
          _ = 1453846982483 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 2147912143543) ^ 4195140905 = 1044024153078 := by
        calc
          (5 : ZMod 2147912143543) ^ 4195140905 = (5 : ZMod 2147912143543) ^ (2097570452 + 2097570452 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2097570452 * (5 : ZMod 2147912143543) ^ 2097570452) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1044024153078 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 2147912143543) ^ 8390281810 = 1174648593811 := by
        calc
          (5 : ZMod 2147912143543) ^ 8390281810 = (5 : ZMod 2147912143543) ^ (4195140905 + 4195140905) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 4195140905 * (5 : ZMod 2147912143543) ^ 4195140905 := by rw [pow_add]
          _ = 1174648593811 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 2147912143543) ^ 16780563621 = 237008086443 := by
        calc
          (5 : ZMod 2147912143543) ^ 16780563621 = (5 : ZMod 2147912143543) ^ (8390281810 + 8390281810 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 8390281810 * (5 : ZMod 2147912143543) ^ 8390281810) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 237008086443 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 2147912143543) ^ 33561127242 = 651674593695 := by
        calc
          (5 : ZMod 2147912143543) ^ 33561127242 = (5 : ZMod 2147912143543) ^ (16780563621 + 16780563621) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 16780563621 * (5 : ZMod 2147912143543) ^ 16780563621 := by rw [pow_add]
          _ = 651674593695 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 2147912143543) ^ 67122254485 = 219494480168 := by
        calc
          (5 : ZMod 2147912143543) ^ 67122254485 = (5 : ZMod 2147912143543) ^ (33561127242 + 33561127242 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 33561127242 * (5 : ZMod 2147912143543) ^ 33561127242) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 219494480168 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 2147912143543) ^ 134244508971 = 67195170362 := by
        calc
          (5 : ZMod 2147912143543) ^ 134244508971 = (5 : ZMod 2147912143543) ^ (67122254485 + 67122254485 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 67122254485 * (5 : ZMod 2147912143543) ^ 67122254485) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 67195170362 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 2147912143543) ^ 268489017942 = 527092218734 := by
        calc
          (5 : ZMod 2147912143543) ^ 268489017942 = (5 : ZMod 2147912143543) ^ (134244508971 + 134244508971) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 134244508971 * (5 : ZMod 2147912143543) ^ 134244508971 := by rw [pow_add]
          _ = 527092218734 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 2147912143543) ^ 536978035885 = 907190235990 := by
        calc
          (5 : ZMod 2147912143543) ^ 536978035885 = (5 : ZMod 2147912143543) ^ (268489017942 + 268489017942 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 268489017942 * (5 : ZMod 2147912143543) ^ 268489017942) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 907190235990 := by rw [factor_0_37]; decide
      have factor_0_39 : (5 : ZMod 2147912143543) ^ 1073956071771 = 2147912143542 := by
        calc
          (5 : ZMod 2147912143543) ^ 1073956071771 = (5 : ZMod 2147912143543) ^ (536978035885 + 536978035885 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 536978035885 * (5 : ZMod 2147912143543) ^ 536978035885) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 2147912143542 := by rw [factor_0_38]; decide
      change (5 : ZMod 2147912143543) ^ 1073956071771 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (5 : ZMod 2147912143543) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 2147912143543) ^ 2 = 25 := by
        calc
          (5 : ZMod 2147912143543) ^ 2 = (5 : ZMod 2147912143543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1 * (5 : ZMod 2147912143543) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 2147912143543) ^ 5 = 3125 := by
        calc
          (5 : ZMod 2147912143543) ^ 5 = (5 : ZMod 2147912143543) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2 * (5 : ZMod 2147912143543) ^ 2) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 2147912143543) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 2147912143543) ^ 10 = (5 : ZMod 2147912143543) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 5 * (5 : ZMod 2147912143543) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 2147912143543) ^ 20 = 859297324733 := by
        calc
          (5 : ZMod 2147912143543) ^ 20 = (5 : ZMod 2147912143543) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 10 * (5 : ZMod 2147912143543) ^ 10 := by rw [pow_add]
          _ = 859297324733 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 2147912143543) ^ 41 = 1322284126310 := by
        calc
          (5 : ZMod 2147912143543) ^ 41 = (5 : ZMod 2147912143543) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 20 * (5 : ZMod 2147912143543) ^ 20) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1322284126310 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 2147912143543) ^ 83 = 1367257852576 := by
        calc
          (5 : ZMod 2147912143543) ^ 83 = (5 : ZMod 2147912143543) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 41 * (5 : ZMod 2147912143543) ^ 41) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1367257852576 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 2147912143543) ^ 166 = 1744206351229 := by
        calc
          (5 : ZMod 2147912143543) ^ 166 = (5 : ZMod 2147912143543) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 83 * (5 : ZMod 2147912143543) ^ 83 := by rw [pow_add]
          _ = 1744206351229 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 2147912143543) ^ 333 = 1284223797035 := by
        calc
          (5 : ZMod 2147912143543) ^ 333 = (5 : ZMod 2147912143543) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 166 * (5 : ZMod 2147912143543) ^ 166) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1284223797035 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 2147912143543) ^ 666 = 658679291910 := by
        calc
          (5 : ZMod 2147912143543) ^ 666 = (5 : ZMod 2147912143543) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 333 * (5 : ZMod 2147912143543) ^ 333 := by rw [pow_add]
          _ = 658679291910 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 2147912143543) ^ 1333 = 452259994830 := by
        calc
          (5 : ZMod 2147912143543) ^ 1333 = (5 : ZMod 2147912143543) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 666 * (5 : ZMod 2147912143543) ^ 666) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 452259994830 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 2147912143543) ^ 2667 = 1185388183800 := by
        calc
          (5 : ZMod 2147912143543) ^ 2667 = (5 : ZMod 2147912143543) ^ (1333 + 1333 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1333 * (5 : ZMod 2147912143543) ^ 1333) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1185388183800 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 2147912143543) ^ 5334 = 2042633803252 := by
        calc
          (5 : ZMod 2147912143543) ^ 5334 = (5 : ZMod 2147912143543) ^ (2667 + 2667) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 2667 * (5 : ZMod 2147912143543) ^ 2667 := by rw [pow_add]
          _ = 2042633803252 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 2147912143543) ^ 10668 = 217665301834 := by
        calc
          (5 : ZMod 2147912143543) ^ 10668 = (5 : ZMod 2147912143543) ^ (5334 + 5334) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 5334 * (5 : ZMod 2147912143543) ^ 5334 := by rw [pow_add]
          _ = 217665301834 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 2147912143543) ^ 21337 = 573814991221 := by
        calc
          (5 : ZMod 2147912143543) ^ 21337 = (5 : ZMod 2147912143543) ^ (10668 + 10668 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 10668 * (5 : ZMod 2147912143543) ^ 10668) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 573814991221 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 2147912143543) ^ 42675 = 583430818921 := by
        calc
          (5 : ZMod 2147912143543) ^ 42675 = (5 : ZMod 2147912143543) ^ (21337 + 21337 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 21337 * (5 : ZMod 2147912143543) ^ 21337) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 583430818921 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 2147912143543) ^ 85350 = 497314320643 := by
        calc
          (5 : ZMod 2147912143543) ^ 85350 = (5 : ZMod 2147912143543) ^ (42675 + 42675) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 42675 * (5 : ZMod 2147912143543) ^ 42675 := by rw [pow_add]
          _ = 497314320643 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 2147912143543) ^ 170700 = 1791120344829 := by
        calc
          (5 : ZMod 2147912143543) ^ 170700 = (5 : ZMod 2147912143543) ^ (85350 + 85350) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 85350 * (5 : ZMod 2147912143543) ^ 85350 := by rw [pow_add]
          _ = 1791120344829 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 2147912143543) ^ 341401 = 1641165464550 := by
        calc
          (5 : ZMod 2147912143543) ^ 341401 = (5 : ZMod 2147912143543) ^ (170700 + 170700 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 170700 * (5 : ZMod 2147912143543) ^ 170700) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1641165464550 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 2147912143543) ^ 682802 = 152905051057 := by
        calc
          (5 : ZMod 2147912143543) ^ 682802 = (5 : ZMod 2147912143543) ^ (341401 + 341401) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 341401 * (5 : ZMod 2147912143543) ^ 341401 := by rw [pow_add]
          _ = 152905051057 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 2147912143543) ^ 1365605 = 274555747834 := by
        calc
          (5 : ZMod 2147912143543) ^ 1365605 = (5 : ZMod 2147912143543) ^ (682802 + 682802 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 682802 * (5 : ZMod 2147912143543) ^ 682802) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 274555747834 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 2147912143543) ^ 2731211 = 1728269724681 := by
        calc
          (5 : ZMod 2147912143543) ^ 2731211 = (5 : ZMod 2147912143543) ^ (1365605 + 1365605 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1365605 * (5 : ZMod 2147912143543) ^ 1365605) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1728269724681 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 2147912143543) ^ 5462423 = 655502037872 := by
        calc
          (5 : ZMod 2147912143543) ^ 5462423 = (5 : ZMod 2147912143543) ^ (2731211 + 2731211 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2731211 * (5 : ZMod 2147912143543) ^ 2731211) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 655502037872 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 2147912143543) ^ 10924846 = 54902829307 := by
        calc
          (5 : ZMod 2147912143543) ^ 10924846 = (5 : ZMod 2147912143543) ^ (5462423 + 5462423) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 5462423 * (5 : ZMod 2147912143543) ^ 5462423 := by rw [pow_add]
          _ = 54902829307 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 2147912143543) ^ 21849692 = 934338672646 := by
        calc
          (5 : ZMod 2147912143543) ^ 21849692 = (5 : ZMod 2147912143543) ^ (10924846 + 10924846) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 10924846 * (5 : ZMod 2147912143543) ^ 10924846 := by rw [pow_add]
          _ = 934338672646 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 2147912143543) ^ 43699384 = 1285001324024 := by
        calc
          (5 : ZMod 2147912143543) ^ 43699384 = (5 : ZMod 2147912143543) ^ (21849692 + 21849692) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 21849692 * (5 : ZMod 2147912143543) ^ 21849692 := by rw [pow_add]
          _ = 1285001324024 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 2147912143543) ^ 87398768 = 46524508045 := by
        calc
          (5 : ZMod 2147912143543) ^ 87398768 = (5 : ZMod 2147912143543) ^ (43699384 + 43699384) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 43699384 * (5 : ZMod 2147912143543) ^ 43699384 := by rw [pow_add]
          _ = 46524508045 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 2147912143543) ^ 174797537 = 1149026615812 := by
        calc
          (5 : ZMod 2147912143543) ^ 174797537 = (5 : ZMod 2147912143543) ^ (87398768 + 87398768 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 87398768 * (5 : ZMod 2147912143543) ^ 87398768) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1149026615812 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 2147912143543) ^ 349595075 = 452148767790 := by
        calc
          (5 : ZMod 2147912143543) ^ 349595075 = (5 : ZMod 2147912143543) ^ (174797537 + 174797537 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 174797537 * (5 : ZMod 2147912143543) ^ 174797537) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 452148767790 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 2147912143543) ^ 699190150 = 92348631291 := by
        calc
          (5 : ZMod 2147912143543) ^ 699190150 = (5 : ZMod 2147912143543) ^ (349595075 + 349595075) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 349595075 * (5 : ZMod 2147912143543) ^ 349595075 := by rw [pow_add]
          _ = 92348631291 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 2147912143543) ^ 1398380301 = 1755081681405 := by
        calc
          (5 : ZMod 2147912143543) ^ 1398380301 = (5 : ZMod 2147912143543) ^ (699190150 + 699190150 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 699190150 * (5 : ZMod 2147912143543) ^ 699190150) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1755081681405 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 2147912143543) ^ 2796760603 = 1581734427549 := by
        calc
          (5 : ZMod 2147912143543) ^ 2796760603 = (5 : ZMod 2147912143543) ^ (1398380301 + 1398380301 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1398380301 * (5 : ZMod 2147912143543) ^ 1398380301) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1581734427549 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 2147912143543) ^ 5593521207 = 473813759151 := by
        calc
          (5 : ZMod 2147912143543) ^ 5593521207 = (5 : ZMod 2147912143543) ^ (2796760603 + 2796760603 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2796760603 * (5 : ZMod 2147912143543) ^ 2796760603) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 473813759151 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 2147912143543) ^ 11187042414 = 1810162392794 := by
        calc
          (5 : ZMod 2147912143543) ^ 11187042414 = (5 : ZMod 2147912143543) ^ (5593521207 + 5593521207) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 5593521207 * (5 : ZMod 2147912143543) ^ 5593521207 := by rw [pow_add]
          _ = 1810162392794 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 2147912143543) ^ 22374084828 = 56264478247 := by
        calc
          (5 : ZMod 2147912143543) ^ 22374084828 = (5 : ZMod 2147912143543) ^ (11187042414 + 11187042414) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 11187042414 * (5 : ZMod 2147912143543) ^ 11187042414 := by rw [pow_add]
          _ = 56264478247 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 2147912143543) ^ 44748169657 = 359600836943 := by
        calc
          (5 : ZMod 2147912143543) ^ 44748169657 = (5 : ZMod 2147912143543) ^ (22374084828 + 22374084828 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 22374084828 * (5 : ZMod 2147912143543) ^ 22374084828) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 359600836943 := by rw [factor_1_34]; decide
      have factor_1_36 : (5 : ZMod 2147912143543) ^ 89496339314 = 1517716532211 := by
        calc
          (5 : ZMod 2147912143543) ^ 89496339314 = (5 : ZMod 2147912143543) ^ (44748169657 + 44748169657) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 44748169657 * (5 : ZMod 2147912143543) ^ 44748169657 := by rw [pow_add]
          _ = 1517716532211 := by rw [factor_1_35]; decide
      have factor_1_37 : (5 : ZMod 2147912143543) ^ 178992678628 = 1574560253303 := by
        calc
          (5 : ZMod 2147912143543) ^ 178992678628 = (5 : ZMod 2147912143543) ^ (89496339314 + 89496339314) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 89496339314 * (5 : ZMod 2147912143543) ^ 89496339314 := by rw [pow_add]
          _ = 1574560253303 := by rw [factor_1_36]; decide
      have factor_1_38 : (5 : ZMod 2147912143543) ^ 357985357257 = 718169547059 := by
        calc
          (5 : ZMod 2147912143543) ^ 357985357257 = (5 : ZMod 2147912143543) ^ (178992678628 + 178992678628 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 178992678628 * (5 : ZMod 2147912143543) ^ 178992678628) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 718169547059 := by rw [factor_1_37]; decide
      have factor_1_39 : (5 : ZMod 2147912143543) ^ 715970714514 = 718169547058 := by
        calc
          (5 : ZMod 2147912143543) ^ 715970714514 = (5 : ZMod 2147912143543) ^ (357985357257 + 357985357257) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 357985357257 * (5 : ZMod 2147912143543) ^ 357985357257 := by rw [pow_add]
          _ = 718169547058 := by rw [factor_1_38]; decide
      change (5 : ZMod 2147912143543) ^ 715970714514 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (5 : ZMod 2147912143543) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 2147912143543) ^ 2 = 25 := by
        calc
          (5 : ZMod 2147912143543) ^ 2 = (5 : ZMod 2147912143543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1 * (5 : ZMod 2147912143543) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 2147912143543) ^ 5 = 3125 := by
        calc
          (5 : ZMod 2147912143543) ^ 5 = (5 : ZMod 2147912143543) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2 * (5 : ZMod 2147912143543) ^ 2) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 2147912143543) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 2147912143543) ^ 11 = (5 : ZMod 2147912143543) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 5 * (5 : ZMod 2147912143543) ^ 5) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 2147912143543) ^ 22 = 3311682895 := by
        calc
          (5 : ZMod 2147912143543) ^ 22 = (5 : ZMod 2147912143543) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 11 * (5 : ZMod 2147912143543) ^ 11 := by rw [pow_add]
          _ = 3311682895 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 2147912143543) ^ 45 = 1629315823238 := by
        calc
          (5 : ZMod 2147912143543) ^ 45 = (5 : ZMod 2147912143543) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 22 * (5 : ZMod 2147912143543) ^ 22) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1629315823238 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 2147912143543) ^ 90 = 1348834106610 := by
        calc
          (5 : ZMod 2147912143543) ^ 90 = (5 : ZMod 2147912143543) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 45 * (5 : ZMod 2147912143543) ^ 45 := by rw [pow_add]
          _ = 1348834106610 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 2147912143543) ^ 181 = 1236893070445 := by
        calc
          (5 : ZMod 2147912143543) ^ 181 = (5 : ZMod 2147912143543) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 90 * (5 : ZMod 2147912143543) ^ 90) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1236893070445 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 2147912143543) ^ 363 = 1234580600772 := by
        calc
          (5 : ZMod 2147912143543) ^ 363 = (5 : ZMod 2147912143543) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 181 * (5 : ZMod 2147912143543) ^ 181) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1234580600772 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 2147912143543) ^ 727 = 1690599191360 := by
        calc
          (5 : ZMod 2147912143543) ^ 727 = (5 : ZMod 2147912143543) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 363 * (5 : ZMod 2147912143543) ^ 363) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1690599191360 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 2147912143543) ^ 1454 = 220817464573 := by
        calc
          (5 : ZMod 2147912143543) ^ 1454 = (5 : ZMod 2147912143543) ^ (727 + 727) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 727 * (5 : ZMod 2147912143543) ^ 727 := by rw [pow_add]
          _ = 220817464573 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 2147912143543) ^ 2909 = 1187720303447 := by
        calc
          (5 : ZMod 2147912143543) ^ 2909 = (5 : ZMod 2147912143543) ^ (1454 + 1454 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1454 * (5 : ZMod 2147912143543) ^ 1454) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1187720303447 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 2147912143543) ^ 5819 = 918912010692 := by
        calc
          (5 : ZMod 2147912143543) ^ 5819 = (5 : ZMod 2147912143543) ^ (2909 + 2909 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2909 * (5 : ZMod 2147912143543) ^ 2909) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 918912010692 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 2147912143543) ^ 11638 = 1072933769912 := by
        calc
          (5 : ZMod 2147912143543) ^ 11638 = (5 : ZMod 2147912143543) ^ (5819 + 5819) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 5819 * (5 : ZMod 2147912143543) ^ 5819 := by rw [pow_add]
          _ = 1072933769912 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 2147912143543) ^ 23277 = 896488107897 := by
        calc
          (5 : ZMod 2147912143543) ^ 23277 = (5 : ZMod 2147912143543) ^ (11638 + 11638 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 11638 * (5 : ZMod 2147912143543) ^ 11638) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 896488107897 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 2147912143543) ^ 46554 = 930761821499 := by
        calc
          (5 : ZMod 2147912143543) ^ 46554 = (5 : ZMod 2147912143543) ^ (23277 + 23277) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 23277 * (5 : ZMod 2147912143543) ^ 23277 := by rw [pow_add]
          _ = 930761821499 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 2147912143543) ^ 93109 = 1406052703146 := by
        calc
          (5 : ZMod 2147912143543) ^ 93109 = (5 : ZMod 2147912143543) ^ (46554 + 46554 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 46554 * (5 : ZMod 2147912143543) ^ 46554) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1406052703146 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 2147912143543) ^ 186218 = 607341600991 := by
        calc
          (5 : ZMod 2147912143543) ^ 186218 = (5 : ZMod 2147912143543) ^ (93109 + 93109) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 93109 * (5 : ZMod 2147912143543) ^ 93109 := by rw [pow_add]
          _ = 607341600991 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 2147912143543) ^ 372437 = 1994172856808 := by
        calc
          (5 : ZMod 2147912143543) ^ 372437 = (5 : ZMod 2147912143543) ^ (186218 + 186218 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 186218 * (5 : ZMod 2147912143543) ^ 186218) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1994172856808 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 2147912143543) ^ 744875 = 2086480685437 := by
        calc
          (5 : ZMod 2147912143543) ^ 744875 = (5 : ZMod 2147912143543) ^ (372437 + 372437 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 372437 * (5 : ZMod 2147912143543) ^ 372437) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 2086480685437 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 2147912143543) ^ 1489751 = 1814522484932 := by
        calc
          (5 : ZMod 2147912143543) ^ 1489751 = (5 : ZMod 2147912143543) ^ (744875 + 744875 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 744875 * (5 : ZMod 2147912143543) ^ 744875) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1814522484932 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 2147912143543) ^ 2979503 = 2141744709317 := by
        calc
          (5 : ZMod 2147912143543) ^ 2979503 = (5 : ZMod 2147912143543) ^ (1489751 + 1489751 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1489751 * (5 : ZMod 2147912143543) ^ 1489751) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 2141744709317 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 2147912143543) ^ 5959006 = 1952586131742 := by
        calc
          (5 : ZMod 2147912143543) ^ 5959006 = (5 : ZMod 2147912143543) ^ (2979503 + 2979503) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 2979503 * (5 : ZMod 2147912143543) ^ 2979503 := by rw [pow_add]
          _ = 1952586131742 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 2147912143543) ^ 11918013 = 82394673115 := by
        calc
          (5 : ZMod 2147912143543) ^ 11918013 = (5 : ZMod 2147912143543) ^ (5959006 + 5959006 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 5959006 * (5 : ZMod 2147912143543) ^ 5959006) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 82394673115 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 2147912143543) ^ 23836027 = 1254520013396 := by
        calc
          (5 : ZMod 2147912143543) ^ 23836027 = (5 : ZMod 2147912143543) ^ (11918013 + 11918013 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 11918013 * (5 : ZMod 2147912143543) ^ 11918013) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1254520013396 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 2147912143543) ^ 47672055 = 444337117212 := by
        calc
          (5 : ZMod 2147912143543) ^ 47672055 = (5 : ZMod 2147912143543) ^ (23836027 + 23836027 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 23836027 * (5 : ZMod 2147912143543) ^ 23836027) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 444337117212 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 2147912143543) ^ 95344111 = 776865829799 := by
        calc
          (5 : ZMod 2147912143543) ^ 95344111 = (5 : ZMod 2147912143543) ^ (47672055 + 47672055 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 47672055 * (5 : ZMod 2147912143543) ^ 47672055) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 776865829799 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 2147912143543) ^ 190688222 = 1272903485418 := by
        calc
          (5 : ZMod 2147912143543) ^ 190688222 = (5 : ZMod 2147912143543) ^ (95344111 + 95344111) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 95344111 * (5 : ZMod 2147912143543) ^ 95344111 := by rw [pow_add]
          _ = 1272903485418 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 2147912143543) ^ 381376445 = 811435607701 := by
        calc
          (5 : ZMod 2147912143543) ^ 381376445 = (5 : ZMod 2147912143543) ^ (190688222 + 190688222 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 190688222 * (5 : ZMod 2147912143543) ^ 190688222) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 811435607701 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 2147912143543) ^ 762752891 = 1990440296899 := by
        calc
          (5 : ZMod 2147912143543) ^ 762752891 = (5 : ZMod 2147912143543) ^ (381376445 + 381376445 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 381376445 * (5 : ZMod 2147912143543) ^ 381376445) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1990440296899 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 2147912143543) ^ 1525505783 = 1474538406468 := by
        calc
          (5 : ZMod 2147912143543) ^ 1525505783 = (5 : ZMod 2147912143543) ^ (762752891 + 762752891 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 762752891 * (5 : ZMod 2147912143543) ^ 762752891) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1474538406468 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 2147912143543) ^ 3051011567 = 1127504117667 := by
        calc
          (5 : ZMod 2147912143543) ^ 3051011567 = (5 : ZMod 2147912143543) ^ (1525505783 + 1525505783 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1525505783 * (5 : ZMod 2147912143543) ^ 1525505783) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1127504117667 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 2147912143543) ^ 6102023135 = 1971961684511 := by
        calc
          (5 : ZMod 2147912143543) ^ 6102023135 = (5 : ZMod 2147912143543) ^ (3051011567 + 3051011567 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 3051011567 * (5 : ZMod 2147912143543) ^ 3051011567) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1971961684511 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 2147912143543) ^ 12204046270 = 2144441558162 := by
        calc
          (5 : ZMod 2147912143543) ^ 12204046270 = (5 : ZMod 2147912143543) ^ (6102023135 + 6102023135) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 6102023135 * (5 : ZMod 2147912143543) ^ 6102023135 := by rw [pow_add]
          _ = 2144441558162 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 2147912143543) ^ 24408092540 = 2120121226282 := by
        calc
          (5 : ZMod 2147912143543) ^ 24408092540 = (5 : ZMod 2147912143543) ^ (12204046270 + 12204046270) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 12204046270 * (5 : ZMod 2147912143543) ^ 12204046270 := by rw [pow_add]
          _ = 2120121226282 := by rw [factor_2_33]; decide
      have factor_2_35 : (5 : ZMod 2147912143543) ^ 48816185080 = 627790082178 := by
        calc
          (5 : ZMod 2147912143543) ^ 48816185080 = (5 : ZMod 2147912143543) ^ (24408092540 + 24408092540) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 24408092540 * (5 : ZMod 2147912143543) ^ 24408092540 := by rw [pow_add]
          _ = 627790082178 := by rw [factor_2_34]; decide
      have factor_2_36 : (5 : ZMod 2147912143543) ^ 97632370161 = 105173034847 := by
        calc
          (5 : ZMod 2147912143543) ^ 97632370161 = (5 : ZMod 2147912143543) ^ (48816185080 + 48816185080 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 48816185080 * (5 : ZMod 2147912143543) ^ 48816185080) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 105173034847 := by rw [factor_2_35]; decide
      have factor_2_37 : (5 : ZMod 2147912143543) ^ 195264740322 = 1083104170930 := by
        calc
          (5 : ZMod 2147912143543) ^ 195264740322 = (5 : ZMod 2147912143543) ^ (97632370161 + 97632370161) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 97632370161 * (5 : ZMod 2147912143543) ^ 97632370161 := by rw [pow_add]
          _ = 1083104170930 := by rw [factor_2_36]; decide
      change (5 : ZMod 2147912143543) ^ 195264740322 ≠ 1
      rw [factor_2_37]
      decide
    ·
      have factor_3_0 : (5 : ZMod 2147912143543) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 2147912143543) ^ 3 = 125 := by
        calc
          (5 : ZMod 2147912143543) ^ 3 = (5 : ZMod 2147912143543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1 * (5 : ZMod 2147912143543) ^ 1) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 2147912143543) ^ 6 = 15625 := by
        calc
          (5 : ZMod 2147912143543) ^ 6 = (5 : ZMod 2147912143543) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 3 * (5 : ZMod 2147912143543) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 2147912143543) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 2147912143543) ^ 12 = (5 : ZMod 2147912143543) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 6 * (5 : ZMod 2147912143543) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 2147912143543) ^ 24 = 82792072375 := by
        calc
          (5 : ZMod 2147912143543) ^ 24 = (5 : ZMod 2147912143543) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 12 * (5 : ZMod 2147912143543) ^ 12 := by rw [pow_add]
          _ = 82792072375 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 2147912143543) ^ 48 = 1760736411708 := by
        calc
          (5 : ZMod 2147912143543) ^ 48 = (5 : ZMod 2147912143543) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 24 * (5 : ZMod 2147912143543) ^ 24 := by rw [pow_add]
          _ = 1760736411708 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 2147912143543) ^ 97 = 1094816686670 := by
        calc
          (5 : ZMod 2147912143543) ^ 97 = (5 : ZMod 2147912143543) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 48 * (5 : ZMod 2147912143543) ^ 48) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1094816686670 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 2147912143543) ^ 195 = 108383364692 := by
        calc
          (5 : ZMod 2147912143543) ^ 195 = (5 : ZMod 2147912143543) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 97 * (5 : ZMod 2147912143543) ^ 97) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 108383364692 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 2147912143543) ^ 390 = 179631728357 := by
        calc
          (5 : ZMod 2147912143543) ^ 390 = (5 : ZMod 2147912143543) ^ (195 + 195) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 195 * (5 : ZMod 2147912143543) ^ 195 := by rw [pow_add]
          _ = 179631728357 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 2147912143543) ^ 780 = 841169117196 := by
        calc
          (5 : ZMod 2147912143543) ^ 780 = (5 : ZMod 2147912143543) ^ (390 + 390) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 390 * (5 : ZMod 2147912143543) ^ 390 := by rw [pow_add]
          _ = 841169117196 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 2147912143543) ^ 1561 = 952772928965 := by
        calc
          (5 : ZMod 2147912143543) ^ 1561 = (5 : ZMod 2147912143543) ^ (780 + 780 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 780 * (5 : ZMod 2147912143543) ^ 780) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 952772928965 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 2147912143543) ^ 3122 = 916195292803 := by
        calc
          (5 : ZMod 2147912143543) ^ 3122 = (5 : ZMod 2147912143543) ^ (1561 + 1561) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1561 * (5 : ZMod 2147912143543) ^ 1561 := by rw [pow_add]
          _ = 916195292803 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 2147912143543) ^ 6245 = 249381850645 := by
        calc
          (5 : ZMod 2147912143543) ^ 6245 = (5 : ZMod 2147912143543) ^ (3122 + 3122 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 3122 * (5 : ZMod 2147912143543) ^ 3122) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 249381850645 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 2147912143543) ^ 12490 = 525529416180 := by
        calc
          (5 : ZMod 2147912143543) ^ 12490 = (5 : ZMod 2147912143543) ^ (6245 + 6245) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 6245 * (5 : ZMod 2147912143543) ^ 6245 := by rw [pow_add]
          _ = 525529416180 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 2147912143543) ^ 24980 = 772660103831 := by
        calc
          (5 : ZMod 2147912143543) ^ 24980 = (5 : ZMod 2147912143543) ^ (12490 + 12490) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 12490 * (5 : ZMod 2147912143543) ^ 12490 := by rw [pow_add]
          _ = 772660103831 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 2147912143543) ^ 49961 = 1131722986927 := by
        calc
          (5 : ZMod 2147912143543) ^ 49961 = (5 : ZMod 2147912143543) ^ (24980 + 24980 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 24980 * (5 : ZMod 2147912143543) ^ 24980) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1131722986927 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 2147912143543) ^ 99922 = 1276720238581 := by
        calc
          (5 : ZMod 2147912143543) ^ 99922 = (5 : ZMod 2147912143543) ^ (49961 + 49961) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 49961 * (5 : ZMod 2147912143543) ^ 49961 := by rw [pow_add]
          _ = 1276720238581 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 2147912143543) ^ 199844 = 300549950271 := by
        calc
          (5 : ZMod 2147912143543) ^ 199844 = (5 : ZMod 2147912143543) ^ (99922 + 99922) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 99922 * (5 : ZMod 2147912143543) ^ 99922 := by rw [pow_add]
          _ = 300549950271 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 2147912143543) ^ 399689 = 1181329702885 := by
        calc
          (5 : ZMod 2147912143543) ^ 399689 = (5 : ZMod 2147912143543) ^ (199844 + 199844 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 199844 * (5 : ZMod 2147912143543) ^ 199844) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1181329702885 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 2147912143543) ^ 799378 = 1261966018257 := by
        calc
          (5 : ZMod 2147912143543) ^ 799378 = (5 : ZMod 2147912143543) ^ (399689 + 399689) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 399689 * (5 : ZMod 2147912143543) ^ 399689 := by rw [pow_add]
          _ = 1261966018257 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 2147912143543) ^ 1598757 = 893377912083 := by
        calc
          (5 : ZMod 2147912143543) ^ 1598757 = (5 : ZMod 2147912143543) ^ (799378 + 799378 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 799378 * (5 : ZMod 2147912143543) ^ 799378) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 893377912083 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 2147912143543) ^ 3197515 = 1960608463134 := by
        calc
          (5 : ZMod 2147912143543) ^ 3197515 = (5 : ZMod 2147912143543) ^ (1598757 + 1598757 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1598757 * (5 : ZMod 2147912143543) ^ 1598757) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1960608463134 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 2147912143543) ^ 6395031 = 1277273403830 := by
        calc
          (5 : ZMod 2147912143543) ^ 6395031 = (5 : ZMod 2147912143543) ^ (3197515 + 3197515 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 3197515 * (5 : ZMod 2147912143543) ^ 3197515) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1277273403830 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 2147912143543) ^ 12790063 = 917354812709 := by
        calc
          (5 : ZMod 2147912143543) ^ 12790063 = (5 : ZMod 2147912143543) ^ (6395031 + 6395031 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 6395031 * (5 : ZMod 2147912143543) ^ 6395031) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 917354812709 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 2147912143543) ^ 25580127 = 1223495814049 := by
        calc
          (5 : ZMod 2147912143543) ^ 25580127 = (5 : ZMod 2147912143543) ^ (12790063 + 12790063 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 12790063 * (5 : ZMod 2147912143543) ^ 12790063) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1223495814049 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 2147912143543) ^ 51160254 = 391471721209 := by
        calc
          (5 : ZMod 2147912143543) ^ 51160254 = (5 : ZMod 2147912143543) ^ (25580127 + 25580127) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 25580127 * (5 : ZMod 2147912143543) ^ 25580127 := by rw [pow_add]
          _ = 391471721209 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 2147912143543) ^ 102320509 = 518946340184 := by
        calc
          (5 : ZMod 2147912143543) ^ 102320509 = (5 : ZMod 2147912143543) ^ (51160254 + 51160254 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 51160254 * (5 : ZMod 2147912143543) ^ 51160254) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 518946340184 := by rw [factor_3_25]; decide
      have factor_3_27 : (5 : ZMod 2147912143543) ^ 204641019 = 741839663779 := by
        calc
          (5 : ZMod 2147912143543) ^ 204641019 = (5 : ZMod 2147912143543) ^ (102320509 + 102320509 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 102320509 * (5 : ZMod 2147912143543) ^ 102320509) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 741839663779 := by rw [factor_3_26]; decide
      have factor_3_28 : (5 : ZMod 2147912143543) ^ 409282039 = 1178159854832 := by
        calc
          (5 : ZMod 2147912143543) ^ 409282039 = (5 : ZMod 2147912143543) ^ (204641019 + 204641019 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 204641019 * (5 : ZMod 2147912143543) ^ 204641019) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1178159854832 := by rw [factor_3_27]; decide
      have factor_3_29 : (5 : ZMod 2147912143543) ^ 818564079 = 1222075111646 := by
        calc
          (5 : ZMod 2147912143543) ^ 818564079 = (5 : ZMod 2147912143543) ^ (409282039 + 409282039 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 409282039 * (5 : ZMod 2147912143543) ^ 409282039) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1222075111646 := by rw [factor_3_28]; decide
      have factor_3_30 : (5 : ZMod 2147912143543) ^ 1637128158 = 331394515107 := by
        calc
          (5 : ZMod 2147912143543) ^ 1637128158 = (5 : ZMod 2147912143543) ^ (818564079 + 818564079) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 818564079 * (5 : ZMod 2147912143543) ^ 818564079 := by rw [pow_add]
          _ = 331394515107 := by rw [factor_3_29]; decide
      have factor_3_31 : (5 : ZMod 2147912143543) ^ 3274256316 = 477507087314 := by
        calc
          (5 : ZMod 2147912143543) ^ 3274256316 = (5 : ZMod 2147912143543) ^ (1637128158 + 1637128158) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 1637128158 * (5 : ZMod 2147912143543) ^ 1637128158 := by rw [pow_add]
          _ = 477507087314 := by rw [factor_3_30]; decide
      have factor_3_32 : (5 : ZMod 2147912143543) ^ 6548512632 = 1799106866075 := by
        calc
          (5 : ZMod 2147912143543) ^ 6548512632 = (5 : ZMod 2147912143543) ^ (3274256316 + 3274256316) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 3274256316 * (5 : ZMod 2147912143543) ^ 3274256316 := by rw [pow_add]
          _ = 1799106866075 := by rw [factor_3_31]; decide
      have factor_3_33 : (5 : ZMod 2147912143543) ^ 13097025265 = 146243336048 := by
        calc
          (5 : ZMod 2147912143543) ^ 13097025265 = (5 : ZMod 2147912143543) ^ (6548512632 + 6548512632 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 6548512632 * (5 : ZMod 2147912143543) ^ 6548512632) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 146243336048 := by rw [factor_3_32]; decide
      have factor_3_34 : (5 : ZMod 2147912143543) ^ 26194050531 = 1700173386307 := by
        calc
          (5 : ZMod 2147912143543) ^ 26194050531 = (5 : ZMod 2147912143543) ^ (13097025265 + 13097025265 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 13097025265 * (5 : ZMod 2147912143543) ^ 13097025265) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1700173386307 := by rw [factor_3_33]; decide
      have factor_3_35 : (5 : ZMod 2147912143543) ^ 52388101062 = 984500493635 := by
        calc
          (5 : ZMod 2147912143543) ^ 52388101062 = (5 : ZMod 2147912143543) ^ (26194050531 + 26194050531) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 26194050531 * (5 : ZMod 2147912143543) ^ 26194050531 := by rw [pow_add]
          _ = 984500493635 := by rw [factor_3_34]; decide
      change (5 : ZMod 2147912143543) ^ 52388101062 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (5 : ZMod 2147912143543) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 2147912143543) ^ 3 = 125 := by
        calc
          (5 : ZMod 2147912143543) ^ 3 = (5 : ZMod 2147912143543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1 * (5 : ZMod 2147912143543) ^ 1) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 2147912143543) ^ 7 = 78125 := by
        calc
          (5 : ZMod 2147912143543) ^ 7 = (5 : ZMod 2147912143543) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 3 * (5 : ZMod 2147912143543) ^ 3) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 2147912143543) ^ 15 = 30517578125 := by
        calc
          (5 : ZMod 2147912143543) ^ 15 = (5 : ZMod 2147912143543) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 7 * (5 : ZMod 2147912143543) ^ 7) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 30517578125 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 2147912143543) ^ 31 = 767190088902 := by
        calc
          (5 : ZMod 2147912143543) ^ 31 = (5 : ZMod 2147912143543) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 15 * (5 : ZMod 2147912143543) ^ 15) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 767190088902 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 2147912143543) ^ 63 = 184811906002 := by
        calc
          (5 : ZMod 2147912143543) ^ 63 = (5 : ZMod 2147912143543) ^ (31 + 31 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 31 * (5 : ZMod 2147912143543) ^ 31) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 184811906002 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 2147912143543) ^ 126 = 620435687445 := by
        calc
          (5 : ZMod 2147912143543) ^ 126 = (5 : ZMod 2147912143543) ^ (63 + 63) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 63 * (5 : ZMod 2147912143543) ^ 63 := by rw [pow_add]
          _ = 620435687445 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 2147912143543) ^ 253 = 236255489975 := by
        calc
          (5 : ZMod 2147912143543) ^ 253 = (5 : ZMod 2147912143543) ^ (126 + 126 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 126 * (5 : ZMod 2147912143543) ^ 126) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 236255489975 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 2147912143543) ^ 507 = 431110303182 := by
        calc
          (5 : ZMod 2147912143543) ^ 507 = (5 : ZMod 2147912143543) ^ (253 + 253 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 253 * (5 : ZMod 2147912143543) ^ 253) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 431110303182 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 2147912143543) ^ 1014 = 258718464902 := by
        calc
          (5 : ZMod 2147912143543) ^ 1014 = (5 : ZMod 2147912143543) ^ (507 + 507) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 507 * (5 : ZMod 2147912143543) ^ 507 := by rw [pow_add]
          _ = 258718464902 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 2147912143543) ^ 2029 = 1601341137658 := by
        calc
          (5 : ZMod 2147912143543) ^ 2029 = (5 : ZMod 2147912143543) ^ (1014 + 1014 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 1014 * (5 : ZMod 2147912143543) ^ 1014) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 1601341137658 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 2147912143543) ^ 4059 = 2050706786342 := by
        calc
          (5 : ZMod 2147912143543) ^ 4059 = (5 : ZMod 2147912143543) ^ (2029 + 2029 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = ((5 : ZMod 2147912143543) ^ 2029 * (5 : ZMod 2147912143543) ^ 2029) * (5 : ZMod 2147912143543) := by rw [pow_succ, pow_add]
          _ = 2050706786342 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 2147912143543) ^ 8118 = 189345884724 := by
        calc
          (5 : ZMod 2147912143543) ^ 8118 = (5 : ZMod 2147912143543) ^ (4059 + 4059) :=
            congrArg (fun n : ℕ => (5 : ZMod 2147912143543) ^ n) (by norm_num)
          _ = (5 : ZMod 2147912143543) ^ 4059 * (5 : ZMod 2147912143543) ^ 4059 := by rw [pow_add]
          _ = 189345884724 := by rw [factor_4_11]; decide
      change (5 : ZMod 2147912143543) ^ 8118 ≠ 1
      rw [factor_4_12]
      decide

#print axioms prime_lucas_2147912143543

end TotientTailPeriodKiller
end Erdos249257
