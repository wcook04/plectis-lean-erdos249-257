import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_116454478141 : Nat.Prime 116454478141 := by
  apply lucas_primality 116454478141 (10 : ZMod 116454478141)
  ·
      have fermat_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 116454478141) ^ 3 = 1000 := by
        calc
          (10 : ZMod 116454478141) ^ 3 = (10 : ZMod 116454478141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 116454478141) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 116454478141) ^ 6 = (10 : ZMod 116454478141) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3 * (10 : ZMod 116454478141) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 116454478141) ^ 13 = 101369358015 := by
        calc
          (10 : ZMod 116454478141) ^ 13 = (10 : ZMod 116454478141) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 6 * (10 : ZMod 116454478141) ^ 6) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 101369358015 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 116454478141) ^ 27 = 6222519672 := by
        calc
          (10 : ZMod 116454478141) ^ 27 = (10 : ZMod 116454478141) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 13 * (10 : ZMod 116454478141) ^ 13) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 6222519672 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 116454478141) ^ 54 = 69756649848 := by
        calc
          (10 : ZMod 116454478141) ^ 54 = (10 : ZMod 116454478141) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 27 * (10 : ZMod 116454478141) ^ 27 := by rw [pow_add]
          _ = 69756649848 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 116454478141) ^ 108 = 108467530817 := by
        calc
          (10 : ZMod 116454478141) ^ 108 = (10 : ZMod 116454478141) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 54 * (10 : ZMod 116454478141) ^ 54 := by rw [pow_add]
          _ = 108467530817 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 116454478141) ^ 216 = 76121279991 := by
        calc
          (10 : ZMod 116454478141) ^ 216 = (10 : ZMod 116454478141) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 108 * (10 : ZMod 116454478141) ^ 108 := by rw [pow_add]
          _ = 76121279991 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 116454478141) ^ 433 = 42634087633 := by
        calc
          (10 : ZMod 116454478141) ^ 433 = (10 : ZMod 116454478141) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 216 * (10 : ZMod 116454478141) ^ 216) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 42634087633 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 116454478141) ^ 867 = 85628906123 := by
        calc
          (10 : ZMod 116454478141) ^ 867 = (10 : ZMod 116454478141) ^ (433 + 433 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 433 * (10 : ZMod 116454478141) ^ 433) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 85628906123 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 116454478141) ^ 1735 = 50017012440 := by
        calc
          (10 : ZMod 116454478141) ^ 1735 = (10 : ZMod 116454478141) ^ (867 + 867 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 867 * (10 : ZMod 116454478141) ^ 867) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 50017012440 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 116454478141) ^ 3470 = 112614006151 := by
        calc
          (10 : ZMod 116454478141) ^ 3470 = (10 : ZMod 116454478141) ^ (1735 + 1735) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1735 * (10 : ZMod 116454478141) ^ 1735 := by rw [pow_add]
          _ = 112614006151 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 116454478141) ^ 6941 = 30794355046 := by
        calc
          (10 : ZMod 116454478141) ^ 6941 = (10 : ZMod 116454478141) ^ (3470 + 3470 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3470 * (10 : ZMod 116454478141) ^ 3470) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 30794355046 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 116454478141) ^ 13882 = 84049208012 := by
        calc
          (10 : ZMod 116454478141) ^ 13882 = (10 : ZMod 116454478141) ^ (6941 + 6941) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 6941 * (10 : ZMod 116454478141) ^ 6941 := by rw [pow_add]
          _ = 84049208012 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 116454478141) ^ 27764 = 52908364026 := by
        calc
          (10 : ZMod 116454478141) ^ 27764 = (10 : ZMod 116454478141) ^ (13882 + 13882) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 13882 * (10 : ZMod 116454478141) ^ 13882 := by rw [pow_add]
          _ = 52908364026 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 116454478141) ^ 55529 = 115548552911 := by
        calc
          (10 : ZMod 116454478141) ^ 55529 = (10 : ZMod 116454478141) ^ (27764 + 27764 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 27764 * (10 : ZMod 116454478141) ^ 27764) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 115548552911 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 116454478141) ^ 111059 = 16992252306 := by
        calc
          (10 : ZMod 116454478141) ^ 111059 = (10 : ZMod 116454478141) ^ (55529 + 55529 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 55529 * (10 : ZMod 116454478141) ^ 55529) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 16992252306 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 116454478141) ^ 222119 = 27595446525 := by
        calc
          (10 : ZMod 116454478141) ^ 222119 = (10 : ZMod 116454478141) ^ (111059 + 111059 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 111059 * (10 : ZMod 116454478141) ^ 111059) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 27595446525 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 116454478141) ^ 444238 = 38828005759 := by
        calc
          (10 : ZMod 116454478141) ^ 444238 = (10 : ZMod 116454478141) ^ (222119 + 222119) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 222119 * (10 : ZMod 116454478141) ^ 222119 := by rw [pow_add]
          _ = 38828005759 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 116454478141) ^ 888477 = 92894882360 := by
        calc
          (10 : ZMod 116454478141) ^ 888477 = (10 : ZMod 116454478141) ^ (444238 + 444238 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 444238 * (10 : ZMod 116454478141) ^ 444238) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 92894882360 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 116454478141) ^ 1776954 = 63898855132 := by
        calc
          (10 : ZMod 116454478141) ^ 1776954 = (10 : ZMod 116454478141) ^ (888477 + 888477) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 888477 * (10 : ZMod 116454478141) ^ 888477 := by rw [pow_add]
          _ = 63898855132 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 116454478141) ^ 3553908 = 65853049144 := by
        calc
          (10 : ZMod 116454478141) ^ 3553908 = (10 : ZMod 116454478141) ^ (1776954 + 1776954) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1776954 * (10 : ZMod 116454478141) ^ 1776954 := by rw [pow_add]
          _ = 65853049144 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 116454478141) ^ 7107817 = 73382705036 := by
        calc
          (10 : ZMod 116454478141) ^ 7107817 = (10 : ZMod 116454478141) ^ (3553908 + 3553908 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3553908 * (10 : ZMod 116454478141) ^ 3553908) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 73382705036 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 116454478141) ^ 14215634 = 24518446380 := by
        calc
          (10 : ZMod 116454478141) ^ 14215634 = (10 : ZMod 116454478141) ^ (7107817 + 7107817) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 7107817 * (10 : ZMod 116454478141) ^ 7107817 := by rw [pow_add]
          _ = 24518446380 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 116454478141) ^ 28431269 = 33642978380 := by
        calc
          (10 : ZMod 116454478141) ^ 28431269 = (10 : ZMod 116454478141) ^ (14215634 + 14215634 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 14215634 * (10 : ZMod 116454478141) ^ 14215634) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 33642978380 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 116454478141) ^ 56862538 = 104485541473 := by
        calc
          (10 : ZMod 116454478141) ^ 56862538 = (10 : ZMod 116454478141) ^ (28431269 + 28431269) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 28431269 * (10 : ZMod 116454478141) ^ 28431269 := by rw [pow_add]
          _ = 104485541473 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 116454478141) ^ 113725076 = 114756687061 := by
        calc
          (10 : ZMod 116454478141) ^ 113725076 = (10 : ZMod 116454478141) ^ (56862538 + 56862538) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 56862538 * (10 : ZMod 116454478141) ^ 56862538 := by rw [pow_add]
          _ = 114756687061 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 116454478141) ^ 227450152 = 32571026326 := by
        calc
          (10 : ZMod 116454478141) ^ 227450152 = (10 : ZMod 116454478141) ^ (113725076 + 113725076) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 113725076 * (10 : ZMod 116454478141) ^ 113725076 := by rw [pow_add]
          _ = 32571026326 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 116454478141) ^ 454900305 = 59600900818 := by
        calc
          (10 : ZMod 116454478141) ^ 454900305 = (10 : ZMod 116454478141) ^ (227450152 + 227450152 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 227450152 * (10 : ZMod 116454478141) ^ 227450152) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 59600900818 := by rw [fermat_27]; decide
      have fermat_29 : (10 : ZMod 116454478141) ^ 909800610 = 71132503344 := by
        calc
          (10 : ZMod 116454478141) ^ 909800610 = (10 : ZMod 116454478141) ^ (454900305 + 454900305) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 454900305 * (10 : ZMod 116454478141) ^ 454900305 := by rw [pow_add]
          _ = 71132503344 := by rw [fermat_28]; decide
      have fermat_30 : (10 : ZMod 116454478141) ^ 1819601220 = 45892272931 := by
        calc
          (10 : ZMod 116454478141) ^ 1819601220 = (10 : ZMod 116454478141) ^ (909800610 + 909800610) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 909800610 * (10 : ZMod 116454478141) ^ 909800610 := by rw [pow_add]
          _ = 45892272931 := by rw [fermat_29]; decide
      have fermat_31 : (10 : ZMod 116454478141) ^ 3639202441 = 104612642720 := by
        calc
          (10 : ZMod 116454478141) ^ 3639202441 = (10 : ZMod 116454478141) ^ (1819601220 + 1819601220 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1819601220 * (10 : ZMod 116454478141) ^ 1819601220) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 104612642720 := by rw [fermat_30]; decide
      have fermat_32 : (10 : ZMod 116454478141) ^ 7278404883 = 98272067343 := by
        calc
          (10 : ZMod 116454478141) ^ 7278404883 = (10 : ZMod 116454478141) ^ (3639202441 + 3639202441 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3639202441 * (10 : ZMod 116454478141) ^ 3639202441) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 98272067343 := by rw [fermat_31]; decide
      have fermat_33 : (10 : ZMod 116454478141) ^ 14556809767 = 29740054208 := by
        calc
          (10 : ZMod 116454478141) ^ 14556809767 = (10 : ZMod 116454478141) ^ (7278404883 + 7278404883 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 7278404883 * (10 : ZMod 116454478141) ^ 7278404883) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 29740054208 := by rw [fermat_32]; decide
      have fermat_34 : (10 : ZMod 116454478141) ^ 29113619535 = 45872425897 := by
        calc
          (10 : ZMod 116454478141) ^ 29113619535 = (10 : ZMod 116454478141) ^ (14556809767 + 14556809767 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 14556809767 * (10 : ZMod 116454478141) ^ 14556809767) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 45872425897 := by rw [fermat_33]; decide
      have fermat_35 : (10 : ZMod 116454478141) ^ 58227239070 = 116454478140 := by
        calc
          (10 : ZMod 116454478141) ^ 58227239070 = (10 : ZMod 116454478141) ^ (29113619535 + 29113619535) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 29113619535 * (10 : ZMod 116454478141) ^ 29113619535 := by rw [pow_add]
          _ = 116454478140 := by rw [fermat_34]; decide
      have fermat_36 : (10 : ZMod 116454478141) ^ 116454478140 = 1 := by
        calc
          (10 : ZMod 116454478141) ^ 116454478140 = (10 : ZMod 116454478141) ^ (58227239070 + 58227239070) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 58227239070 * (10 : ZMod 116454478141) ^ 58227239070 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 116454478141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 116454478141) ^ 3 = 1000 := by
        calc
          (10 : ZMod 116454478141) ^ 3 = (10 : ZMod 116454478141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 116454478141) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 116454478141) ^ 6 = (10 : ZMod 116454478141) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3 * (10 : ZMod 116454478141) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 116454478141) ^ 13 = 101369358015 := by
        calc
          (10 : ZMod 116454478141) ^ 13 = (10 : ZMod 116454478141) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 6 * (10 : ZMod 116454478141) ^ 6) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 101369358015 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 116454478141) ^ 27 = 6222519672 := by
        calc
          (10 : ZMod 116454478141) ^ 27 = (10 : ZMod 116454478141) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 13 * (10 : ZMod 116454478141) ^ 13) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 6222519672 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 116454478141) ^ 54 = 69756649848 := by
        calc
          (10 : ZMod 116454478141) ^ 54 = (10 : ZMod 116454478141) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 27 * (10 : ZMod 116454478141) ^ 27 := by rw [pow_add]
          _ = 69756649848 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 116454478141) ^ 108 = 108467530817 := by
        calc
          (10 : ZMod 116454478141) ^ 108 = (10 : ZMod 116454478141) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 54 * (10 : ZMod 116454478141) ^ 54 := by rw [pow_add]
          _ = 108467530817 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 116454478141) ^ 216 = 76121279991 := by
        calc
          (10 : ZMod 116454478141) ^ 216 = (10 : ZMod 116454478141) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 108 * (10 : ZMod 116454478141) ^ 108 := by rw [pow_add]
          _ = 76121279991 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 116454478141) ^ 433 = 42634087633 := by
        calc
          (10 : ZMod 116454478141) ^ 433 = (10 : ZMod 116454478141) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 216 * (10 : ZMod 116454478141) ^ 216) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 42634087633 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 116454478141) ^ 867 = 85628906123 := by
        calc
          (10 : ZMod 116454478141) ^ 867 = (10 : ZMod 116454478141) ^ (433 + 433 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 433 * (10 : ZMod 116454478141) ^ 433) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 85628906123 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 116454478141) ^ 1735 = 50017012440 := by
        calc
          (10 : ZMod 116454478141) ^ 1735 = (10 : ZMod 116454478141) ^ (867 + 867 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 867 * (10 : ZMod 116454478141) ^ 867) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 50017012440 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 116454478141) ^ 3470 = 112614006151 := by
        calc
          (10 : ZMod 116454478141) ^ 3470 = (10 : ZMod 116454478141) ^ (1735 + 1735) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1735 * (10 : ZMod 116454478141) ^ 1735 := by rw [pow_add]
          _ = 112614006151 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 116454478141) ^ 6941 = 30794355046 := by
        calc
          (10 : ZMod 116454478141) ^ 6941 = (10 : ZMod 116454478141) ^ (3470 + 3470 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3470 * (10 : ZMod 116454478141) ^ 3470) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 30794355046 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 116454478141) ^ 13882 = 84049208012 := by
        calc
          (10 : ZMod 116454478141) ^ 13882 = (10 : ZMod 116454478141) ^ (6941 + 6941) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 6941 * (10 : ZMod 116454478141) ^ 6941 := by rw [pow_add]
          _ = 84049208012 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 116454478141) ^ 27764 = 52908364026 := by
        calc
          (10 : ZMod 116454478141) ^ 27764 = (10 : ZMod 116454478141) ^ (13882 + 13882) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 13882 * (10 : ZMod 116454478141) ^ 13882 := by rw [pow_add]
          _ = 52908364026 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 116454478141) ^ 55529 = 115548552911 := by
        calc
          (10 : ZMod 116454478141) ^ 55529 = (10 : ZMod 116454478141) ^ (27764 + 27764 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 27764 * (10 : ZMod 116454478141) ^ 27764) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 115548552911 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 116454478141) ^ 111059 = 16992252306 := by
        calc
          (10 : ZMod 116454478141) ^ 111059 = (10 : ZMod 116454478141) ^ (55529 + 55529 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 55529 * (10 : ZMod 116454478141) ^ 55529) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 16992252306 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 116454478141) ^ 222119 = 27595446525 := by
        calc
          (10 : ZMod 116454478141) ^ 222119 = (10 : ZMod 116454478141) ^ (111059 + 111059 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 111059 * (10 : ZMod 116454478141) ^ 111059) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 27595446525 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 116454478141) ^ 444238 = 38828005759 := by
        calc
          (10 : ZMod 116454478141) ^ 444238 = (10 : ZMod 116454478141) ^ (222119 + 222119) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 222119 * (10 : ZMod 116454478141) ^ 222119 := by rw [pow_add]
          _ = 38828005759 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 116454478141) ^ 888477 = 92894882360 := by
        calc
          (10 : ZMod 116454478141) ^ 888477 = (10 : ZMod 116454478141) ^ (444238 + 444238 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 444238 * (10 : ZMod 116454478141) ^ 444238) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 92894882360 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 116454478141) ^ 1776954 = 63898855132 := by
        calc
          (10 : ZMod 116454478141) ^ 1776954 = (10 : ZMod 116454478141) ^ (888477 + 888477) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 888477 * (10 : ZMod 116454478141) ^ 888477 := by rw [pow_add]
          _ = 63898855132 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 116454478141) ^ 3553908 = 65853049144 := by
        calc
          (10 : ZMod 116454478141) ^ 3553908 = (10 : ZMod 116454478141) ^ (1776954 + 1776954) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1776954 * (10 : ZMod 116454478141) ^ 1776954 := by rw [pow_add]
          _ = 65853049144 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 116454478141) ^ 7107817 = 73382705036 := by
        calc
          (10 : ZMod 116454478141) ^ 7107817 = (10 : ZMod 116454478141) ^ (3553908 + 3553908 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3553908 * (10 : ZMod 116454478141) ^ 3553908) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 73382705036 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 116454478141) ^ 14215634 = 24518446380 := by
        calc
          (10 : ZMod 116454478141) ^ 14215634 = (10 : ZMod 116454478141) ^ (7107817 + 7107817) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 7107817 * (10 : ZMod 116454478141) ^ 7107817 := by rw [pow_add]
          _ = 24518446380 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 116454478141) ^ 28431269 = 33642978380 := by
        calc
          (10 : ZMod 116454478141) ^ 28431269 = (10 : ZMod 116454478141) ^ (14215634 + 14215634 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 14215634 * (10 : ZMod 116454478141) ^ 14215634) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 33642978380 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 116454478141) ^ 56862538 = 104485541473 := by
        calc
          (10 : ZMod 116454478141) ^ 56862538 = (10 : ZMod 116454478141) ^ (28431269 + 28431269) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 28431269 * (10 : ZMod 116454478141) ^ 28431269 := by rw [pow_add]
          _ = 104485541473 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 116454478141) ^ 113725076 = 114756687061 := by
        calc
          (10 : ZMod 116454478141) ^ 113725076 = (10 : ZMod 116454478141) ^ (56862538 + 56862538) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 56862538 * (10 : ZMod 116454478141) ^ 56862538 := by rw [pow_add]
          _ = 114756687061 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 116454478141) ^ 227450152 = 32571026326 := by
        calc
          (10 : ZMod 116454478141) ^ 227450152 = (10 : ZMod 116454478141) ^ (113725076 + 113725076) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 113725076 * (10 : ZMod 116454478141) ^ 113725076 := by rw [pow_add]
          _ = 32571026326 := by rw [factor_0_26]; decide
      have factor_0_28 : (10 : ZMod 116454478141) ^ 454900305 = 59600900818 := by
        calc
          (10 : ZMod 116454478141) ^ 454900305 = (10 : ZMod 116454478141) ^ (227450152 + 227450152 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 227450152 * (10 : ZMod 116454478141) ^ 227450152) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 59600900818 := by rw [factor_0_27]; decide
      have factor_0_29 : (10 : ZMod 116454478141) ^ 909800610 = 71132503344 := by
        calc
          (10 : ZMod 116454478141) ^ 909800610 = (10 : ZMod 116454478141) ^ (454900305 + 454900305) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 454900305 * (10 : ZMod 116454478141) ^ 454900305 := by rw [pow_add]
          _ = 71132503344 := by rw [factor_0_28]; decide
      have factor_0_30 : (10 : ZMod 116454478141) ^ 1819601220 = 45892272931 := by
        calc
          (10 : ZMod 116454478141) ^ 1819601220 = (10 : ZMod 116454478141) ^ (909800610 + 909800610) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 909800610 * (10 : ZMod 116454478141) ^ 909800610 := by rw [pow_add]
          _ = 45892272931 := by rw [factor_0_29]; decide
      have factor_0_31 : (10 : ZMod 116454478141) ^ 3639202441 = 104612642720 := by
        calc
          (10 : ZMod 116454478141) ^ 3639202441 = (10 : ZMod 116454478141) ^ (1819601220 + 1819601220 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1819601220 * (10 : ZMod 116454478141) ^ 1819601220) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 104612642720 := by rw [factor_0_30]; decide
      have factor_0_32 : (10 : ZMod 116454478141) ^ 7278404883 = 98272067343 := by
        calc
          (10 : ZMod 116454478141) ^ 7278404883 = (10 : ZMod 116454478141) ^ (3639202441 + 3639202441 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3639202441 * (10 : ZMod 116454478141) ^ 3639202441) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 98272067343 := by rw [factor_0_31]; decide
      have factor_0_33 : (10 : ZMod 116454478141) ^ 14556809767 = 29740054208 := by
        calc
          (10 : ZMod 116454478141) ^ 14556809767 = (10 : ZMod 116454478141) ^ (7278404883 + 7278404883 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 7278404883 * (10 : ZMod 116454478141) ^ 7278404883) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 29740054208 := by rw [factor_0_32]; decide
      have factor_0_34 : (10 : ZMod 116454478141) ^ 29113619535 = 45872425897 := by
        calc
          (10 : ZMod 116454478141) ^ 29113619535 = (10 : ZMod 116454478141) ^ (14556809767 + 14556809767 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 14556809767 * (10 : ZMod 116454478141) ^ 14556809767) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 45872425897 := by rw [factor_0_33]; decide
      have factor_0_35 : (10 : ZMod 116454478141) ^ 58227239070 = 116454478140 := by
        calc
          (10 : ZMod 116454478141) ^ 58227239070 = (10 : ZMod 116454478141) ^ (29113619535 + 29113619535) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 29113619535 * (10 : ZMod 116454478141) ^ 29113619535 := by rw [pow_add]
          _ = 116454478140 := by rw [factor_0_34]; decide
      change (10 : ZMod 116454478141) ^ 58227239070 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 116454478141) ^ 2 = 100 := by
        calc
          (10 : ZMod 116454478141) ^ 2 = (10 : ZMod 116454478141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 116454478141) ^ 4 = 10000 := by
        calc
          (10 : ZMod 116454478141) ^ 4 = (10 : ZMod 116454478141) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2 * (10 : ZMod 116454478141) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 116454478141) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 116454478141) ^ 9 = (10 : ZMod 116454478141) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4 * (10 : ZMod 116454478141) ^ 4) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 116454478141) ^ 18 = 39297238514 := by
        calc
          (10 : ZMod 116454478141) ^ 18 = (10 : ZMod 116454478141) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 9 * (10 : ZMod 116454478141) ^ 9 := by rw [pow_add]
          _ = 39297238514 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 116454478141) ^ 36 = 88405345976 := by
        calc
          (10 : ZMod 116454478141) ^ 36 = (10 : ZMod 116454478141) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 18 * (10 : ZMod 116454478141) ^ 18 := by rw [pow_add]
          _ = 88405345976 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 116454478141) ^ 72 = 42917664378 := by
        calc
          (10 : ZMod 116454478141) ^ 72 = (10 : ZMod 116454478141) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 36 * (10 : ZMod 116454478141) ^ 36 := by rw [pow_add]
          _ = 42917664378 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 116454478141) ^ 144 = 109473591517 := by
        calc
          (10 : ZMod 116454478141) ^ 144 = (10 : ZMod 116454478141) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 72 * (10 : ZMod 116454478141) ^ 72 := by rw [pow_add]
          _ = 109473591517 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 116454478141) ^ 289 = 34016220907 := by
        calc
          (10 : ZMod 116454478141) ^ 289 = (10 : ZMod 116454478141) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 144 * (10 : ZMod 116454478141) ^ 144) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 34016220907 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 116454478141) ^ 578 = 85819875906 := by
        calc
          (10 : ZMod 116454478141) ^ 578 = (10 : ZMod 116454478141) ^ (289 + 289) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 289 * (10 : ZMod 116454478141) ^ 289 := by rw [pow_add]
          _ = 85819875906 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 116454478141) ^ 1156 = 98105568979 := by
        calc
          (10 : ZMod 116454478141) ^ 1156 = (10 : ZMod 116454478141) ^ (578 + 578) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 578 * (10 : ZMod 116454478141) ^ 578 := by rw [pow_add]
          _ = 98105568979 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 116454478141) ^ 2313 = 85265950632 := by
        calc
          (10 : ZMod 116454478141) ^ 2313 = (10 : ZMod 116454478141) ^ (1156 + 1156 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1156 * (10 : ZMod 116454478141) ^ 1156) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 85265950632 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 116454478141) ^ 4627 = 89845071244 := by
        calc
          (10 : ZMod 116454478141) ^ 4627 = (10 : ZMod 116454478141) ^ (2313 + 2313 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2313 * (10 : ZMod 116454478141) ^ 2313) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 89845071244 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 116454478141) ^ 9254 = 33108506202 := by
        calc
          (10 : ZMod 116454478141) ^ 9254 = (10 : ZMod 116454478141) ^ (4627 + 4627) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 4627 * (10 : ZMod 116454478141) ^ 4627 := by rw [pow_add]
          _ = 33108506202 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 116454478141) ^ 18509 = 79929299044 := by
        calc
          (10 : ZMod 116454478141) ^ 18509 = (10 : ZMod 116454478141) ^ (9254 + 9254 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 9254 * (10 : ZMod 116454478141) ^ 9254) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 79929299044 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 116454478141) ^ 37019 = 51658330386 := by
        calc
          (10 : ZMod 116454478141) ^ 37019 = (10 : ZMod 116454478141) ^ (18509 + 18509 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 18509 * (10 : ZMod 116454478141) ^ 18509) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 51658330386 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 116454478141) ^ 74039 = 76235136619 := by
        calc
          (10 : ZMod 116454478141) ^ 74039 = (10 : ZMod 116454478141) ^ (37019 + 37019 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 37019 * (10 : ZMod 116454478141) ^ 37019) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 76235136619 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 116454478141) ^ 148079 = 5919824182 := by
        calc
          (10 : ZMod 116454478141) ^ 148079 = (10 : ZMod 116454478141) ^ (74039 + 74039 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 74039 * (10 : ZMod 116454478141) ^ 74039) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 5919824182 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 116454478141) ^ 296159 = 115950147826 := by
        calc
          (10 : ZMod 116454478141) ^ 296159 = (10 : ZMod 116454478141) ^ (148079 + 148079 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 148079 * (10 : ZMod 116454478141) ^ 148079) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 115950147826 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 116454478141) ^ 592318 = 25738894138 := by
        calc
          (10 : ZMod 116454478141) ^ 592318 = (10 : ZMod 116454478141) ^ (296159 + 296159) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 296159 * (10 : ZMod 116454478141) ^ 296159 := by rw [pow_add]
          _ = 25738894138 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 116454478141) ^ 1184636 = 98214137931 := by
        calc
          (10 : ZMod 116454478141) ^ 1184636 = (10 : ZMod 116454478141) ^ (592318 + 592318) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 592318 * (10 : ZMod 116454478141) ^ 592318 := by rw [pow_add]
          _ = 98214137931 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 116454478141) ^ 2369272 = 21910050479 := by
        calc
          (10 : ZMod 116454478141) ^ 2369272 = (10 : ZMod 116454478141) ^ (1184636 + 1184636) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1184636 * (10 : ZMod 116454478141) ^ 1184636 := by rw [pow_add]
          _ = 21910050479 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 116454478141) ^ 4738544 = 44731422948 := by
        calc
          (10 : ZMod 116454478141) ^ 4738544 = (10 : ZMod 116454478141) ^ (2369272 + 2369272) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2369272 * (10 : ZMod 116454478141) ^ 2369272 := by rw [pow_add]
          _ = 44731422948 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 116454478141) ^ 9477089 = 18114564790 := by
        calc
          (10 : ZMod 116454478141) ^ 9477089 = (10 : ZMod 116454478141) ^ (4738544 + 4738544 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4738544 * (10 : ZMod 116454478141) ^ 4738544) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 18114564790 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 116454478141) ^ 18954179 = 83541567552 := by
        calc
          (10 : ZMod 116454478141) ^ 18954179 = (10 : ZMod 116454478141) ^ (9477089 + 9477089 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 9477089 * (10 : ZMod 116454478141) ^ 9477089) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 83541567552 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 116454478141) ^ 37908358 = 21363806244 := by
        calc
          (10 : ZMod 116454478141) ^ 37908358 = (10 : ZMod 116454478141) ^ (18954179 + 18954179) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 18954179 * (10 : ZMod 116454478141) ^ 18954179 := by rw [pow_add]
          _ = 21363806244 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 116454478141) ^ 75816717 = 47870871157 := by
        calc
          (10 : ZMod 116454478141) ^ 75816717 = (10 : ZMod 116454478141) ^ (37908358 + 37908358 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 37908358 * (10 : ZMod 116454478141) ^ 37908358) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 47870871157 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 116454478141) ^ 151633435 = 5171473413 := by
        calc
          (10 : ZMod 116454478141) ^ 151633435 = (10 : ZMod 116454478141) ^ (75816717 + 75816717 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 75816717 * (10 : ZMod 116454478141) ^ 75816717) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 5171473413 := by rw [factor_1_26]; decide
      have factor_1_28 : (10 : ZMod 116454478141) ^ 303266870 = 106951465124 := by
        calc
          (10 : ZMod 116454478141) ^ 303266870 = (10 : ZMod 116454478141) ^ (151633435 + 151633435) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 151633435 * (10 : ZMod 116454478141) ^ 151633435 := by rw [pow_add]
          _ = 106951465124 := by rw [factor_1_27]; decide
      have factor_1_29 : (10 : ZMod 116454478141) ^ 606533740 = 37899396394 := by
        calc
          (10 : ZMod 116454478141) ^ 606533740 = (10 : ZMod 116454478141) ^ (303266870 + 303266870) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 303266870 * (10 : ZMod 116454478141) ^ 303266870 := by rw [pow_add]
          _ = 37899396394 := by rw [factor_1_28]; decide
      have factor_1_30 : (10 : ZMod 116454478141) ^ 1213067480 = 80951000450 := by
        calc
          (10 : ZMod 116454478141) ^ 1213067480 = (10 : ZMod 116454478141) ^ (606533740 + 606533740) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 606533740 * (10 : ZMod 116454478141) ^ 606533740 := by rw [pow_add]
          _ = 80951000450 := by rw [factor_1_29]; decide
      have factor_1_31 : (10 : ZMod 116454478141) ^ 2426134961 = 92841361228 := by
        calc
          (10 : ZMod 116454478141) ^ 2426134961 = (10 : ZMod 116454478141) ^ (1213067480 + 1213067480 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1213067480 * (10 : ZMod 116454478141) ^ 1213067480) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 92841361228 := by rw [factor_1_30]; decide
      have factor_1_32 : (10 : ZMod 116454478141) ^ 4852269922 = 1243367946 := by
        calc
          (10 : ZMod 116454478141) ^ 4852269922 = (10 : ZMod 116454478141) ^ (2426134961 + 2426134961) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2426134961 * (10 : ZMod 116454478141) ^ 2426134961 := by rw [pow_add]
          _ = 1243367946 := by rw [factor_1_31]; decide
      have factor_1_33 : (10 : ZMod 116454478141) ^ 9704539845 = 9998372048 := by
        calc
          (10 : ZMod 116454478141) ^ 9704539845 = (10 : ZMod 116454478141) ^ (4852269922 + 4852269922 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4852269922 * (10 : ZMod 116454478141) ^ 4852269922) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 9998372048 := by rw [factor_1_32]; decide
      have factor_1_34 : (10 : ZMod 116454478141) ^ 19409079690 = 60226319434 := by
        calc
          (10 : ZMod 116454478141) ^ 19409079690 = (10 : ZMod 116454478141) ^ (9704539845 + 9704539845) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 9704539845 * (10 : ZMod 116454478141) ^ 9704539845 := by rw [pow_add]
          _ = 60226319434 := by rw [factor_1_33]; decide
      have factor_1_35 : (10 : ZMod 116454478141) ^ 38818159380 = 60226319433 := by
        calc
          (10 : ZMod 116454478141) ^ 38818159380 = (10 : ZMod 116454478141) ^ (19409079690 + 19409079690) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 19409079690 * (10 : ZMod 116454478141) ^ 19409079690 := by rw [pow_add]
          _ = 60226319433 := by rw [factor_1_34]; decide
      change (10 : ZMod 116454478141) ^ 38818159380 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 116454478141) ^ 2 = 100 := by
        calc
          (10 : ZMod 116454478141) ^ 2 = (10 : ZMod 116454478141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 116454478141) ^ 5 = 100000 := by
        calc
          (10 : ZMod 116454478141) ^ 5 = (10 : ZMod 116454478141) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2 * (10 : ZMod 116454478141) ^ 2) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 116454478141) ^ 10 = 10000000000 := by
        calc
          (10 : ZMod 116454478141) ^ 10 = (10 : ZMod 116454478141) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 5 * (10 : ZMod 116454478141) ^ 5 := by rw [pow_add]
          _ = 10000000000 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 116454478141) ^ 21 = 52079380483 := by
        calc
          (10 : ZMod 116454478141) ^ 21 = (10 : ZMod 116454478141) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 10 * (10 : ZMod 116454478141) ^ 10) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 52079380483 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 116454478141) ^ 43 = 2764587472 := by
        calc
          (10 : ZMod 116454478141) ^ 43 = (10 : ZMod 116454478141) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 21 * (10 : ZMod 116454478141) ^ 21) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 2764587472 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 116454478141) ^ 86 = 39693862651 := by
        calc
          (10 : ZMod 116454478141) ^ 86 = (10 : ZMod 116454478141) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 43 * (10 : ZMod 116454478141) ^ 43 := by rw [pow_add]
          _ = 39693862651 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 116454478141) ^ 173 = 41786090746 := by
        calc
          (10 : ZMod 116454478141) ^ 173 = (10 : ZMod 116454478141) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 86 * (10 : ZMod 116454478141) ^ 86) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 41786090746 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 116454478141) ^ 347 = 109378320447 := by
        calc
          (10 : ZMod 116454478141) ^ 347 = (10 : ZMod 116454478141) ^ (173 + 173 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 173 * (10 : ZMod 116454478141) ^ 173) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 109378320447 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 116454478141) ^ 694 = 48658835986 := by
        calc
          (10 : ZMod 116454478141) ^ 694 = (10 : ZMod 116454478141) ^ (347 + 347) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 347 * (10 : ZMod 116454478141) ^ 347 := by rw [pow_add]
          _ = 48658835986 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 116454478141) ^ 1388 = 917883806 := by
        calc
          (10 : ZMod 116454478141) ^ 1388 = (10 : ZMod 116454478141) ^ (694 + 694) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 694 * (10 : ZMod 116454478141) ^ 694 := by rw [pow_add]
          _ = 917883806 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 116454478141) ^ 2776 = 30308872038 := by
        calc
          (10 : ZMod 116454478141) ^ 2776 = (10 : ZMod 116454478141) ^ (1388 + 1388) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1388 * (10 : ZMod 116454478141) ^ 1388 := by rw [pow_add]
          _ = 30308872038 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 116454478141) ^ 5552 = 82129485850 := by
        calc
          (10 : ZMod 116454478141) ^ 5552 = (10 : ZMod 116454478141) ^ (2776 + 2776) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2776 * (10 : ZMod 116454478141) ^ 2776 := by rw [pow_add]
          _ = 82129485850 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 116454478141) ^ 11105 = 64426343926 := by
        calc
          (10 : ZMod 116454478141) ^ 11105 = (10 : ZMod 116454478141) ^ (5552 + 5552 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 5552 * (10 : ZMod 116454478141) ^ 5552) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 64426343926 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 116454478141) ^ 22211 = 18176349156 := by
        calc
          (10 : ZMod 116454478141) ^ 22211 = (10 : ZMod 116454478141) ^ (11105 + 11105 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 11105 * (10 : ZMod 116454478141) ^ 11105) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 18176349156 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 116454478141) ^ 44423 = 80577205225 := by
        calc
          (10 : ZMod 116454478141) ^ 44423 = (10 : ZMod 116454478141) ^ (22211 + 22211 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 22211 * (10 : ZMod 116454478141) ^ 22211) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 80577205225 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 116454478141) ^ 88847 = 78858327225 := by
        calc
          (10 : ZMod 116454478141) ^ 88847 = (10 : ZMod 116454478141) ^ (44423 + 44423 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 44423 * (10 : ZMod 116454478141) ^ 44423) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 78858327225 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 116454478141) ^ 177695 = 114023840490 := by
        calc
          (10 : ZMod 116454478141) ^ 177695 = (10 : ZMod 116454478141) ^ (88847 + 88847 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 88847 * (10 : ZMod 116454478141) ^ 88847) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 114023840490 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 116454478141) ^ 355390 = 61427356577 := by
        calc
          (10 : ZMod 116454478141) ^ 355390 = (10 : ZMod 116454478141) ^ (177695 + 177695) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 177695 * (10 : ZMod 116454478141) ^ 177695 := by rw [pow_add]
          _ = 61427356577 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 116454478141) ^ 710781 = 93273427009 := by
        calc
          (10 : ZMod 116454478141) ^ 710781 = (10 : ZMod 116454478141) ^ (355390 + 355390 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 355390 * (10 : ZMod 116454478141) ^ 355390) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 93273427009 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 116454478141) ^ 1421563 = 67888549352 := by
        calc
          (10 : ZMod 116454478141) ^ 1421563 = (10 : ZMod 116454478141) ^ (710781 + 710781 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 710781 * (10 : ZMod 116454478141) ^ 710781) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 67888549352 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 116454478141) ^ 2843126 = 78461784714 := by
        calc
          (10 : ZMod 116454478141) ^ 2843126 = (10 : ZMod 116454478141) ^ (1421563 + 1421563) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1421563 * (10 : ZMod 116454478141) ^ 1421563 := by rw [pow_add]
          _ = 78461784714 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 116454478141) ^ 5686253 = 60628566043 := by
        calc
          (10 : ZMod 116454478141) ^ 5686253 = (10 : ZMod 116454478141) ^ (2843126 + 2843126 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2843126 * (10 : ZMod 116454478141) ^ 2843126) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 60628566043 := by rw [factor_2_21]; decide
      have factor_2_23 : (10 : ZMod 116454478141) ^ 11372507 = 106100518004 := by
        calc
          (10 : ZMod 116454478141) ^ 11372507 = (10 : ZMod 116454478141) ^ (5686253 + 5686253 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 5686253 * (10 : ZMod 116454478141) ^ 5686253) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 106100518004 := by rw [factor_2_22]; decide
      have factor_2_24 : (10 : ZMod 116454478141) ^ 22745015 = 76289061774 := by
        calc
          (10 : ZMod 116454478141) ^ 22745015 = (10 : ZMod 116454478141) ^ (11372507 + 11372507 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 11372507 * (10 : ZMod 116454478141) ^ 11372507) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 76289061774 := by rw [factor_2_23]; decide
      have factor_2_25 : (10 : ZMod 116454478141) ^ 45490030 = 32901322385 := by
        calc
          (10 : ZMod 116454478141) ^ 45490030 = (10 : ZMod 116454478141) ^ (22745015 + 22745015) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 22745015 * (10 : ZMod 116454478141) ^ 22745015 := by rw [pow_add]
          _ = 32901322385 := by rw [factor_2_24]; decide
      have factor_2_26 : (10 : ZMod 116454478141) ^ 90980061 = 23345070718 := by
        calc
          (10 : ZMod 116454478141) ^ 90980061 = (10 : ZMod 116454478141) ^ (45490030 + 45490030 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 45490030 * (10 : ZMod 116454478141) ^ 45490030) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 23345070718 := by rw [factor_2_25]; decide
      have factor_2_27 : (10 : ZMod 116454478141) ^ 181960122 = 3356758200 := by
        calc
          (10 : ZMod 116454478141) ^ 181960122 = (10 : ZMod 116454478141) ^ (90980061 + 90980061) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 90980061 * (10 : ZMod 116454478141) ^ 90980061 := by rw [pow_add]
          _ = 3356758200 := by rw [factor_2_26]; decide
      have factor_2_28 : (10 : ZMod 116454478141) ^ 363920244 = 77255935060 := by
        calc
          (10 : ZMod 116454478141) ^ 363920244 = (10 : ZMod 116454478141) ^ (181960122 + 181960122) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 181960122 * (10 : ZMod 116454478141) ^ 181960122 := by rw [pow_add]
          _ = 77255935060 := by rw [factor_2_27]; decide
      have factor_2_29 : (10 : ZMod 116454478141) ^ 727840488 = 85519720973 := by
        calc
          (10 : ZMod 116454478141) ^ 727840488 = (10 : ZMod 116454478141) ^ (363920244 + 363920244) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 363920244 * (10 : ZMod 116454478141) ^ 363920244 := by rw [pow_add]
          _ = 85519720973 := by rw [factor_2_28]; decide
      have factor_2_30 : (10 : ZMod 116454478141) ^ 1455680976 = 47023550942 := by
        calc
          (10 : ZMod 116454478141) ^ 1455680976 = (10 : ZMod 116454478141) ^ (727840488 + 727840488) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 727840488 * (10 : ZMod 116454478141) ^ 727840488 := by rw [pow_add]
          _ = 47023550942 := by rw [factor_2_29]; decide
      have factor_2_31 : (10 : ZMod 116454478141) ^ 2911361953 = 49183775570 := by
        calc
          (10 : ZMod 116454478141) ^ 2911361953 = (10 : ZMod 116454478141) ^ (1455680976 + 1455680976 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1455680976 * (10 : ZMod 116454478141) ^ 1455680976) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 49183775570 := by rw [factor_2_30]; decide
      have factor_2_32 : (10 : ZMod 116454478141) ^ 5822723907 = 41183469327 := by
        calc
          (10 : ZMod 116454478141) ^ 5822723907 = (10 : ZMod 116454478141) ^ (2911361953 + 2911361953 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2911361953 * (10 : ZMod 116454478141) ^ 2911361953) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 41183469327 := by rw [factor_2_31]; decide
      have factor_2_33 : (10 : ZMod 116454478141) ^ 11645447814 = 114638641240 := by
        calc
          (10 : ZMod 116454478141) ^ 11645447814 = (10 : ZMod 116454478141) ^ (5822723907 + 5822723907) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 5822723907 * (10 : ZMod 116454478141) ^ 5822723907 := by rw [pow_add]
          _ = 114638641240 := by rw [factor_2_32]; decide
      have factor_2_34 : (10 : ZMod 116454478141) ^ 23290895628 = 88296154346 := by
        calc
          (10 : ZMod 116454478141) ^ 23290895628 = (10 : ZMod 116454478141) ^ (11645447814 + 11645447814) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 11645447814 * (10 : ZMod 116454478141) ^ 11645447814 := by rw [pow_add]
          _ = 88296154346 := by rw [factor_2_33]; decide
      change (10 : ZMod 116454478141) ^ 23290895628 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 116454478141) ^ 3 = 1000 := by
        calc
          (10 : ZMod 116454478141) ^ 3 = (10 : ZMod 116454478141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 116454478141) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 116454478141) ^ 7 = (10 : ZMod 116454478141) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3 * (10 : ZMod 116454478141) ^ 3) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 116454478141) ^ 15 = 5396203233 := by
        calc
          (10 : ZMod 116454478141) ^ 15 = (10 : ZMod 116454478141) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 7 * (10 : ZMod 116454478141) ^ 7) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 5396203233 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 116454478141) ^ 30 = 50432330527 := by
        calc
          (10 : ZMod 116454478141) ^ 30 = (10 : ZMod 116454478141) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 15 * (10 : ZMod 116454478141) ^ 15 := by rw [pow_add]
          _ = 50432330527 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 116454478141) ^ 61 = 98508675065 := by
        calc
          (10 : ZMod 116454478141) ^ 61 = (10 : ZMod 116454478141) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 30 * (10 : ZMod 116454478141) ^ 30) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 98508675065 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 116454478141) ^ 123 = 2404361258 := by
        calc
          (10 : ZMod 116454478141) ^ 123 = (10 : ZMod 116454478141) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 61 * (10 : ZMod 116454478141) ^ 61) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 2404361258 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 116454478141) ^ 247 = 107131250143 := by
        calc
          (10 : ZMod 116454478141) ^ 247 = (10 : ZMod 116454478141) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 123 * (10 : ZMod 116454478141) ^ 123) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 107131250143 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 116454478141) ^ 495 = 34568739072 := by
        calc
          (10 : ZMod 116454478141) ^ 495 = (10 : ZMod 116454478141) ^ (247 + 247 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 247 * (10 : ZMod 116454478141) ^ 247) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 34568739072 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 116454478141) ^ 991 = 13292870764 := by
        calc
          (10 : ZMod 116454478141) ^ 991 = (10 : ZMod 116454478141) ^ (495 + 495 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 495 * (10 : ZMod 116454478141) ^ 495) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 13292870764 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 116454478141) ^ 1983 = 59889910905 := by
        calc
          (10 : ZMod 116454478141) ^ 1983 = (10 : ZMod 116454478141) ^ (991 + 991 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 991 * (10 : ZMod 116454478141) ^ 991) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 59889910905 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 116454478141) ^ 3966 = 29243653578 := by
        calc
          (10 : ZMod 116454478141) ^ 3966 = (10 : ZMod 116454478141) ^ (1983 + 1983) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1983 * (10 : ZMod 116454478141) ^ 1983 := by rw [pow_add]
          _ = 29243653578 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 116454478141) ^ 7932 = 33246484702 := by
        calc
          (10 : ZMod 116454478141) ^ 7932 = (10 : ZMod 116454478141) ^ (3966 + 3966) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3966 * (10 : ZMod 116454478141) ^ 3966 := by rw [pow_add]
          _ = 33246484702 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 116454478141) ^ 15865 = 85709258143 := by
        calc
          (10 : ZMod 116454478141) ^ 15865 = (10 : ZMod 116454478141) ^ (7932 + 7932 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 7932 * (10 : ZMod 116454478141) ^ 7932) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 85709258143 := by rw [factor_3_12]; decide
      have factor_3_14 : (10 : ZMod 116454478141) ^ 31731 = 98792212505 := by
        calc
          (10 : ZMod 116454478141) ^ 31731 = (10 : ZMod 116454478141) ^ (15865 + 15865 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 15865 * (10 : ZMod 116454478141) ^ 15865) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 98792212505 := by rw [factor_3_13]; decide
      have factor_3_15 : (10 : ZMod 116454478141) ^ 63462 = 79450761289 := by
        calc
          (10 : ZMod 116454478141) ^ 63462 = (10 : ZMod 116454478141) ^ (31731 + 31731) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 31731 * (10 : ZMod 116454478141) ^ 31731 := by rw [pow_add]
          _ = 79450761289 := by rw [factor_3_14]; decide
      have factor_3_16 : (10 : ZMod 116454478141) ^ 126925 = 48131546257 := by
        calc
          (10 : ZMod 116454478141) ^ 126925 = (10 : ZMod 116454478141) ^ (63462 + 63462 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 63462 * (10 : ZMod 116454478141) ^ 63462) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 48131546257 := by rw [factor_3_15]; decide
      have factor_3_17 : (10 : ZMod 116454478141) ^ 253850 = 62353275289 := by
        calc
          (10 : ZMod 116454478141) ^ 253850 = (10 : ZMod 116454478141) ^ (126925 + 126925) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 126925 * (10 : ZMod 116454478141) ^ 126925 := by rw [pow_add]
          _ = 62353275289 := by rw [factor_3_16]; decide
      have factor_3_18 : (10 : ZMod 116454478141) ^ 507701 = 81781602808 := by
        calc
          (10 : ZMod 116454478141) ^ 507701 = (10 : ZMod 116454478141) ^ (253850 + 253850 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 253850 * (10 : ZMod 116454478141) ^ 253850) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 81781602808 := by rw [factor_3_17]; decide
      have factor_3_19 : (10 : ZMod 116454478141) ^ 1015402 = 87279169049 := by
        calc
          (10 : ZMod 116454478141) ^ 1015402 = (10 : ZMod 116454478141) ^ (507701 + 507701) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 507701 * (10 : ZMod 116454478141) ^ 507701 := by rw [pow_add]
          _ = 87279169049 := by rw [factor_3_18]; decide
      have factor_3_20 : (10 : ZMod 116454478141) ^ 2030804 = 7356056383 := by
        calc
          (10 : ZMod 116454478141) ^ 2030804 = (10 : ZMod 116454478141) ^ (1015402 + 1015402) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1015402 * (10 : ZMod 116454478141) ^ 1015402 := by rw [pow_add]
          _ = 7356056383 := by rw [factor_3_19]; decide
      have factor_3_21 : (10 : ZMod 116454478141) ^ 4061609 = 29238401126 := by
        calc
          (10 : ZMod 116454478141) ^ 4061609 = (10 : ZMod 116454478141) ^ (2030804 + 2030804 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2030804 * (10 : ZMod 116454478141) ^ 2030804) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 29238401126 := by rw [factor_3_20]; decide
      have factor_3_22 : (10 : ZMod 116454478141) ^ 8123219 = 27436074307 := by
        calc
          (10 : ZMod 116454478141) ^ 8123219 = (10 : ZMod 116454478141) ^ (4061609 + 4061609 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4061609 * (10 : ZMod 116454478141) ^ 4061609) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 27436074307 := by rw [factor_3_21]; decide
      have factor_3_23 : (10 : ZMod 116454478141) ^ 16246439 = 84755656163 := by
        calc
          (10 : ZMod 116454478141) ^ 16246439 = (10 : ZMod 116454478141) ^ (8123219 + 8123219 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 8123219 * (10 : ZMod 116454478141) ^ 8123219) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 84755656163 := by rw [factor_3_22]; decide
      have factor_3_24 : (10 : ZMod 116454478141) ^ 32492878 = 81930739296 := by
        calc
          (10 : ZMod 116454478141) ^ 32492878 = (10 : ZMod 116454478141) ^ (16246439 + 16246439) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 16246439 * (10 : ZMod 116454478141) ^ 16246439 := by rw [pow_add]
          _ = 81930739296 := by rw [factor_3_23]; decide
      have factor_3_25 : (10 : ZMod 116454478141) ^ 64985757 = 8547401700 := by
        calc
          (10 : ZMod 116454478141) ^ 64985757 = (10 : ZMod 116454478141) ^ (32492878 + 32492878 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 32492878 * (10 : ZMod 116454478141) ^ 32492878) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 8547401700 := by rw [factor_3_24]; decide
      have factor_3_26 : (10 : ZMod 116454478141) ^ 129971515 = 1231181816 := by
        calc
          (10 : ZMod 116454478141) ^ 129971515 = (10 : ZMod 116454478141) ^ (64985757 + 64985757 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 64985757 * (10 : ZMod 116454478141) ^ 64985757) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1231181816 := by rw [factor_3_25]; decide
      have factor_3_27 : (10 : ZMod 116454478141) ^ 259943031 = 42963792488 := by
        calc
          (10 : ZMod 116454478141) ^ 259943031 = (10 : ZMod 116454478141) ^ (129971515 + 129971515 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 129971515 * (10 : ZMod 116454478141) ^ 129971515) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 42963792488 := by rw [factor_3_26]; decide
      have factor_3_28 : (10 : ZMod 116454478141) ^ 519886063 = 64214360208 := by
        calc
          (10 : ZMod 116454478141) ^ 519886063 = (10 : ZMod 116454478141) ^ (259943031 + 259943031 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 259943031 * (10 : ZMod 116454478141) ^ 259943031) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 64214360208 := by rw [factor_3_27]; decide
      have factor_3_29 : (10 : ZMod 116454478141) ^ 1039772126 = 60633137076 := by
        calc
          (10 : ZMod 116454478141) ^ 1039772126 = (10 : ZMod 116454478141) ^ (519886063 + 519886063) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 519886063 * (10 : ZMod 116454478141) ^ 519886063 := by rw [pow_add]
          _ = 60633137076 := by rw [factor_3_28]; decide
      have factor_3_30 : (10 : ZMod 116454478141) ^ 2079544252 = 36106219387 := by
        calc
          (10 : ZMod 116454478141) ^ 2079544252 = (10 : ZMod 116454478141) ^ (1039772126 + 1039772126) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1039772126 * (10 : ZMod 116454478141) ^ 1039772126 := by rw [pow_add]
          _ = 36106219387 := by rw [factor_3_29]; decide
      have factor_3_31 : (10 : ZMod 116454478141) ^ 4159088505 = 52331680104 := by
        calc
          (10 : ZMod 116454478141) ^ 4159088505 = (10 : ZMod 116454478141) ^ (2079544252 + 2079544252 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2079544252 * (10 : ZMod 116454478141) ^ 2079544252) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 52331680104 := by rw [factor_3_30]; decide
      have factor_3_32 : (10 : ZMod 116454478141) ^ 8318177010 = 100573915773 := by
        calc
          (10 : ZMod 116454478141) ^ 8318177010 = (10 : ZMod 116454478141) ^ (4159088505 + 4159088505) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 4159088505 * (10 : ZMod 116454478141) ^ 4159088505 := by rw [pow_add]
          _ = 100573915773 := by rw [factor_3_31]; decide
      have factor_3_33 : (10 : ZMod 116454478141) ^ 16636354020 = 25251956312 := by
        calc
          (10 : ZMod 116454478141) ^ 16636354020 = (10 : ZMod 116454478141) ^ (8318177010 + 8318177010) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 8318177010 * (10 : ZMod 116454478141) ^ 8318177010 := by rw [pow_add]
          _ = 25251956312 := by rw [factor_3_32]; decide
      change (10 : ZMod 116454478141) ^ 16636354020 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_4_1 : (10 : ZMod 116454478141) ^ 2 = 100 := by
        calc
          (10 : ZMod 116454478141) ^ 2 = (10 : ZMod 116454478141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_4_0]; decide
      have factor_4_2 : (10 : ZMod 116454478141) ^ 4 = 10000 := by
        calc
          (10 : ZMod 116454478141) ^ 4 = (10 : ZMod 116454478141) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2 * (10 : ZMod 116454478141) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_4_1]; decide
      have factor_4_3 : (10 : ZMod 116454478141) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 116454478141) ^ 9 = (10 : ZMod 116454478141) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4 * (10 : ZMod 116454478141) ^ 4) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [factor_4_2]; decide
      have factor_4_4 : (10 : ZMod 116454478141) ^ 19 = 43608950717 := by
        calc
          (10 : ZMod 116454478141) ^ 19 = (10 : ZMod 116454478141) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 9 * (10 : ZMod 116454478141) ^ 9) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 43608950717 := by rw [factor_4_3]; decide
      have factor_4_5 : (10 : ZMod 116454478141) ^ 39 = 16397066981 := by
        calc
          (10 : ZMod 116454478141) ^ 39 = (10 : ZMod 116454478141) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 19 * (10 : ZMod 116454478141) ^ 19) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 16397066981 := by rw [factor_4_4]; decide
      have factor_4_6 : (10 : ZMod 116454478141) ^ 78 = 113276306565 := by
        calc
          (10 : ZMod 116454478141) ^ 78 = (10 : ZMod 116454478141) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 39 * (10 : ZMod 116454478141) ^ 39 := by rw [pow_add]
          _ = 113276306565 := by rw [factor_4_5]; decide
      have factor_4_7 : (10 : ZMod 116454478141) ^ 157 = 54261956688 := by
        calc
          (10 : ZMod 116454478141) ^ 157 = (10 : ZMod 116454478141) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 78 * (10 : ZMod 116454478141) ^ 78) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 54261956688 := by rw [factor_4_6]; decide
      have factor_4_8 : (10 : ZMod 116454478141) ^ 315 = 6812240881 := by
        calc
          (10 : ZMod 116454478141) ^ 315 = (10 : ZMod 116454478141) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 157 * (10 : ZMod 116454478141) ^ 157) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 6812240881 := by rw [factor_4_7]; decide
      have factor_4_9 : (10 : ZMod 116454478141) ^ 631 = 101904582468 := by
        calc
          (10 : ZMod 116454478141) ^ 631 = (10 : ZMod 116454478141) ^ (315 + 315 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 315 * (10 : ZMod 116454478141) ^ 315) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 101904582468 := by rw [factor_4_8]; decide
      have factor_4_10 : (10 : ZMod 116454478141) ^ 1262 = 92940868842 := by
        calc
          (10 : ZMod 116454478141) ^ 1262 = (10 : ZMod 116454478141) ^ (631 + 631) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 631 * (10 : ZMod 116454478141) ^ 631 := by rw [pow_add]
          _ = 92940868842 := by rw [factor_4_9]; decide
      have factor_4_11 : (10 : ZMod 116454478141) ^ 2524 = 35082913658 := by
        calc
          (10 : ZMod 116454478141) ^ 2524 = (10 : ZMod 116454478141) ^ (1262 + 1262) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1262 * (10 : ZMod 116454478141) ^ 1262 := by rw [pow_add]
          _ = 35082913658 := by rw [factor_4_10]; decide
      have factor_4_12 : (10 : ZMod 116454478141) ^ 5048 = 17539754288 := by
        calc
          (10 : ZMod 116454478141) ^ 5048 = (10 : ZMod 116454478141) ^ (2524 + 2524) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2524 * (10 : ZMod 116454478141) ^ 2524 := by rw [pow_add]
          _ = 17539754288 := by rw [factor_4_11]; decide
      have factor_4_13 : (10 : ZMod 116454478141) ^ 10096 = 93332024496 := by
        calc
          (10 : ZMod 116454478141) ^ 10096 = (10 : ZMod 116454478141) ^ (5048 + 5048) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 5048 * (10 : ZMod 116454478141) ^ 5048 := by rw [pow_add]
          _ = 93332024496 := by rw [factor_4_12]; decide
      have factor_4_14 : (10 : ZMod 116454478141) ^ 20192 = 7482644255 := by
        calc
          (10 : ZMod 116454478141) ^ 20192 = (10 : ZMod 116454478141) ^ (10096 + 10096) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 10096 * (10 : ZMod 116454478141) ^ 10096 := by rw [pow_add]
          _ = 7482644255 := by rw [factor_4_13]; decide
      have factor_4_15 : (10 : ZMod 116454478141) ^ 40385 = 104397696128 := by
        calc
          (10 : ZMod 116454478141) ^ 40385 = (10 : ZMod 116454478141) ^ (20192 + 20192 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 20192 * (10 : ZMod 116454478141) ^ 20192) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 104397696128 := by rw [factor_4_14]; decide
      have factor_4_16 : (10 : ZMod 116454478141) ^ 80770 = 65655821836 := by
        calc
          (10 : ZMod 116454478141) ^ 80770 = (10 : ZMod 116454478141) ^ (40385 + 40385) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 40385 * (10 : ZMod 116454478141) ^ 40385 := by rw [pow_add]
          _ = 65655821836 := by rw [factor_4_15]; decide
      have factor_4_17 : (10 : ZMod 116454478141) ^ 161541 = 66390316398 := by
        calc
          (10 : ZMod 116454478141) ^ 161541 = (10 : ZMod 116454478141) ^ (80770 + 80770 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 80770 * (10 : ZMod 116454478141) ^ 80770) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 66390316398 := by rw [factor_4_16]; decide
      have factor_4_18 : (10 : ZMod 116454478141) ^ 323082 = 21685405669 := by
        calc
          (10 : ZMod 116454478141) ^ 323082 = (10 : ZMod 116454478141) ^ (161541 + 161541) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 161541 * (10 : ZMod 116454478141) ^ 161541 := by rw [pow_add]
          _ = 21685405669 := by rw [factor_4_17]; decide
      have factor_4_19 : (10 : ZMod 116454478141) ^ 646165 = 3941780955 := by
        calc
          (10 : ZMod 116454478141) ^ 646165 = (10 : ZMod 116454478141) ^ (323082 + 323082 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 323082 * (10 : ZMod 116454478141) ^ 323082) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 3941780955 := by rw [factor_4_18]; decide
      have factor_4_20 : (10 : ZMod 116454478141) ^ 1292330 = 84790650356 := by
        calc
          (10 : ZMod 116454478141) ^ 1292330 = (10 : ZMod 116454478141) ^ (646165 + 646165) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 646165 * (10 : ZMod 116454478141) ^ 646165 := by rw [pow_add]
          _ = 84790650356 := by rw [factor_4_19]; decide
      have factor_4_21 : (10 : ZMod 116454478141) ^ 2584660 = 110101129248 := by
        calc
          (10 : ZMod 116454478141) ^ 2584660 = (10 : ZMod 116454478141) ^ (1292330 + 1292330) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1292330 * (10 : ZMod 116454478141) ^ 1292330 := by rw [pow_add]
          _ = 110101129248 := by rw [factor_4_20]; decide
      have factor_4_22 : (10 : ZMod 116454478141) ^ 5169321 = 9508235256 := by
        calc
          (10 : ZMod 116454478141) ^ 5169321 = (10 : ZMod 116454478141) ^ (2584660 + 2584660 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2584660 * (10 : ZMod 116454478141) ^ 2584660) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 9508235256 := by rw [factor_4_21]; decide
      have factor_4_23 : (10 : ZMod 116454478141) ^ 10338643 = 111654628598 := by
        calc
          (10 : ZMod 116454478141) ^ 10338643 = (10 : ZMod 116454478141) ^ (5169321 + 5169321 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 5169321 * (10 : ZMod 116454478141) ^ 5169321) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 111654628598 := by rw [factor_4_22]; decide
      have factor_4_24 : (10 : ZMod 116454478141) ^ 20677286 = 91924003545 := by
        calc
          (10 : ZMod 116454478141) ^ 20677286 = (10 : ZMod 116454478141) ^ (10338643 + 10338643) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 10338643 * (10 : ZMod 116454478141) ^ 10338643 := by rw [pow_add]
          _ = 91924003545 := by rw [factor_4_23]; decide
      have factor_4_25 : (10 : ZMod 116454478141) ^ 41354573 = 95028201696 := by
        calc
          (10 : ZMod 116454478141) ^ 41354573 = (10 : ZMod 116454478141) ^ (20677286 + 20677286 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 20677286 * (10 : ZMod 116454478141) ^ 20677286) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 95028201696 := by rw [factor_4_24]; decide
      have factor_4_26 : (10 : ZMod 116454478141) ^ 82709146 = 47868550190 := by
        calc
          (10 : ZMod 116454478141) ^ 82709146 = (10 : ZMod 116454478141) ^ (41354573 + 41354573) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 41354573 * (10 : ZMod 116454478141) ^ 41354573 := by rw [pow_add]
          _ = 47868550190 := by rw [factor_4_25]; decide
      have factor_4_27 : (10 : ZMod 116454478141) ^ 165418292 = 115229901142 := by
        calc
          (10 : ZMod 116454478141) ^ 165418292 = (10 : ZMod 116454478141) ^ (82709146 + 82709146) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 82709146 * (10 : ZMod 116454478141) ^ 82709146 := by rw [pow_add]
          _ = 115229901142 := by rw [factor_4_26]; decide
      have factor_4_28 : (10 : ZMod 116454478141) ^ 330836585 = 46698849443 := by
        calc
          (10 : ZMod 116454478141) ^ 330836585 = (10 : ZMod 116454478141) ^ (165418292 + 165418292 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 165418292 * (10 : ZMod 116454478141) ^ 165418292) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 46698849443 := by rw [factor_4_27]; decide
      have factor_4_29 : (10 : ZMod 116454478141) ^ 661673171 = 75377987802 := by
        calc
          (10 : ZMod 116454478141) ^ 661673171 = (10 : ZMod 116454478141) ^ (330836585 + 330836585 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 330836585 * (10 : ZMod 116454478141) ^ 330836585) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 75377987802 := by rw [factor_4_28]; decide
      have factor_4_30 : (10 : ZMod 116454478141) ^ 1323346342 = 11437423828 := by
        calc
          (10 : ZMod 116454478141) ^ 1323346342 = (10 : ZMod 116454478141) ^ (661673171 + 661673171) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 661673171 * (10 : ZMod 116454478141) ^ 661673171 := by rw [pow_add]
          _ = 11437423828 := by rw [factor_4_29]; decide
      have factor_4_31 : (10 : ZMod 116454478141) ^ 2646692685 = 59508964322 := by
        calc
          (10 : ZMod 116454478141) ^ 2646692685 = (10 : ZMod 116454478141) ^ (1323346342 + 1323346342 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1323346342 * (10 : ZMod 116454478141) ^ 1323346342) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 59508964322 := by rw [factor_4_30]; decide
      have factor_4_32 : (10 : ZMod 116454478141) ^ 5293385370 = 111081810370 := by
        calc
          (10 : ZMod 116454478141) ^ 5293385370 = (10 : ZMod 116454478141) ^ (2646692685 + 2646692685) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2646692685 * (10 : ZMod 116454478141) ^ 2646692685 := by rw [pow_add]
          _ = 111081810370 := by rw [factor_4_31]; decide
      have factor_4_33 : (10 : ZMod 116454478141) ^ 10586770740 = 57816077669 := by
        calc
          (10 : ZMod 116454478141) ^ 10586770740 = (10 : ZMod 116454478141) ^ (5293385370 + 5293385370) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 5293385370 * (10 : ZMod 116454478141) ^ 5293385370 := by rw [pow_add]
          _ = 57816077669 := by rw [factor_4_32]; decide
      change (10 : ZMod 116454478141) ^ 10586770740 ≠ 1
      rw [factor_4_33]
      decide
    ·
      have factor_5_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_5_1 : (10 : ZMod 116454478141) ^ 2 = 100 := by
        calc
          (10 : ZMod 116454478141) ^ 2 = (10 : ZMod 116454478141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_5_0]; decide
      have factor_5_2 : (10 : ZMod 116454478141) ^ 4 = 10000 := by
        calc
          (10 : ZMod 116454478141) ^ 4 = (10 : ZMod 116454478141) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2 * (10 : ZMod 116454478141) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_5_1]; decide
      have factor_5_3 : (10 : ZMod 116454478141) ^ 8 = 100000000 := by
        calc
          (10 : ZMod 116454478141) ^ 8 = (10 : ZMod 116454478141) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 4 * (10 : ZMod 116454478141) ^ 4 := by rw [pow_add]
          _ = 100000000 := by rw [factor_5_2]; decide
      have factor_5_4 : (10 : ZMod 116454478141) ^ 16 = 53962032330 := by
        calc
          (10 : ZMod 116454478141) ^ 16 = (10 : ZMod 116454478141) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 8 * (10 : ZMod 116454478141) ^ 8 := by rw [pow_add]
          _ = 53962032330 := by rw [factor_5_3]; decide
      have factor_5_5 : (10 : ZMod 116454478141) ^ 33 = 7541491947 := by
        calc
          (10 : ZMod 116454478141) ^ 33 = (10 : ZMod 116454478141) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 16 * (10 : ZMod 116454478141) ^ 16) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 7541491947 := by rw [factor_5_4]; decide
      have factor_5_6 : (10 : ZMod 116454478141) ^ 66 = 99655030951 := by
        calc
          (10 : ZMod 116454478141) ^ 66 = (10 : ZMod 116454478141) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 33 * (10 : ZMod 116454478141) ^ 33 := by rw [pow_add]
          _ = 99655030951 := by rw [factor_5_5]; decide
      have factor_5_7 : (10 : ZMod 116454478141) ^ 133 = 40070660285 := by
        calc
          (10 : ZMod 116454478141) ^ 133 = (10 : ZMod 116454478141) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 66 * (10 : ZMod 116454478141) ^ 66) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 40070660285 := by rw [factor_5_6]; decide
      have factor_5_8 : (10 : ZMod 116454478141) ^ 266 = 34123224060 := by
        calc
          (10 : ZMod 116454478141) ^ 266 = (10 : ZMod 116454478141) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 133 * (10 : ZMod 116454478141) ^ 133 := by rw [pow_add]
          _ = 34123224060 := by rw [factor_5_7]; decide
      have factor_5_9 : (10 : ZMod 116454478141) ^ 533 = 49868043203 := by
        calc
          (10 : ZMod 116454478141) ^ 533 = (10 : ZMod 116454478141) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 266 * (10 : ZMod 116454478141) ^ 266) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 49868043203 := by rw [factor_5_8]; decide
      have factor_5_10 : (10 : ZMod 116454478141) ^ 1067 = 59476848937 := by
        calc
          (10 : ZMod 116454478141) ^ 1067 = (10 : ZMod 116454478141) ^ (533 + 533 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 533 * (10 : ZMod 116454478141) ^ 533) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 59476848937 := by rw [factor_5_9]; decide
      have factor_5_11 : (10 : ZMod 116454478141) ^ 2135 = 26947108033 := by
        calc
          (10 : ZMod 116454478141) ^ 2135 = (10 : ZMod 116454478141) ^ (1067 + 1067 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1067 * (10 : ZMod 116454478141) ^ 1067) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 26947108033 := by rw [factor_5_10]; decide
      have factor_5_12 : (10 : ZMod 116454478141) ^ 4271 = 19140205639 := by
        calc
          (10 : ZMod 116454478141) ^ 4271 = (10 : ZMod 116454478141) ^ (2135 + 2135 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2135 * (10 : ZMod 116454478141) ^ 2135) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 19140205639 := by rw [factor_5_11]; decide
      have factor_5_13 : (10 : ZMod 116454478141) ^ 8543 = 45977448522 := by
        calc
          (10 : ZMod 116454478141) ^ 8543 = (10 : ZMod 116454478141) ^ (4271 + 4271 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4271 * (10 : ZMod 116454478141) ^ 4271) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 45977448522 := by rw [factor_5_12]; decide
      have factor_5_14 : (10 : ZMod 116454478141) ^ 17086 = 21119493101 := by
        calc
          (10 : ZMod 116454478141) ^ 17086 = (10 : ZMod 116454478141) ^ (8543 + 8543) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 8543 * (10 : ZMod 116454478141) ^ 8543 := by rw [pow_add]
          _ = 21119493101 := by rw [factor_5_13]; decide
      have factor_5_15 : (10 : ZMod 116454478141) ^ 34172 = 26378904238 := by
        calc
          (10 : ZMod 116454478141) ^ 34172 = (10 : ZMod 116454478141) ^ (17086 + 17086) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 17086 * (10 : ZMod 116454478141) ^ 17086 := by rw [pow_add]
          _ = 26378904238 := by rw [factor_5_14]; decide
      have factor_5_16 : (10 : ZMod 116454478141) ^ 68344 = 88429049603 := by
        calc
          (10 : ZMod 116454478141) ^ 68344 = (10 : ZMod 116454478141) ^ (34172 + 34172) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 34172 * (10 : ZMod 116454478141) ^ 34172 := by rw [pow_add]
          _ = 88429049603 := by rw [factor_5_15]; decide
      have factor_5_17 : (10 : ZMod 116454478141) ^ 136688 = 109804441106 := by
        calc
          (10 : ZMod 116454478141) ^ 136688 = (10 : ZMod 116454478141) ^ (68344 + 68344) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 68344 * (10 : ZMod 116454478141) ^ 68344 := by rw [pow_add]
          _ = 109804441106 := by rw [factor_5_16]; decide
      have factor_5_18 : (10 : ZMod 116454478141) ^ 273377 = 60917108567 := by
        calc
          (10 : ZMod 116454478141) ^ 273377 = (10 : ZMod 116454478141) ^ (136688 + 136688 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 136688 * (10 : ZMod 116454478141) ^ 136688) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 60917108567 := by rw [factor_5_17]; decide
      have factor_5_19 : (10 : ZMod 116454478141) ^ 546755 = 67068453282 := by
        calc
          (10 : ZMod 116454478141) ^ 546755 = (10 : ZMod 116454478141) ^ (273377 + 273377 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 273377 * (10 : ZMod 116454478141) ^ 273377) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 67068453282 := by rw [factor_5_18]; decide
      have factor_5_20 : (10 : ZMod 116454478141) ^ 1093510 = 3272131216 := by
        calc
          (10 : ZMod 116454478141) ^ 1093510 = (10 : ZMod 116454478141) ^ (546755 + 546755) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 546755 * (10 : ZMod 116454478141) ^ 546755 := by rw [pow_add]
          _ = 3272131216 := by rw [factor_5_19]; decide
      have factor_5_21 : (10 : ZMod 116454478141) ^ 2187020 = 40448464942 := by
        calc
          (10 : ZMod 116454478141) ^ 2187020 = (10 : ZMod 116454478141) ^ (1093510 + 1093510) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1093510 * (10 : ZMod 116454478141) ^ 1093510 := by rw [pow_add]
          _ = 40448464942 := by rw [factor_5_20]; decide
      have factor_5_22 : (10 : ZMod 116454478141) ^ 4374041 = 110183643015 := by
        calc
          (10 : ZMod 116454478141) ^ 4374041 = (10 : ZMod 116454478141) ^ (2187020 + 2187020 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2187020 * (10 : ZMod 116454478141) ^ 2187020) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 110183643015 := by rw [factor_5_21]; decide
      have factor_5_23 : (10 : ZMod 116454478141) ^ 8748082 = 72168030469 := by
        calc
          (10 : ZMod 116454478141) ^ 8748082 = (10 : ZMod 116454478141) ^ (4374041 + 4374041) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 4374041 * (10 : ZMod 116454478141) ^ 4374041 := by rw [pow_add]
          _ = 72168030469 := by rw [factor_5_22]; decide
      have factor_5_24 : (10 : ZMod 116454478141) ^ 17496165 = 13039169780 := by
        calc
          (10 : ZMod 116454478141) ^ 17496165 = (10 : ZMod 116454478141) ^ (8748082 + 8748082 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 8748082 * (10 : ZMod 116454478141) ^ 8748082) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 13039169780 := by rw [factor_5_23]; decide
      have factor_5_25 : (10 : ZMod 116454478141) ^ 34992331 = 4122275135 := by
        calc
          (10 : ZMod 116454478141) ^ 34992331 = (10 : ZMod 116454478141) ^ (17496165 + 17496165 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 17496165 * (10 : ZMod 116454478141) ^ 17496165) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 4122275135 := by rw [factor_5_24]; decide
      have factor_5_26 : (10 : ZMod 116454478141) ^ 69984662 = 14189101199 := by
        calc
          (10 : ZMod 116454478141) ^ 69984662 = (10 : ZMod 116454478141) ^ (34992331 + 34992331) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 34992331 * (10 : ZMod 116454478141) ^ 34992331 := by rw [pow_add]
          _ = 14189101199 := by rw [factor_5_25]; decide
      have factor_5_27 : (10 : ZMod 116454478141) ^ 139969324 = 95939822412 := by
        calc
          (10 : ZMod 116454478141) ^ 139969324 = (10 : ZMod 116454478141) ^ (69984662 + 69984662) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 69984662 * (10 : ZMod 116454478141) ^ 69984662 := by rw [pow_add]
          _ = 95939822412 := by rw [factor_5_26]; decide
      have factor_5_28 : (10 : ZMod 116454478141) ^ 279938649 = 14623685729 := by
        calc
          (10 : ZMod 116454478141) ^ 279938649 = (10 : ZMod 116454478141) ^ (139969324 + 139969324 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 139969324 * (10 : ZMod 116454478141) ^ 139969324) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 14623685729 := by rw [factor_5_27]; decide
      have factor_5_29 : (10 : ZMod 116454478141) ^ 559877298 = 111003726726 := by
        calc
          (10 : ZMod 116454478141) ^ 559877298 = (10 : ZMod 116454478141) ^ (279938649 + 279938649) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 279938649 * (10 : ZMod 116454478141) ^ 279938649 := by rw [pow_add]
          _ = 111003726726 := by rw [factor_5_28]; decide
      have factor_5_30 : (10 : ZMod 116454478141) ^ 1119754597 = 37964483168 := by
        calc
          (10 : ZMod 116454478141) ^ 1119754597 = (10 : ZMod 116454478141) ^ (559877298 + 559877298 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 559877298 * (10 : ZMod 116454478141) ^ 559877298) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 37964483168 := by rw [factor_5_29]; decide
      have factor_5_31 : (10 : ZMod 116454478141) ^ 2239509195 = 23982372665 := by
        calc
          (10 : ZMod 116454478141) ^ 2239509195 = (10 : ZMod 116454478141) ^ (1119754597 + 1119754597 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1119754597 * (10 : ZMod 116454478141) ^ 1119754597) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 23982372665 := by rw [factor_5_30]; decide
      have factor_5_32 : (10 : ZMod 116454478141) ^ 4479018390 = 107631308911 := by
        calc
          (10 : ZMod 116454478141) ^ 4479018390 = (10 : ZMod 116454478141) ^ (2239509195 + 2239509195) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2239509195 * (10 : ZMod 116454478141) ^ 2239509195 := by rw [pow_add]
          _ = 107631308911 := by rw [factor_5_31]; decide
      have factor_5_33 : (10 : ZMod 116454478141) ^ 8958036780 = 51273093210 := by
        calc
          (10 : ZMod 116454478141) ^ 8958036780 = (10 : ZMod 116454478141) ^ (4479018390 + 4479018390) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 4479018390 * (10 : ZMod 116454478141) ^ 4479018390 := by rw [pow_add]
          _ = 51273093210 := by rw [factor_5_32]; decide
      change (10 : ZMod 116454478141) ^ 8958036780 ≠ 1
      rw [factor_5_33]
      decide
    ·
      have factor_6_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_6_1 : (10 : ZMod 116454478141) ^ 3 = 1000 := by
        calc
          (10 : ZMod 116454478141) ^ 3 = (10 : ZMod 116454478141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_6_0]; decide
      have factor_6_2 : (10 : ZMod 116454478141) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 116454478141) ^ 6 = (10 : ZMod 116454478141) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3 * (10 : ZMod 116454478141) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_6_1]; decide
      have factor_6_3 : (10 : ZMod 116454478141) ^ 12 = 68364174872 := by
        calc
          (10 : ZMod 116454478141) ^ 12 = (10 : ZMod 116454478141) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 6 * (10 : ZMod 116454478141) ^ 6 := by rw [pow_add]
          _ = 68364174872 := by rw [factor_6_2]; decide
      have factor_6_4 : (10 : ZMod 116454478141) ^ 25 = 9378583448 := by
        calc
          (10 : ZMod 116454478141) ^ 25 = (10 : ZMod 116454478141) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 12 * (10 : ZMod 116454478141) ^ 12) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 9378583448 := by rw [factor_6_3]; decide
      have factor_6_5 : (10 : ZMod 116454478141) ^ 51 = 8454479076 := by
        calc
          (10 : ZMod 116454478141) ^ 51 = (10 : ZMod 116454478141) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 25 * (10 : ZMod 116454478141) ^ 25) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 8454479076 := by rw [factor_6_4]; decide
      have factor_6_6 : (10 : ZMod 116454478141) ^ 102 = 86684513180 := by
        calc
          (10 : ZMod 116454478141) ^ 102 = (10 : ZMod 116454478141) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 51 * (10 : ZMod 116454478141) ^ 51 := by rw [pow_add]
          _ = 86684513180 := by rw [factor_6_5]; decide
      have factor_6_7 : (10 : ZMod 116454478141) ^ 204 = 60790390157 := by
        calc
          (10 : ZMod 116454478141) ^ 204 = (10 : ZMod 116454478141) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 102 * (10 : ZMod 116454478141) ^ 102 := by rw [pow_add]
          _ = 60790390157 := by rw [factor_6_6]; decide
      have factor_6_8 : (10 : ZMod 116454478141) ^ 408 = 63221741516 := by
        calc
          (10 : ZMod 116454478141) ^ 408 = (10 : ZMod 116454478141) ^ (204 + 204) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 204 * (10 : ZMod 116454478141) ^ 204 := by rw [pow_add]
          _ = 63221741516 := by rw [factor_6_7]; decide
      have factor_6_9 : (10 : ZMod 116454478141) ^ 816 = 18754528995 := by
        calc
          (10 : ZMod 116454478141) ^ 816 = (10 : ZMod 116454478141) ^ (408 + 408) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 408 * (10 : ZMod 116454478141) ^ 408 := by rw [pow_add]
          _ = 18754528995 := by rw [factor_6_8]; decide
      have factor_6_10 : (10 : ZMod 116454478141) ^ 1633 = 19551902700 := by
        calc
          (10 : ZMod 116454478141) ^ 1633 = (10 : ZMod 116454478141) ^ (816 + 816 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 816 * (10 : ZMod 116454478141) ^ 816) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 19551902700 := by rw [factor_6_9]; decide
      have factor_6_11 : (10 : ZMod 116454478141) ^ 3266 = 9602871973 := by
        calc
          (10 : ZMod 116454478141) ^ 3266 = (10 : ZMod 116454478141) ^ (1633 + 1633) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1633 * (10 : ZMod 116454478141) ^ 1633 := by rw [pow_add]
          _ = 9602871973 := by rw [factor_6_10]; decide
      have factor_6_12 : (10 : ZMod 116454478141) ^ 6532 = 20902623582 := by
        calc
          (10 : ZMod 116454478141) ^ 6532 = (10 : ZMod 116454478141) ^ (3266 + 3266) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3266 * (10 : ZMod 116454478141) ^ 3266 := by rw [pow_add]
          _ = 20902623582 := by rw [factor_6_11]; decide
      have factor_6_13 : (10 : ZMod 116454478141) ^ 13065 = 59453716336 := by
        calc
          (10 : ZMod 116454478141) ^ 13065 = (10 : ZMod 116454478141) ^ (6532 + 6532 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 6532 * (10 : ZMod 116454478141) ^ 6532) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 59453716336 := by rw [factor_6_12]; decide
      have factor_6_14 : (10 : ZMod 116454478141) ^ 26131 = 751841610 := by
        calc
          (10 : ZMod 116454478141) ^ 26131 = (10 : ZMod 116454478141) ^ (13065 + 13065 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 13065 * (10 : ZMod 116454478141) ^ 13065) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 751841610 := by rw [factor_6_13]; decide
      have factor_6_15 : (10 : ZMod 116454478141) ^ 52263 = 85739824324 := by
        calc
          (10 : ZMod 116454478141) ^ 52263 = (10 : ZMod 116454478141) ^ (26131 + 26131 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 26131 * (10 : ZMod 116454478141) ^ 26131) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 85739824324 := by rw [factor_6_14]; decide
      have factor_6_16 : (10 : ZMod 116454478141) ^ 104526 = 6785021176 := by
        calc
          (10 : ZMod 116454478141) ^ 104526 = (10 : ZMod 116454478141) ^ (52263 + 52263) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 52263 * (10 : ZMod 116454478141) ^ 52263 := by rw [pow_add]
          _ = 6785021176 := by rw [factor_6_15]; decide
      have factor_6_17 : (10 : ZMod 116454478141) ^ 209053 = 45656578392 := by
        calc
          (10 : ZMod 116454478141) ^ 209053 = (10 : ZMod 116454478141) ^ (104526 + 104526 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 104526 * (10 : ZMod 116454478141) ^ 104526) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 45656578392 := by rw [factor_6_16]; decide
      have factor_6_18 : (10 : ZMod 116454478141) ^ 418106 = 60909293020 := by
        calc
          (10 : ZMod 116454478141) ^ 418106 = (10 : ZMod 116454478141) ^ (209053 + 209053) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 209053 * (10 : ZMod 116454478141) ^ 209053 := by rw [pow_add]
          _ = 60909293020 := by rw [factor_6_17]; decide
      have factor_6_19 : (10 : ZMod 116454478141) ^ 836213 = 43570581092 := by
        calc
          (10 : ZMod 116454478141) ^ 836213 = (10 : ZMod 116454478141) ^ (418106 + 418106 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 418106 * (10 : ZMod 116454478141) ^ 418106) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 43570581092 := by rw [factor_6_18]; decide
      have factor_6_20 : (10 : ZMod 116454478141) ^ 1672427 = 115341769817 := by
        calc
          (10 : ZMod 116454478141) ^ 1672427 = (10 : ZMod 116454478141) ^ (836213 + 836213 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 836213 * (10 : ZMod 116454478141) ^ 836213) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 115341769817 := by rw [factor_6_19]; decide
      have factor_6_21 : (10 : ZMod 116454478141) ^ 3344855 = 19443346758 := by
        calc
          (10 : ZMod 116454478141) ^ 3344855 = (10 : ZMod 116454478141) ^ (1672427 + 1672427 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1672427 * (10 : ZMod 116454478141) ^ 1672427) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 19443346758 := by rw [factor_6_20]; decide
      have factor_6_22 : (10 : ZMod 116454478141) ^ 6689710 = 18199951950 := by
        calc
          (10 : ZMod 116454478141) ^ 6689710 = (10 : ZMod 116454478141) ^ (3344855 + 3344855) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3344855 * (10 : ZMod 116454478141) ^ 3344855 := by rw [pow_add]
          _ = 18199951950 := by rw [factor_6_21]; decide
      have factor_6_23 : (10 : ZMod 116454478141) ^ 13379420 = 107144393031 := by
        calc
          (10 : ZMod 116454478141) ^ 13379420 = (10 : ZMod 116454478141) ^ (6689710 + 6689710) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 6689710 * (10 : ZMod 116454478141) ^ 6689710 := by rw [pow_add]
          _ = 107144393031 := by rw [factor_6_22]; decide
      have factor_6_24 : (10 : ZMod 116454478141) ^ 26758841 = 20538642486 := by
        calc
          (10 : ZMod 116454478141) ^ 26758841 = (10 : ZMod 116454478141) ^ (13379420 + 13379420 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 13379420 * (10 : ZMod 116454478141) ^ 13379420) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 20538642486 := by rw [factor_6_23]; decide
      have factor_6_25 : (10 : ZMod 116454478141) ^ 53517682 = 44368081513 := by
        calc
          (10 : ZMod 116454478141) ^ 53517682 = (10 : ZMod 116454478141) ^ (26758841 + 26758841) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 26758841 * (10 : ZMod 116454478141) ^ 26758841 := by rw [pow_add]
          _ = 44368081513 := by rw [factor_6_24]; decide
      have factor_6_26 : (10 : ZMod 116454478141) ^ 107035365 = 113432111657 := by
        calc
          (10 : ZMod 116454478141) ^ 107035365 = (10 : ZMod 116454478141) ^ (53517682 + 53517682 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 53517682 * (10 : ZMod 116454478141) ^ 53517682) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 113432111657 := by rw [factor_6_25]; decide
      have factor_6_27 : (10 : ZMod 116454478141) ^ 214070731 = 112412880851 := by
        calc
          (10 : ZMod 116454478141) ^ 214070731 = (10 : ZMod 116454478141) ^ (107035365 + 107035365 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 107035365 * (10 : ZMod 116454478141) ^ 107035365) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 112412880851 := by rw [factor_6_26]; decide
      have factor_6_28 : (10 : ZMod 116454478141) ^ 428141463 = 18548227393 := by
        calc
          (10 : ZMod 116454478141) ^ 428141463 = (10 : ZMod 116454478141) ^ (214070731 + 214070731 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 214070731 * (10 : ZMod 116454478141) ^ 214070731) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 18548227393 := by rw [factor_6_27]; decide
      have factor_6_29 : (10 : ZMod 116454478141) ^ 856282927 = 5479081778 := by
        calc
          (10 : ZMod 116454478141) ^ 856282927 = (10 : ZMod 116454478141) ^ (428141463 + 428141463 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 428141463 * (10 : ZMod 116454478141) ^ 428141463) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 5479081778 := by rw [factor_6_28]; decide
      have factor_6_30 : (10 : ZMod 116454478141) ^ 1712565855 = 1393836180 := by
        calc
          (10 : ZMod 116454478141) ^ 1712565855 = (10 : ZMod 116454478141) ^ (856282927 + 856282927 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 856282927 * (10 : ZMod 116454478141) ^ 856282927) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1393836180 := by rw [factor_6_29]; decide
      have factor_6_31 : (10 : ZMod 116454478141) ^ 3425131710 = 98287396765 := by
        calc
          (10 : ZMod 116454478141) ^ 3425131710 = (10 : ZMod 116454478141) ^ (1712565855 + 1712565855) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1712565855 * (10 : ZMod 116454478141) ^ 1712565855 := by rw [pow_add]
          _ = 98287396765 := by rw [factor_6_30]; decide
      have factor_6_32 : (10 : ZMod 116454478141) ^ 6850263420 = 65159008907 := by
        calc
          (10 : ZMod 116454478141) ^ 6850263420 = (10 : ZMod 116454478141) ^ (3425131710 + 3425131710) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3425131710 * (10 : ZMod 116454478141) ^ 3425131710 := by rw [pow_add]
          _ = 65159008907 := by rw [factor_6_31]; decide
      change (10 : ZMod 116454478141) ^ 6850263420 ≠ 1
      rw [factor_6_32]
      decide
    ·
      have factor_7_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_7_1 : (10 : ZMod 116454478141) ^ 2 = 100 := by
        calc
          (10 : ZMod 116454478141) ^ 2 = (10 : ZMod 116454478141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_7_0]; decide
      have factor_7_2 : (10 : ZMod 116454478141) ^ 5 = 100000 := by
        calc
          (10 : ZMod 116454478141) ^ 5 = (10 : ZMod 116454478141) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2 * (10 : ZMod 116454478141) ^ 2) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_7_1]; decide
      have factor_7_3 : (10 : ZMod 116454478141) ^ 11 = 100000000000 := by
        calc
          (10 : ZMod 116454478141) ^ 11 = (10 : ZMod 116454478141) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 5 * (10 : ZMod 116454478141) ^ 5) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 100000000000 := by rw [factor_7_2]; decide
      have factor_7_4 : (10 : ZMod 116454478141) ^ 22 = 54975892266 := by
        calc
          (10 : ZMod 116454478141) ^ 22 = (10 : ZMod 116454478141) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 11 * (10 : ZMod 116454478141) ^ 11 := by rw [pow_add]
          _ = 54975892266 := by rw [factor_7_3]; decide
      have factor_7_5 : (10 : ZMod 116454478141) ^ 45 = 43549790918 := by
        calc
          (10 : ZMod 116454478141) ^ 45 = (10 : ZMod 116454478141) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 22 * (10 : ZMod 116454478141) ^ 22) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 43549790918 := by rw [factor_7_4]; decide
      have factor_7_6 : (10 : ZMod 116454478141) ^ 91 = 35377664015 := by
        calc
          (10 : ZMod 116454478141) ^ 91 = (10 : ZMod 116454478141) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 45 * (10 : ZMod 116454478141) ^ 45) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 35377664015 := by rw [factor_7_5]; decide
      have factor_7_7 : (10 : ZMod 116454478141) ^ 182 = 57840141323 := by
        calc
          (10 : ZMod 116454478141) ^ 182 = (10 : ZMod 116454478141) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 91 * (10 : ZMod 116454478141) ^ 91 := by rw [pow_add]
          _ = 57840141323 := by rw [factor_7_6]; decide
      have factor_7_8 : (10 : ZMod 116454478141) ^ 365 = 48198279062 := by
        calc
          (10 : ZMod 116454478141) ^ 365 = (10 : ZMod 116454478141) ^ (182 + 182 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 182 * (10 : ZMod 116454478141) ^ 182) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 48198279062 := by rw [factor_7_7]; decide
      have factor_7_9 : (10 : ZMod 116454478141) ^ 730 = 115890517664 := by
        calc
          (10 : ZMod 116454478141) ^ 730 = (10 : ZMod 116454478141) ^ (365 + 365) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 365 * (10 : ZMod 116454478141) ^ 365 := by rw [pow_add]
          _ = 115890517664 := by rw [factor_7_8]; decide
      have factor_7_10 : (10 : ZMod 116454478141) ^ 1461 = 90777676988 := by
        calc
          (10 : ZMod 116454478141) ^ 1461 = (10 : ZMod 116454478141) ^ (730 + 730 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 730 * (10 : ZMod 116454478141) ^ 730) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 90777676988 := by rw [factor_7_9]; decide
      have factor_7_11 : (10 : ZMod 116454478141) ^ 2922 = 86280066165 := by
        calc
          (10 : ZMod 116454478141) ^ 2922 = (10 : ZMod 116454478141) ^ (1461 + 1461) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1461 * (10 : ZMod 116454478141) ^ 1461 := by rw [pow_add]
          _ = 86280066165 := by rw [factor_7_10]; decide
      have factor_7_12 : (10 : ZMod 116454478141) ^ 5845 = 72819065232 := by
        calc
          (10 : ZMod 116454478141) ^ 5845 = (10 : ZMod 116454478141) ^ (2922 + 2922 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 2922 * (10 : ZMod 116454478141) ^ 2922) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 72819065232 := by rw [factor_7_11]; decide
      have factor_7_13 : (10 : ZMod 116454478141) ^ 11690 = 18655275979 := by
        calc
          (10 : ZMod 116454478141) ^ 11690 = (10 : ZMod 116454478141) ^ (5845 + 5845) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 5845 * (10 : ZMod 116454478141) ^ 5845 := by rw [pow_add]
          _ = 18655275979 := by rw [factor_7_12]; decide
      have factor_7_14 : (10 : ZMod 116454478141) ^ 23380 = 8815270378 := by
        calc
          (10 : ZMod 116454478141) ^ 23380 = (10 : ZMod 116454478141) ^ (11690 + 11690) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 11690 * (10 : ZMod 116454478141) ^ 11690 := by rw [pow_add]
          _ = 8815270378 := by rw [factor_7_13]; decide
      have factor_7_15 : (10 : ZMod 116454478141) ^ 46761 = 49753236523 := by
        calc
          (10 : ZMod 116454478141) ^ 46761 = (10 : ZMod 116454478141) ^ (23380 + 23380 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 23380 * (10 : ZMod 116454478141) ^ 23380) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 49753236523 := by rw [factor_7_14]; decide
      have factor_7_16 : (10 : ZMod 116454478141) ^ 93523 = 45151950043 := by
        calc
          (10 : ZMod 116454478141) ^ 93523 = (10 : ZMod 116454478141) ^ (46761 + 46761 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 46761 * (10 : ZMod 116454478141) ^ 46761) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 45151950043 := by rw [factor_7_15]; decide
      have factor_7_17 : (10 : ZMod 116454478141) ^ 187047 = 92443376896 := by
        calc
          (10 : ZMod 116454478141) ^ 187047 = (10 : ZMod 116454478141) ^ (93523 + 93523 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 93523 * (10 : ZMod 116454478141) ^ 93523) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 92443376896 := by rw [factor_7_16]; decide
      have factor_7_18 : (10 : ZMod 116454478141) ^ 374095 = 78493529850 := by
        calc
          (10 : ZMod 116454478141) ^ 374095 = (10 : ZMod 116454478141) ^ (187047 + 187047 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 187047 * (10 : ZMod 116454478141) ^ 187047) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 78493529850 := by rw [factor_7_17]; decide
      have factor_7_19 : (10 : ZMod 116454478141) ^ 748191 = 102662492837 := by
        calc
          (10 : ZMod 116454478141) ^ 748191 = (10 : ZMod 116454478141) ^ (374095 + 374095 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 374095 * (10 : ZMod 116454478141) ^ 374095) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 102662492837 := by rw [factor_7_18]; decide
      have factor_7_20 : (10 : ZMod 116454478141) ^ 1496382 = 32100878843 := by
        calc
          (10 : ZMod 116454478141) ^ 1496382 = (10 : ZMod 116454478141) ^ (748191 + 748191) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 748191 * (10 : ZMod 116454478141) ^ 748191 := by rw [pow_add]
          _ = 32100878843 := by rw [factor_7_19]; decide
      have factor_7_21 : (10 : ZMod 116454478141) ^ 2992765 = 35568172559 := by
        calc
          (10 : ZMod 116454478141) ^ 2992765 = (10 : ZMod 116454478141) ^ (1496382 + 1496382 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1496382 * (10 : ZMod 116454478141) ^ 1496382) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 35568172559 := by rw [factor_7_20]; decide
      have factor_7_22 : (10 : ZMod 116454478141) ^ 5985530 = 68144627161 := by
        calc
          (10 : ZMod 116454478141) ^ 5985530 = (10 : ZMod 116454478141) ^ (2992765 + 2992765) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2992765 * (10 : ZMod 116454478141) ^ 2992765 := by rw [pow_add]
          _ = 68144627161 := by rw [factor_7_21]; decide
      have factor_7_23 : (10 : ZMod 116454478141) ^ 11971060 = 98841588524 := by
        calc
          (10 : ZMod 116454478141) ^ 11971060 = (10 : ZMod 116454478141) ^ (5985530 + 5985530) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 5985530 * (10 : ZMod 116454478141) ^ 5985530 := by rw [pow_add]
          _ = 98841588524 := by rw [factor_7_22]; decide
      have factor_7_24 : (10 : ZMod 116454478141) ^ 23942121 = 60692896433 := by
        calc
          (10 : ZMod 116454478141) ^ 23942121 = (10 : ZMod 116454478141) ^ (11971060 + 11971060 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 11971060 * (10 : ZMod 116454478141) ^ 11971060) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 60692896433 := by rw [factor_7_23]; decide
      have factor_7_25 : (10 : ZMod 116454478141) ^ 47884242 = 112671934234 := by
        calc
          (10 : ZMod 116454478141) ^ 47884242 = (10 : ZMod 116454478141) ^ (23942121 + 23942121) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 23942121 * (10 : ZMod 116454478141) ^ 23942121 := by rw [pow_add]
          _ = 112671934234 := by rw [factor_7_24]; decide
      have factor_7_26 : (10 : ZMod 116454478141) ^ 95768485 = 107397505491 := by
        calc
          (10 : ZMod 116454478141) ^ 95768485 = (10 : ZMod 116454478141) ^ (47884242 + 47884242 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 47884242 * (10 : ZMod 116454478141) ^ 47884242) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 107397505491 := by rw [factor_7_25]; decide
      have factor_7_27 : (10 : ZMod 116454478141) ^ 191536970 = 2207354672 := by
        calc
          (10 : ZMod 116454478141) ^ 191536970 = (10 : ZMod 116454478141) ^ (95768485 + 95768485) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 95768485 * (10 : ZMod 116454478141) ^ 95768485 := by rw [pow_add]
          _ = 2207354672 := by rw [factor_7_26]; decide
      have factor_7_28 : (10 : ZMod 116454478141) ^ 383073941 = 67117934917 := by
        calc
          (10 : ZMod 116454478141) ^ 383073941 = (10 : ZMod 116454478141) ^ (191536970 + 191536970 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 191536970 * (10 : ZMod 116454478141) ^ 191536970) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 67117934917 := by rw [factor_7_27]; decide
      have factor_7_29 : (10 : ZMod 116454478141) ^ 766147882 = 114775832759 := by
        calc
          (10 : ZMod 116454478141) ^ 766147882 = (10 : ZMod 116454478141) ^ (383073941 + 383073941) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 383073941 * (10 : ZMod 116454478141) ^ 383073941 := by rw [pow_add]
          _ = 114775832759 := by rw [factor_7_28]; decide
      have factor_7_30 : (10 : ZMod 116454478141) ^ 1532295765 = 66419937448 := by
        calc
          (10 : ZMod 116454478141) ^ 1532295765 = (10 : ZMod 116454478141) ^ (766147882 + 766147882 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 766147882 * (10 : ZMod 116454478141) ^ 766147882) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 66419937448 := by rw [factor_7_29]; decide
      have factor_7_31 : (10 : ZMod 116454478141) ^ 3064591530 = 70670548168 := by
        calc
          (10 : ZMod 116454478141) ^ 3064591530 = (10 : ZMod 116454478141) ^ (1532295765 + 1532295765) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1532295765 * (10 : ZMod 116454478141) ^ 1532295765 := by rw [pow_add]
          _ = 70670548168 := by rw [factor_7_30]; decide
      have factor_7_32 : (10 : ZMod 116454478141) ^ 6129183060 = 41967229289 := by
        calc
          (10 : ZMod 116454478141) ^ 6129183060 = (10 : ZMod 116454478141) ^ (3064591530 + 3064591530) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3064591530 * (10 : ZMod 116454478141) ^ 3064591530 := by rw [pow_add]
          _ = 41967229289 := by rw [factor_7_31]; decide
      change (10 : ZMod 116454478141) ^ 6129183060 ≠ 1
      rw [factor_7_32]
      decide
    ·
      have factor_8_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_8_1 : (10 : ZMod 116454478141) ^ 2 = 100 := by
        calc
          (10 : ZMod 116454478141) ^ 2 = (10 : ZMod 116454478141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_8_0]; decide
      have factor_8_2 : (10 : ZMod 116454478141) ^ 4 = 10000 := by
        calc
          (10 : ZMod 116454478141) ^ 4 = (10 : ZMod 116454478141) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2 * (10 : ZMod 116454478141) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_8_1]; decide
      have factor_8_3 : (10 : ZMod 116454478141) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 116454478141) ^ 9 = (10 : ZMod 116454478141) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4 * (10 : ZMod 116454478141) ^ 4) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [factor_8_2]; decide
      have factor_8_4 : (10 : ZMod 116454478141) ^ 18 = 39297238514 := by
        calc
          (10 : ZMod 116454478141) ^ 18 = (10 : ZMod 116454478141) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 9 * (10 : ZMod 116454478141) ^ 9 := by rw [pow_add]
          _ = 39297238514 := by rw [factor_8_3]; decide
      have factor_8_5 : (10 : ZMod 116454478141) ^ 37 = 68872112773 := by
        calc
          (10 : ZMod 116454478141) ^ 37 = (10 : ZMod 116454478141) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 18 * (10 : ZMod 116454478141) ^ 18) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 68872112773 := by rw [factor_8_4]; decide
      have factor_8_6 : (10 : ZMod 116454478141) ^ 75 = 62416422112 := by
        calc
          (10 : ZMod 116454478141) ^ 75 = (10 : ZMod 116454478141) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 37 * (10 : ZMod 116454478141) ^ 37) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 62416422112 := by rw [factor_8_5]; decide
      have factor_8_7 : (10 : ZMod 116454478141) ^ 150 = 93522640386 := by
        calc
          (10 : ZMod 116454478141) ^ 150 = (10 : ZMod 116454478141) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 75 * (10 : ZMod 116454478141) ^ 75 := by rw [pow_add]
          _ = 93522640386 := by rw [factor_8_6]; decide
      have factor_8_8 : (10 : ZMod 116454478141) ^ 301 = 29054879427 := by
        calc
          (10 : ZMod 116454478141) ^ 301 = (10 : ZMod 116454478141) ^ (150 + 150 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 150 * (10 : ZMod 116454478141) ^ 150) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 29054879427 := by rw [factor_8_7]; decide
      have factor_8_9 : (10 : ZMod 116454478141) ^ 603 = 40650444946 := by
        calc
          (10 : ZMod 116454478141) ^ 603 = (10 : ZMod 116454478141) ^ (301 + 301 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 301 * (10 : ZMod 116454478141) ^ 301) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 40650444946 := by rw [factor_8_8]; decide
      have factor_8_10 : (10 : ZMod 116454478141) ^ 1207 = 113502165431 := by
        calc
          (10 : ZMod 116454478141) ^ 1207 = (10 : ZMod 116454478141) ^ (603 + 603 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 603 * (10 : ZMod 116454478141) ^ 603) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 113502165431 := by rw [factor_8_9]; decide
      have factor_8_11 : (10 : ZMod 116454478141) ^ 2414 = 97048952074 := by
        calc
          (10 : ZMod 116454478141) ^ 2414 = (10 : ZMod 116454478141) ^ (1207 + 1207) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1207 * (10 : ZMod 116454478141) ^ 1207 := by rw [pow_add]
          _ = 97048952074 := by rw [factor_8_10]; decide
      have factor_8_12 : (10 : ZMod 116454478141) ^ 4828 = 47919124827 := by
        calc
          (10 : ZMod 116454478141) ^ 4828 = (10 : ZMod 116454478141) ^ (2414 + 2414) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2414 * (10 : ZMod 116454478141) ^ 2414 := by rw [pow_add]
          _ = 47919124827 := by rw [factor_8_11]; decide
      have factor_8_13 : (10 : ZMod 116454478141) ^ 9657 = 114772111779 := by
        calc
          (10 : ZMod 116454478141) ^ 9657 = (10 : ZMod 116454478141) ^ (4828 + 4828 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4828 * (10 : ZMod 116454478141) ^ 4828) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 114772111779 := by rw [factor_8_12]; decide
      have factor_8_14 : (10 : ZMod 116454478141) ^ 19314 = 8095560221 := by
        calc
          (10 : ZMod 116454478141) ^ 19314 = (10 : ZMod 116454478141) ^ (9657 + 9657) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 9657 * (10 : ZMod 116454478141) ^ 9657 := by rw [pow_add]
          _ = 8095560221 := by rw [factor_8_13]; decide
      have factor_8_15 : (10 : ZMod 116454478141) ^ 38629 = 45463718259 := by
        calc
          (10 : ZMod 116454478141) ^ 38629 = (10 : ZMod 116454478141) ^ (19314 + 19314 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 19314 * (10 : ZMod 116454478141) ^ 19314) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 45463718259 := by rw [factor_8_14]; decide
      have factor_8_16 : (10 : ZMod 116454478141) ^ 77258 = 68536067880 := by
        calc
          (10 : ZMod 116454478141) ^ 77258 = (10 : ZMod 116454478141) ^ (38629 + 38629) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 38629 * (10 : ZMod 116454478141) ^ 38629 := by rw [pow_add]
          _ = 68536067880 := by rw [factor_8_15]; decide
      have factor_8_17 : (10 : ZMod 116454478141) ^ 154517 = 110860114581 := by
        calc
          (10 : ZMod 116454478141) ^ 154517 = (10 : ZMod 116454478141) ^ (77258 + 77258 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 77258 * (10 : ZMod 116454478141) ^ 77258) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 110860114581 := by rw [factor_8_16]; decide
      have factor_8_18 : (10 : ZMod 116454478141) ^ 309035 = 102249184003 := by
        calc
          (10 : ZMod 116454478141) ^ 309035 = (10 : ZMod 116454478141) ^ (154517 + 154517 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 154517 * (10 : ZMod 116454478141) ^ 154517) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 102249184003 := by rw [factor_8_17]; decide
      have factor_8_19 : (10 : ZMod 116454478141) ^ 618071 = 111884071493 := by
        calc
          (10 : ZMod 116454478141) ^ 618071 = (10 : ZMod 116454478141) ^ (309035 + 309035 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 309035 * (10 : ZMod 116454478141) ^ 309035) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 111884071493 := by rw [factor_8_18]; decide
      have factor_8_20 : (10 : ZMod 116454478141) ^ 1236142 = 56670173443 := by
        calc
          (10 : ZMod 116454478141) ^ 1236142 = (10 : ZMod 116454478141) ^ (618071 + 618071) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 618071 * (10 : ZMod 116454478141) ^ 618071 := by rw [pow_add]
          _ = 56670173443 := by rw [factor_8_19]; decide
      have factor_8_21 : (10 : ZMod 116454478141) ^ 2472284 = 19440031308 := by
        calc
          (10 : ZMod 116454478141) ^ 2472284 = (10 : ZMod 116454478141) ^ (1236142 + 1236142) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1236142 * (10 : ZMod 116454478141) ^ 1236142 := by rw [pow_add]
          _ = 19440031308 := by rw [factor_8_20]; decide
      have factor_8_22 : (10 : ZMod 116454478141) ^ 4944568 = 44874466237 := by
        calc
          (10 : ZMod 116454478141) ^ 4944568 = (10 : ZMod 116454478141) ^ (2472284 + 2472284) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2472284 * (10 : ZMod 116454478141) ^ 2472284 := by rw [pow_add]
          _ = 44874466237 := by rw [factor_8_21]; decide
      have factor_8_23 : (10 : ZMod 116454478141) ^ 9889137 = 65723178324 := by
        calc
          (10 : ZMod 116454478141) ^ 9889137 = (10 : ZMod 116454478141) ^ (4944568 + 4944568 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 4944568 * (10 : ZMod 116454478141) ^ 4944568) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 65723178324 := by rw [factor_8_22]; decide
      have factor_8_24 : (10 : ZMod 116454478141) ^ 19778274 = 64457136277 := by
        calc
          (10 : ZMod 116454478141) ^ 19778274 = (10 : ZMod 116454478141) ^ (9889137 + 9889137) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 9889137 * (10 : ZMod 116454478141) ^ 9889137 := by rw [pow_add]
          _ = 64457136277 := by rw [factor_8_23]; decide
      have factor_8_25 : (10 : ZMod 116454478141) ^ 39556548 = 32874586855 := by
        calc
          (10 : ZMod 116454478141) ^ 39556548 = (10 : ZMod 116454478141) ^ (19778274 + 19778274) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 19778274 * (10 : ZMod 116454478141) ^ 19778274 := by rw [pow_add]
          _ = 32874586855 := by rw [factor_8_24]; decide
      have factor_8_26 : (10 : ZMod 116454478141) ^ 79113096 = 34647589903 := by
        calc
          (10 : ZMod 116454478141) ^ 79113096 = (10 : ZMod 116454478141) ^ (39556548 + 39556548) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 39556548 * (10 : ZMod 116454478141) ^ 39556548 := by rw [pow_add]
          _ = 34647589903 := by rw [factor_8_25]; decide
      have factor_8_27 : (10 : ZMod 116454478141) ^ 158226193 = 78267886240 := by
        calc
          (10 : ZMod 116454478141) ^ 158226193 = (10 : ZMod 116454478141) ^ (79113096 + 79113096 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 79113096 * (10 : ZMod 116454478141) ^ 79113096) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 78267886240 := by rw [factor_8_26]; decide
      have factor_8_28 : (10 : ZMod 116454478141) ^ 316452386 = 35027561728 := by
        calc
          (10 : ZMod 116454478141) ^ 316452386 = (10 : ZMod 116454478141) ^ (158226193 + 158226193) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 158226193 * (10 : ZMod 116454478141) ^ 158226193 := by rw [pow_add]
          _ = 35027561728 := by rw [factor_8_27]; decide
      have factor_8_29 : (10 : ZMod 116454478141) ^ 632904772 = 115992864970 := by
        calc
          (10 : ZMod 116454478141) ^ 632904772 = (10 : ZMod 116454478141) ^ (316452386 + 316452386) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 316452386 * (10 : ZMod 116454478141) ^ 316452386 := by rw [pow_add]
          _ = 115992864970 := by rw [factor_8_28]; decide
      have factor_8_30 : (10 : ZMod 116454478141) ^ 1265809545 = 41282064855 := by
        calc
          (10 : ZMod 116454478141) ^ 1265809545 = (10 : ZMod 116454478141) ^ (632904772 + 632904772 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 632904772 * (10 : ZMod 116454478141) ^ 632904772) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 41282064855 := by rw [factor_8_29]; decide
      have factor_8_31 : (10 : ZMod 116454478141) ^ 2531619090 = 2423585015 := by
        calc
          (10 : ZMod 116454478141) ^ 2531619090 = (10 : ZMod 116454478141) ^ (1265809545 + 1265809545) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1265809545 * (10 : ZMod 116454478141) ^ 1265809545 := by rw [pow_add]
          _ = 2423585015 := by rw [factor_8_30]; decide
      have factor_8_32 : (10 : ZMod 116454478141) ^ 5063238180 = 50476043899 := by
        calc
          (10 : ZMod 116454478141) ^ 5063238180 = (10 : ZMod 116454478141) ^ (2531619090 + 2531619090) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2531619090 * (10 : ZMod 116454478141) ^ 2531619090 := by rw [pow_add]
          _ = 50476043899 := by rw [factor_8_31]; decide
      change (10 : ZMod 116454478141) ^ 5063238180 ≠ 1
      rw [factor_8_32]
      decide
    ·
      have factor_9_0 : (10 : ZMod 116454478141) ^ 1 = 10 := by norm_num
      have factor_9_1 : (10 : ZMod 116454478141) ^ 3 = 1000 := by
        calc
          (10 : ZMod 116454478141) ^ 3 = (10 : ZMod 116454478141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1 * (10 : ZMod 116454478141) ^ 1) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_9_0]; decide
      have factor_9_2 : (10 : ZMod 116454478141) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 116454478141) ^ 7 = (10 : ZMod 116454478141) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3 * (10 : ZMod 116454478141) ^ 3) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_9_1]; decide
      have factor_9_3 : (10 : ZMod 116454478141) ^ 14 = 82057755022 := by
        calc
          (10 : ZMod 116454478141) ^ 14 = (10 : ZMod 116454478141) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 7 * (10 : ZMod 116454478141) ^ 7 := by rw [pow_add]
          _ = 82057755022 := by rw [factor_9_2]; decide
      have factor_9_4 : (10 : ZMod 116454478141) ^ 29 = 39979576495 := by
        calc
          (10 : ZMod 116454478141) ^ 29 = (10 : ZMod 116454478141) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 14 * (10 : ZMod 116454478141) ^ 14) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 39979576495 := by rw [factor_9_3]; decide
      have factor_9_5 : (10 : ZMod 116454478141) ^ 59 = 41744154100 := by
        calc
          (10 : ZMod 116454478141) ^ 59 = (10 : ZMod 116454478141) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 29 * (10 : ZMod 116454478141) ^ 29) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 41744154100 := by rw [factor_9_4]; decide
      have factor_9_6 : (10 : ZMod 116454478141) ^ 119 = 47304049457 := by
        calc
          (10 : ZMod 116454478141) ^ 119 = (10 : ZMod 116454478141) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 59 * (10 : ZMod 116454478141) ^ 59) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 47304049457 := by rw [factor_9_5]; decide
      have factor_9_7 : (10 : ZMod 116454478141) ^ 239 = 97953445940 := by
        calc
          (10 : ZMod 116454478141) ^ 239 = (10 : ZMod 116454478141) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 119 * (10 : ZMod 116454478141) ^ 119) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 97953445940 := by rw [factor_9_6]; decide
      have factor_9_8 : (10 : ZMod 116454478141) ^ 478 = 90775438172 := by
        calc
          (10 : ZMod 116454478141) ^ 478 = (10 : ZMod 116454478141) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 239 * (10 : ZMod 116454478141) ^ 239 := by rw [pow_add]
          _ = 90775438172 := by rw [factor_9_7]; decide
      have factor_9_9 : (10 : ZMod 116454478141) ^ 957 = 86911579877 := by
        calc
          (10 : ZMod 116454478141) ^ 957 = (10 : ZMod 116454478141) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 478 * (10 : ZMod 116454478141) ^ 478) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 86911579877 := by rw [factor_9_8]; decide
      have factor_9_10 : (10 : ZMod 116454478141) ^ 1914 = 4129115085 := by
        calc
          (10 : ZMod 116454478141) ^ 1914 = (10 : ZMod 116454478141) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 957 * (10 : ZMod 116454478141) ^ 957 := by rw [pow_add]
          _ = 4129115085 := by rw [factor_9_9]; decide
      have factor_9_11 : (10 : ZMod 116454478141) ^ 3829 = 68748496258 := by
        calc
          (10 : ZMod 116454478141) ^ 3829 = (10 : ZMod 116454478141) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 1914 * (10 : ZMod 116454478141) ^ 1914) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 68748496258 := by rw [factor_9_10]; decide
      have factor_9_12 : (10 : ZMod 116454478141) ^ 7659 = 671634288 := by
        calc
          (10 : ZMod 116454478141) ^ 7659 = (10 : ZMod 116454478141) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 3829 * (10 : ZMod 116454478141) ^ 3829) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 671634288 := by rw [factor_9_11]; decide
      have factor_9_13 : (10 : ZMod 116454478141) ^ 15318 = 23650761971 := by
        calc
          (10 : ZMod 116454478141) ^ 15318 = (10 : ZMod 116454478141) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 7659 * (10 : ZMod 116454478141) ^ 7659 := by rw [pow_add]
          _ = 23650761971 := by rw [factor_9_12]; decide
      have factor_9_14 : (10 : ZMod 116454478141) ^ 30637 = 69784260453 := by
        calc
          (10 : ZMod 116454478141) ^ 30637 = (10 : ZMod 116454478141) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 15318 * (10 : ZMod 116454478141) ^ 15318) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 69784260453 := by rw [factor_9_13]; decide
      have factor_9_15 : (10 : ZMod 116454478141) ^ 61274 = 112146971813 := by
        calc
          (10 : ZMod 116454478141) ^ 61274 = (10 : ZMod 116454478141) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 30637 * (10 : ZMod 116454478141) ^ 30637 := by rw [pow_add]
          _ = 112146971813 := by rw [factor_9_14]; decide
      have factor_9_16 : (10 : ZMod 116454478141) ^ 122548 = 48780256002 := by
        calc
          (10 : ZMod 116454478141) ^ 122548 = (10 : ZMod 116454478141) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 61274 * (10 : ZMod 116454478141) ^ 61274 := by rw [pow_add]
          _ = 48780256002 := by rw [factor_9_15]; decide
      have factor_9_17 : (10 : ZMod 116454478141) ^ 245097 = 34942800070 := by
        calc
          (10 : ZMod 116454478141) ^ 245097 = (10 : ZMod 116454478141) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 122548 * (10 : ZMod 116454478141) ^ 122548) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 34942800070 := by rw [factor_9_16]; decide
      have factor_9_18 : (10 : ZMod 116454478141) ^ 490194 = 33438970153 := by
        calc
          (10 : ZMod 116454478141) ^ 490194 = (10 : ZMod 116454478141) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 245097 * (10 : ZMod 116454478141) ^ 245097 := by rw [pow_add]
          _ = 33438970153 := by rw [factor_9_17]; decide
      have factor_9_19 : (10 : ZMod 116454478141) ^ 980388 = 64868798404 := by
        calc
          (10 : ZMod 116454478141) ^ 980388 = (10 : ZMod 116454478141) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 490194 * (10 : ZMod 116454478141) ^ 490194 := by rw [pow_add]
          _ = 64868798404 := by rw [factor_9_18]; decide
      have factor_9_20 : (10 : ZMod 116454478141) ^ 1960777 = 53198341621 := by
        calc
          (10 : ZMod 116454478141) ^ 1960777 = (10 : ZMod 116454478141) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 980388 * (10 : ZMod 116454478141) ^ 980388) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 53198341621 := by rw [factor_9_19]; decide
      have factor_9_21 : (10 : ZMod 116454478141) ^ 3921554 = 33331605509 := by
        calc
          (10 : ZMod 116454478141) ^ 3921554 = (10 : ZMod 116454478141) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1960777 * (10 : ZMod 116454478141) ^ 1960777 := by rw [pow_add]
          _ = 33331605509 := by rw [factor_9_20]; decide
      have factor_9_22 : (10 : ZMod 116454478141) ^ 7843108 = 72774076286 := by
        calc
          (10 : ZMod 116454478141) ^ 7843108 = (10 : ZMod 116454478141) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 3921554 * (10 : ZMod 116454478141) ^ 3921554 := by rw [pow_add]
          _ = 72774076286 := by rw [factor_9_21]; decide
      have factor_9_23 : (10 : ZMod 116454478141) ^ 15686217 = 80417190444 := by
        calc
          (10 : ZMod 116454478141) ^ 15686217 = (10 : ZMod 116454478141) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 7843108 * (10 : ZMod 116454478141) ^ 7843108) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 80417190444 := by rw [factor_9_22]; decide
      have factor_9_24 : (10 : ZMod 116454478141) ^ 31372434 = 72686954072 := by
        calc
          (10 : ZMod 116454478141) ^ 31372434 = (10 : ZMod 116454478141) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 15686217 * (10 : ZMod 116454478141) ^ 15686217 := by rw [pow_add]
          _ = 72686954072 := by rw [factor_9_23]; decide
      have factor_9_25 : (10 : ZMod 116454478141) ^ 62744869 = 43828466204 := by
        calc
          (10 : ZMod 116454478141) ^ 62744869 = (10 : ZMod 116454478141) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 31372434 * (10 : ZMod 116454478141) ^ 31372434) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 43828466204 := by rw [factor_9_24]; decide
      have factor_9_26 : (10 : ZMod 116454478141) ^ 125489739 = 104557210745 := by
        calc
          (10 : ZMod 116454478141) ^ 125489739 = (10 : ZMod 116454478141) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 62744869 * (10 : ZMod 116454478141) ^ 62744869) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 104557210745 := by rw [factor_9_25]; decide
      have factor_9_27 : (10 : ZMod 116454478141) ^ 250979478 = 3936253527 := by
        calc
          (10 : ZMod 116454478141) ^ 250979478 = (10 : ZMod 116454478141) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 125489739 * (10 : ZMod 116454478141) ^ 125489739 := by rw [pow_add]
          _ = 3936253527 := by rw [factor_9_26]; decide
      have factor_9_28 : (10 : ZMod 116454478141) ^ 501958957 = 105669602286 := by
        calc
          (10 : ZMod 116454478141) ^ 501958957 = (10 : ZMod 116454478141) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 250979478 * (10 : ZMod 116454478141) ^ 250979478) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 105669602286 := by rw [factor_9_27]; decide
      have factor_9_29 : (10 : ZMod 116454478141) ^ 1003917915 = 53458954755 := by
        calc
          (10 : ZMod 116454478141) ^ 1003917915 = (10 : ZMod 116454478141) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = ((10 : ZMod 116454478141) ^ 501958957 * (10 : ZMod 116454478141) ^ 501958957) * (10 : ZMod 116454478141) := by rw [pow_succ, pow_add]
          _ = 53458954755 := by rw [factor_9_28]; decide
      have factor_9_30 : (10 : ZMod 116454478141) ^ 2007835830 = 4604892843 := by
        calc
          (10 : ZMod 116454478141) ^ 2007835830 = (10 : ZMod 116454478141) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 1003917915 * (10 : ZMod 116454478141) ^ 1003917915 := by rw [pow_add]
          _ = 4604892843 := by rw [factor_9_29]; decide
      have factor_9_31 : (10 : ZMod 116454478141) ^ 4015671660 = 83090291845 := by
        calc
          (10 : ZMod 116454478141) ^ 4015671660 = (10 : ZMod 116454478141) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (10 : ZMod 116454478141) ^ n) (by norm_num)
          _ = (10 : ZMod 116454478141) ^ 2007835830 * (10 : ZMod 116454478141) ^ 2007835830 := by rw [pow_add]
          _ = 83090291845 := by rw [factor_9_30]; decide
      change (10 : ZMod 116454478141) ^ 4015671660 ≠ 1
      rw [factor_9_31]
      decide

#print axioms prime_lucas_116454478141

end TotientTailPeriodKiller
end Erdos249257
