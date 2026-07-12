import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10890527693

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_4857175351079 : Nat.Prime 4857175351079 := by
  apply lucas_primality 4857175351079 (7 : ZMod 4857175351079)
  ·
      have fermat_0 : (7 : ZMod 4857175351079) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 4857175351079) ^ 2 = 49 := by
        calc
          (7 : ZMod 4857175351079) ^ 2 = (7 : ZMod 4857175351079) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 1 * (7 : ZMod 4857175351079) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 4857175351079) ^ 4 = 2401 := by
        calc
          (7 : ZMod 4857175351079) ^ 4 = (7 : ZMod 4857175351079) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 2 * (7 : ZMod 4857175351079) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 4857175351079) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 4857175351079) ^ 8 = (7 : ZMod 4857175351079) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 4 * (7 : ZMod 4857175351079) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 4857175351079) ^ 17 = 4343272486494 := by
        calc
          (7 : ZMod 4857175351079) ^ 17 = (7 : ZMod 4857175351079) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 8 * (7 : ZMod 4857175351079) ^ 8) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4343272486494 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 4857175351079) ^ 35 = 1566564979511 := by
        calc
          (7 : ZMod 4857175351079) ^ 35 = (7 : ZMod 4857175351079) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 17 * (7 : ZMod 4857175351079) ^ 17) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1566564979511 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 4857175351079) ^ 70 = 1493818884032 := by
        calc
          (7 : ZMod 4857175351079) ^ 70 = (7 : ZMod 4857175351079) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 35 * (7 : ZMod 4857175351079) ^ 35 := by rw [pow_add]
          _ = 1493818884032 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 4857175351079) ^ 141 = 1932057859458 := by
        calc
          (7 : ZMod 4857175351079) ^ 141 = (7 : ZMod 4857175351079) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 70 * (7 : ZMod 4857175351079) ^ 70) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1932057859458 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 4857175351079) ^ 282 = 3174195109159 := by
        calc
          (7 : ZMod 4857175351079) ^ 282 = (7 : ZMod 4857175351079) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 141 * (7 : ZMod 4857175351079) ^ 141 := by rw [pow_add]
          _ = 3174195109159 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 4857175351079) ^ 565 = 4024250906754 := by
        calc
          (7 : ZMod 4857175351079) ^ 565 = (7 : ZMod 4857175351079) ^ (282 + 282 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 282 * (7 : ZMod 4857175351079) ^ 282) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4024250906754 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 4857175351079) ^ 1130 = 3750453594623 := by
        calc
          (7 : ZMod 4857175351079) ^ 1130 = (7 : ZMod 4857175351079) ^ (565 + 565) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 565 * (7 : ZMod 4857175351079) ^ 565 := by rw [pow_add]
          _ = 3750453594623 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 4857175351079) ^ 2261 = 2034984042967 := by
        calc
          (7 : ZMod 4857175351079) ^ 2261 = (7 : ZMod 4857175351079) ^ (1130 + 1130 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1130 * (7 : ZMod 4857175351079) ^ 1130) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2034984042967 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 4857175351079) ^ 4523 = 2201559983480 := by
        calc
          (7 : ZMod 4857175351079) ^ 4523 = (7 : ZMod 4857175351079) ^ (2261 + 2261 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2261 * (7 : ZMod 4857175351079) ^ 2261) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2201559983480 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 4857175351079) ^ 9047 = 2936672574813 := by
        calc
          (7 : ZMod 4857175351079) ^ 9047 = (7 : ZMod 4857175351079) ^ (4523 + 4523 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 4523 * (7 : ZMod 4857175351079) ^ 4523) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2936672574813 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 4857175351079) ^ 18094 = 980511137078 := by
        calc
          (7 : ZMod 4857175351079) ^ 18094 = (7 : ZMod 4857175351079) ^ (9047 + 9047) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 9047 * (7 : ZMod 4857175351079) ^ 9047 := by rw [pow_add]
          _ = 980511137078 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 4857175351079) ^ 36188 = 1373782678835 := by
        calc
          (7 : ZMod 4857175351079) ^ 36188 = (7 : ZMod 4857175351079) ^ (18094 + 18094) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 18094 * (7 : ZMod 4857175351079) ^ 18094 := by rw [pow_add]
          _ = 1373782678835 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 4857175351079) ^ 72377 = 3909380269006 := by
        calc
          (7 : ZMod 4857175351079) ^ 72377 = (7 : ZMod 4857175351079) ^ (36188 + 36188 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 36188 * (7 : ZMod 4857175351079) ^ 36188) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3909380269006 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 4857175351079) ^ 144755 = 2086766071503 := by
        calc
          (7 : ZMod 4857175351079) ^ 144755 = (7 : ZMod 4857175351079) ^ (72377 + 72377 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 72377 * (7 : ZMod 4857175351079) ^ 72377) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2086766071503 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 4857175351079) ^ 289510 = 3898421231744 := by
        calc
          (7 : ZMod 4857175351079) ^ 289510 = (7 : ZMod 4857175351079) ^ (144755 + 144755) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 144755 * (7 : ZMod 4857175351079) ^ 144755 := by rw [pow_add]
          _ = 3898421231744 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 4857175351079) ^ 579020 = 401591084478 := by
        calc
          (7 : ZMod 4857175351079) ^ 579020 = (7 : ZMod 4857175351079) ^ (289510 + 289510) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 289510 * (7 : ZMod 4857175351079) ^ 289510 := by rw [pow_add]
          _ = 401591084478 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 4857175351079) ^ 1158040 = 2906611382799 := by
        calc
          (7 : ZMod 4857175351079) ^ 1158040 = (7 : ZMod 4857175351079) ^ (579020 + 579020) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 579020 * (7 : ZMod 4857175351079) ^ 579020 := by rw [pow_add]
          _ = 2906611382799 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 4857175351079) ^ 2316081 = 912841265931 := by
        calc
          (7 : ZMod 4857175351079) ^ 2316081 = (7 : ZMod 4857175351079) ^ (1158040 + 1158040 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1158040 * (7 : ZMod 4857175351079) ^ 1158040) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 912841265931 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 4857175351079) ^ 4632163 = 1722652887926 := by
        calc
          (7 : ZMod 4857175351079) ^ 4632163 = (7 : ZMod 4857175351079) ^ (2316081 + 2316081 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2316081 * (7 : ZMod 4857175351079) ^ 2316081) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1722652887926 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 4857175351079) ^ 9264326 = 2589932091450 := by
        calc
          (7 : ZMod 4857175351079) ^ 9264326 = (7 : ZMod 4857175351079) ^ (4632163 + 4632163) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 4632163 * (7 : ZMod 4857175351079) ^ 4632163 := by rw [pow_add]
          _ = 2589932091450 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 4857175351079) ^ 18528653 = 1036605035091 := by
        calc
          (7 : ZMod 4857175351079) ^ 18528653 = (7 : ZMod 4857175351079) ^ (9264326 + 9264326 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 9264326 * (7 : ZMod 4857175351079) ^ 9264326) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1036605035091 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 4857175351079) ^ 37057307 = 784714896012 := by
        calc
          (7 : ZMod 4857175351079) ^ 37057307 = (7 : ZMod 4857175351079) ^ (18528653 + 18528653 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 18528653 * (7 : ZMod 4857175351079) ^ 18528653) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 784714896012 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 4857175351079) ^ 74114614 = 3168378623940 := by
        calc
          (7 : ZMod 4857175351079) ^ 74114614 = (7 : ZMod 4857175351079) ^ (37057307 + 37057307) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 37057307 * (7 : ZMod 4857175351079) ^ 37057307 := by rw [pow_add]
          _ = 3168378623940 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 4857175351079) ^ 148229228 = 549032118227 := by
        calc
          (7 : ZMod 4857175351079) ^ 148229228 = (7 : ZMod 4857175351079) ^ (74114614 + 74114614) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 74114614 * (7 : ZMod 4857175351079) ^ 74114614 := by rw [pow_add]
          _ = 549032118227 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 4857175351079) ^ 296458456 = 4529477798071 := by
        calc
          (7 : ZMod 4857175351079) ^ 296458456 = (7 : ZMod 4857175351079) ^ (148229228 + 148229228) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 148229228 * (7 : ZMod 4857175351079) ^ 148229228 := by rw [pow_add]
          _ = 4529477798071 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 4857175351079) ^ 592916912 = 2010342228835 := by
        calc
          (7 : ZMod 4857175351079) ^ 592916912 = (7 : ZMod 4857175351079) ^ (296458456 + 296458456) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 296458456 * (7 : ZMod 4857175351079) ^ 296458456 := by rw [pow_add]
          _ = 2010342228835 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 4857175351079) ^ 1185833825 = 664980053320 := by
        calc
          (7 : ZMod 4857175351079) ^ 1185833825 = (7 : ZMod 4857175351079) ^ (592916912 + 592916912 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 592916912 * (7 : ZMod 4857175351079) ^ 592916912) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 664980053320 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 4857175351079) ^ 2371667651 = 4332211653257 := by
        calc
          (7 : ZMod 4857175351079) ^ 2371667651 = (7 : ZMod 4857175351079) ^ (1185833825 + 1185833825 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1185833825 * (7 : ZMod 4857175351079) ^ 1185833825) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4332211653257 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 4857175351079) ^ 4743335303 = 3176576712559 := by
        calc
          (7 : ZMod 4857175351079) ^ 4743335303 = (7 : ZMod 4857175351079) ^ (2371667651 + 2371667651 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2371667651 * (7 : ZMod 4857175351079) ^ 2371667651) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3176576712559 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 4857175351079) ^ 9486670607 = 4301539904929 := by
        calc
          (7 : ZMod 4857175351079) ^ 9486670607 = (7 : ZMod 4857175351079) ^ (4743335303 + 4743335303 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 4743335303 * (7 : ZMod 4857175351079) ^ 4743335303) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4301539904929 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 4857175351079) ^ 18973341215 = 3733157683965 := by
        calc
          (7 : ZMod 4857175351079) ^ 18973341215 = (7 : ZMod 4857175351079) ^ (9486670607 + 9486670607 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 9486670607 * (7 : ZMod 4857175351079) ^ 9486670607) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3733157683965 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 4857175351079) ^ 37946682430 = 3588885822406 := by
        calc
          (7 : ZMod 4857175351079) ^ 37946682430 = (7 : ZMod 4857175351079) ^ (18973341215 + 18973341215) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 18973341215 * (7 : ZMod 4857175351079) ^ 18973341215 := by rw [pow_add]
          _ = 3588885822406 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 4857175351079) ^ 75893364860 = 1836499899218 := by
        calc
          (7 : ZMod 4857175351079) ^ 75893364860 = (7 : ZMod 4857175351079) ^ (37946682430 + 37946682430) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 37946682430 * (7 : ZMod 4857175351079) ^ 37946682430 := by rw [pow_add]
          _ = 1836499899218 := by rw [fermat_35]; decide
      have fermat_37 : (7 : ZMod 4857175351079) ^ 151786729721 = 3350315665390 := by
        calc
          (7 : ZMod 4857175351079) ^ 151786729721 = (7 : ZMod 4857175351079) ^ (75893364860 + 75893364860 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 75893364860 * (7 : ZMod 4857175351079) ^ 75893364860) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3350315665390 := by rw [fermat_36]; decide
      have fermat_38 : (7 : ZMod 4857175351079) ^ 303573459442 = 1385741621023 := by
        calc
          (7 : ZMod 4857175351079) ^ 303573459442 = (7 : ZMod 4857175351079) ^ (151786729721 + 151786729721) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 151786729721 * (7 : ZMod 4857175351079) ^ 151786729721 := by rw [pow_add]
          _ = 1385741621023 := by rw [fermat_37]; decide
      have fermat_39 : (7 : ZMod 4857175351079) ^ 607146918884 = 1180356141005 := by
        calc
          (7 : ZMod 4857175351079) ^ 607146918884 = (7 : ZMod 4857175351079) ^ (303573459442 + 303573459442) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 303573459442 * (7 : ZMod 4857175351079) ^ 303573459442 := by rw [pow_add]
          _ = 1180356141005 := by rw [fermat_38]; decide
      have fermat_40 : (7 : ZMod 4857175351079) ^ 1214293837769 = 249506997928 := by
        calc
          (7 : ZMod 4857175351079) ^ 1214293837769 = (7 : ZMod 4857175351079) ^ (607146918884 + 607146918884 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 607146918884 * (7 : ZMod 4857175351079) ^ 607146918884) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 249506997928 := by rw [fermat_39]; decide
      have fermat_41 : (7 : ZMod 4857175351079) ^ 2428587675539 = 4857175351078 := by
        calc
          (7 : ZMod 4857175351079) ^ 2428587675539 = (7 : ZMod 4857175351079) ^ (1214293837769 + 1214293837769 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1214293837769 * (7 : ZMod 4857175351079) ^ 1214293837769) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4857175351078 := by rw [fermat_40]; decide
      have fermat_42 : (7 : ZMod 4857175351079) ^ 4857175351078 = 1 := by
        calc
          (7 : ZMod 4857175351079) ^ 4857175351078 = (7 : ZMod 4857175351079) ^ (2428587675539 + 2428587675539) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 2428587675539 * (7 : ZMod 4857175351079) ^ 2428587675539 := by rw [pow_add]
          _ = 1 := by rw [fermat_41]; decide
      simpa using fermat_42
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (223, 1), (10890527693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (223, 1), (10890527693, 1)] : List FactorBlock).map factorBlockValue).prod = 4857175351079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_10890527693) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 4857175351079) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 4857175351079) ^ 2 = 49 := by
        calc
          (7 : ZMod 4857175351079) ^ 2 = (7 : ZMod 4857175351079) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 1 * (7 : ZMod 4857175351079) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 4857175351079) ^ 4 = 2401 := by
        calc
          (7 : ZMod 4857175351079) ^ 4 = (7 : ZMod 4857175351079) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 2 * (7 : ZMod 4857175351079) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 4857175351079) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 4857175351079) ^ 8 = (7 : ZMod 4857175351079) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 4 * (7 : ZMod 4857175351079) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 4857175351079) ^ 17 = 4343272486494 := by
        calc
          (7 : ZMod 4857175351079) ^ 17 = (7 : ZMod 4857175351079) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 8 * (7 : ZMod 4857175351079) ^ 8) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4343272486494 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 4857175351079) ^ 35 = 1566564979511 := by
        calc
          (7 : ZMod 4857175351079) ^ 35 = (7 : ZMod 4857175351079) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 17 * (7 : ZMod 4857175351079) ^ 17) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1566564979511 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 4857175351079) ^ 70 = 1493818884032 := by
        calc
          (7 : ZMod 4857175351079) ^ 70 = (7 : ZMod 4857175351079) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 35 * (7 : ZMod 4857175351079) ^ 35 := by rw [pow_add]
          _ = 1493818884032 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 4857175351079) ^ 141 = 1932057859458 := by
        calc
          (7 : ZMod 4857175351079) ^ 141 = (7 : ZMod 4857175351079) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 70 * (7 : ZMod 4857175351079) ^ 70) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1932057859458 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 4857175351079) ^ 282 = 3174195109159 := by
        calc
          (7 : ZMod 4857175351079) ^ 282 = (7 : ZMod 4857175351079) ^ (141 + 141) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 141 * (7 : ZMod 4857175351079) ^ 141 := by rw [pow_add]
          _ = 3174195109159 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 4857175351079) ^ 565 = 4024250906754 := by
        calc
          (7 : ZMod 4857175351079) ^ 565 = (7 : ZMod 4857175351079) ^ (282 + 282 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 282 * (7 : ZMod 4857175351079) ^ 282) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4024250906754 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 4857175351079) ^ 1130 = 3750453594623 := by
        calc
          (7 : ZMod 4857175351079) ^ 1130 = (7 : ZMod 4857175351079) ^ (565 + 565) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 565 * (7 : ZMod 4857175351079) ^ 565 := by rw [pow_add]
          _ = 3750453594623 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 4857175351079) ^ 2261 = 2034984042967 := by
        calc
          (7 : ZMod 4857175351079) ^ 2261 = (7 : ZMod 4857175351079) ^ (1130 + 1130 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1130 * (7 : ZMod 4857175351079) ^ 1130) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2034984042967 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 4857175351079) ^ 4523 = 2201559983480 := by
        calc
          (7 : ZMod 4857175351079) ^ 4523 = (7 : ZMod 4857175351079) ^ (2261 + 2261 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2261 * (7 : ZMod 4857175351079) ^ 2261) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2201559983480 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 4857175351079) ^ 9047 = 2936672574813 := by
        calc
          (7 : ZMod 4857175351079) ^ 9047 = (7 : ZMod 4857175351079) ^ (4523 + 4523 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 4523 * (7 : ZMod 4857175351079) ^ 4523) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2936672574813 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 4857175351079) ^ 18094 = 980511137078 := by
        calc
          (7 : ZMod 4857175351079) ^ 18094 = (7 : ZMod 4857175351079) ^ (9047 + 9047) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 9047 * (7 : ZMod 4857175351079) ^ 9047 := by rw [pow_add]
          _ = 980511137078 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 4857175351079) ^ 36188 = 1373782678835 := by
        calc
          (7 : ZMod 4857175351079) ^ 36188 = (7 : ZMod 4857175351079) ^ (18094 + 18094) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 18094 * (7 : ZMod 4857175351079) ^ 18094 := by rw [pow_add]
          _ = 1373782678835 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 4857175351079) ^ 72377 = 3909380269006 := by
        calc
          (7 : ZMod 4857175351079) ^ 72377 = (7 : ZMod 4857175351079) ^ (36188 + 36188 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 36188 * (7 : ZMod 4857175351079) ^ 36188) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3909380269006 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 4857175351079) ^ 144755 = 2086766071503 := by
        calc
          (7 : ZMod 4857175351079) ^ 144755 = (7 : ZMod 4857175351079) ^ (72377 + 72377 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 72377 * (7 : ZMod 4857175351079) ^ 72377) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2086766071503 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 4857175351079) ^ 289510 = 3898421231744 := by
        calc
          (7 : ZMod 4857175351079) ^ 289510 = (7 : ZMod 4857175351079) ^ (144755 + 144755) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 144755 * (7 : ZMod 4857175351079) ^ 144755 := by rw [pow_add]
          _ = 3898421231744 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 4857175351079) ^ 579020 = 401591084478 := by
        calc
          (7 : ZMod 4857175351079) ^ 579020 = (7 : ZMod 4857175351079) ^ (289510 + 289510) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 289510 * (7 : ZMod 4857175351079) ^ 289510 := by rw [pow_add]
          _ = 401591084478 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 4857175351079) ^ 1158040 = 2906611382799 := by
        calc
          (7 : ZMod 4857175351079) ^ 1158040 = (7 : ZMod 4857175351079) ^ (579020 + 579020) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 579020 * (7 : ZMod 4857175351079) ^ 579020 := by rw [pow_add]
          _ = 2906611382799 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 4857175351079) ^ 2316081 = 912841265931 := by
        calc
          (7 : ZMod 4857175351079) ^ 2316081 = (7 : ZMod 4857175351079) ^ (1158040 + 1158040 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1158040 * (7 : ZMod 4857175351079) ^ 1158040) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 912841265931 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 4857175351079) ^ 4632163 = 1722652887926 := by
        calc
          (7 : ZMod 4857175351079) ^ 4632163 = (7 : ZMod 4857175351079) ^ (2316081 + 2316081 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2316081 * (7 : ZMod 4857175351079) ^ 2316081) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1722652887926 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 4857175351079) ^ 9264326 = 2589932091450 := by
        calc
          (7 : ZMod 4857175351079) ^ 9264326 = (7 : ZMod 4857175351079) ^ (4632163 + 4632163) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 4632163 * (7 : ZMod 4857175351079) ^ 4632163 := by rw [pow_add]
          _ = 2589932091450 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 4857175351079) ^ 18528653 = 1036605035091 := by
        calc
          (7 : ZMod 4857175351079) ^ 18528653 = (7 : ZMod 4857175351079) ^ (9264326 + 9264326 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 9264326 * (7 : ZMod 4857175351079) ^ 9264326) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1036605035091 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 4857175351079) ^ 37057307 = 784714896012 := by
        calc
          (7 : ZMod 4857175351079) ^ 37057307 = (7 : ZMod 4857175351079) ^ (18528653 + 18528653 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 18528653 * (7 : ZMod 4857175351079) ^ 18528653) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 784714896012 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 4857175351079) ^ 74114614 = 3168378623940 := by
        calc
          (7 : ZMod 4857175351079) ^ 74114614 = (7 : ZMod 4857175351079) ^ (37057307 + 37057307) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 37057307 * (7 : ZMod 4857175351079) ^ 37057307 := by rw [pow_add]
          _ = 3168378623940 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 4857175351079) ^ 148229228 = 549032118227 := by
        calc
          (7 : ZMod 4857175351079) ^ 148229228 = (7 : ZMod 4857175351079) ^ (74114614 + 74114614) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 74114614 * (7 : ZMod 4857175351079) ^ 74114614 := by rw [pow_add]
          _ = 549032118227 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 4857175351079) ^ 296458456 = 4529477798071 := by
        calc
          (7 : ZMod 4857175351079) ^ 296458456 = (7 : ZMod 4857175351079) ^ (148229228 + 148229228) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 148229228 * (7 : ZMod 4857175351079) ^ 148229228 := by rw [pow_add]
          _ = 4529477798071 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 4857175351079) ^ 592916912 = 2010342228835 := by
        calc
          (7 : ZMod 4857175351079) ^ 592916912 = (7 : ZMod 4857175351079) ^ (296458456 + 296458456) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 296458456 * (7 : ZMod 4857175351079) ^ 296458456 := by rw [pow_add]
          _ = 2010342228835 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 4857175351079) ^ 1185833825 = 664980053320 := by
        calc
          (7 : ZMod 4857175351079) ^ 1185833825 = (7 : ZMod 4857175351079) ^ (592916912 + 592916912 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 592916912 * (7 : ZMod 4857175351079) ^ 592916912) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 664980053320 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 4857175351079) ^ 2371667651 = 4332211653257 := by
        calc
          (7 : ZMod 4857175351079) ^ 2371667651 = (7 : ZMod 4857175351079) ^ (1185833825 + 1185833825 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1185833825 * (7 : ZMod 4857175351079) ^ 1185833825) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4332211653257 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 4857175351079) ^ 4743335303 = 3176576712559 := by
        calc
          (7 : ZMod 4857175351079) ^ 4743335303 = (7 : ZMod 4857175351079) ^ (2371667651 + 2371667651 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2371667651 * (7 : ZMod 4857175351079) ^ 2371667651) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3176576712559 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 4857175351079) ^ 9486670607 = 4301539904929 := by
        calc
          (7 : ZMod 4857175351079) ^ 9486670607 = (7 : ZMod 4857175351079) ^ (4743335303 + 4743335303 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 4743335303 * (7 : ZMod 4857175351079) ^ 4743335303) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4301539904929 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 4857175351079) ^ 18973341215 = 3733157683965 := by
        calc
          (7 : ZMod 4857175351079) ^ 18973341215 = (7 : ZMod 4857175351079) ^ (9486670607 + 9486670607 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 9486670607 * (7 : ZMod 4857175351079) ^ 9486670607) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3733157683965 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 4857175351079) ^ 37946682430 = 3588885822406 := by
        calc
          (7 : ZMod 4857175351079) ^ 37946682430 = (7 : ZMod 4857175351079) ^ (18973341215 + 18973341215) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 18973341215 * (7 : ZMod 4857175351079) ^ 18973341215 := by rw [pow_add]
          _ = 3588885822406 := by rw [factor_0_34]; decide
      have factor_0_36 : (7 : ZMod 4857175351079) ^ 75893364860 = 1836499899218 := by
        calc
          (7 : ZMod 4857175351079) ^ 75893364860 = (7 : ZMod 4857175351079) ^ (37946682430 + 37946682430) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 37946682430 * (7 : ZMod 4857175351079) ^ 37946682430 := by rw [pow_add]
          _ = 1836499899218 := by rw [factor_0_35]; decide
      have factor_0_37 : (7 : ZMod 4857175351079) ^ 151786729721 = 3350315665390 := by
        calc
          (7 : ZMod 4857175351079) ^ 151786729721 = (7 : ZMod 4857175351079) ^ (75893364860 + 75893364860 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 75893364860 * (7 : ZMod 4857175351079) ^ 75893364860) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3350315665390 := by rw [factor_0_36]; decide
      have factor_0_38 : (7 : ZMod 4857175351079) ^ 303573459442 = 1385741621023 := by
        calc
          (7 : ZMod 4857175351079) ^ 303573459442 = (7 : ZMod 4857175351079) ^ (151786729721 + 151786729721) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 151786729721 * (7 : ZMod 4857175351079) ^ 151786729721 := by rw [pow_add]
          _ = 1385741621023 := by rw [factor_0_37]; decide
      have factor_0_39 : (7 : ZMod 4857175351079) ^ 607146918884 = 1180356141005 := by
        calc
          (7 : ZMod 4857175351079) ^ 607146918884 = (7 : ZMod 4857175351079) ^ (303573459442 + 303573459442) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 303573459442 * (7 : ZMod 4857175351079) ^ 303573459442 := by rw [pow_add]
          _ = 1180356141005 := by rw [factor_0_38]; decide
      have factor_0_40 : (7 : ZMod 4857175351079) ^ 1214293837769 = 249506997928 := by
        calc
          (7 : ZMod 4857175351079) ^ 1214293837769 = (7 : ZMod 4857175351079) ^ (607146918884 + 607146918884 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 607146918884 * (7 : ZMod 4857175351079) ^ 607146918884) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 249506997928 := by rw [factor_0_39]; decide
      have factor_0_41 : (7 : ZMod 4857175351079) ^ 2428587675539 = 4857175351078 := by
        calc
          (7 : ZMod 4857175351079) ^ 2428587675539 = (7 : ZMod 4857175351079) ^ (1214293837769 + 1214293837769 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1214293837769 * (7 : ZMod 4857175351079) ^ 1214293837769) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 4857175351078 := by rw [factor_0_40]; decide
      change (7 : ZMod 4857175351079) ^ 2428587675539 ≠ 1
      rw [factor_0_41]
      decide
    ·
      have factor_1_0 : (7 : ZMod 4857175351079) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 4857175351079) ^ 2 = 49 := by
        calc
          (7 : ZMod 4857175351079) ^ 2 = (7 : ZMod 4857175351079) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 1 * (7 : ZMod 4857175351079) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 4857175351079) ^ 5 = 16807 := by
        calc
          (7 : ZMod 4857175351079) ^ 5 = (7 : ZMod 4857175351079) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2 * (7 : ZMod 4857175351079) ^ 2) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 4857175351079) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 4857175351079) ^ 10 = (7 : ZMod 4857175351079) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 5 * (7 : ZMod 4857175351079) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 4857175351079) ^ 20 = 3446805437268 := by
        calc
          (7 : ZMod 4857175351079) ^ 20 = (7 : ZMod 4857175351079) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 10 * (7 : ZMod 4857175351079) ^ 10 := by rw [pow_add]
          _ = 3446805437268 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 4857175351079) ^ 40 = 3367207793197 := by
        calc
          (7 : ZMod 4857175351079) ^ 40 = (7 : ZMod 4857175351079) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 20 * (7 : ZMod 4857175351079) ^ 20 := by rw [pow_add]
          _ = 3367207793197 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 4857175351079) ^ 81 = 2231572727979 := by
        calc
          (7 : ZMod 4857175351079) ^ 81 = (7 : ZMod 4857175351079) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 40 * (7 : ZMod 4857175351079) ^ 40) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2231572727979 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 4857175351079) ^ 162 = 2971812018781 := by
        calc
          (7 : ZMod 4857175351079) ^ 162 = (7 : ZMod 4857175351079) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 81 * (7 : ZMod 4857175351079) ^ 81 := by rw [pow_add]
          _ = 2971812018781 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 4857175351079) ^ 324 = 2027206696286 := by
        calc
          (7 : ZMod 4857175351079) ^ 324 = (7 : ZMod 4857175351079) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 162 * (7 : ZMod 4857175351079) ^ 162 := by rw [pow_add]
          _ = 2027206696286 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 4857175351079) ^ 649 = 3596230351759 := by
        calc
          (7 : ZMod 4857175351079) ^ 649 = (7 : ZMod 4857175351079) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 324 * (7 : ZMod 4857175351079) ^ 324) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3596230351759 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 4857175351079) ^ 1298 = 748729449461 := by
        calc
          (7 : ZMod 4857175351079) ^ 1298 = (7 : ZMod 4857175351079) ^ (649 + 649) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 649 * (7 : ZMod 4857175351079) ^ 649 := by rw [pow_add]
          _ = 748729449461 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 4857175351079) ^ 2596 = 2354380411739 := by
        calc
          (7 : ZMod 4857175351079) ^ 2596 = (7 : ZMod 4857175351079) ^ (1298 + 1298) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 1298 * (7 : ZMod 4857175351079) ^ 1298 := by rw [pow_add]
          _ = 2354380411739 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 4857175351079) ^ 5193 = 3265876922552 := by
        calc
          (7 : ZMod 4857175351079) ^ 5193 = (7 : ZMod 4857175351079) ^ (2596 + 2596 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 2596 * (7 : ZMod 4857175351079) ^ 2596) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3265876922552 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 4857175351079) ^ 10386 = 4768513392379 := by
        calc
          (7 : ZMod 4857175351079) ^ 10386 = (7 : ZMod 4857175351079) ^ (5193 + 5193) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 5193 * (7 : ZMod 4857175351079) ^ 5193 := by rw [pow_add]
          _ = 4768513392379 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 4857175351079) ^ 20772 = 3444248073837 := by
        calc
          (7 : ZMod 4857175351079) ^ 20772 = (7 : ZMod 4857175351079) ^ (10386 + 10386) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 10386 * (7 : ZMod 4857175351079) ^ 10386 := by rw [pow_add]
          _ = 3444248073837 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 4857175351079) ^ 41544 = 1764640230161 := by
        calc
          (7 : ZMod 4857175351079) ^ 41544 = (7 : ZMod 4857175351079) ^ (20772 + 20772) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 20772 * (7 : ZMod 4857175351079) ^ 20772 := by rw [pow_add]
          _ = 1764640230161 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 4857175351079) ^ 83088 = 3674061321388 := by
        calc
          (7 : ZMod 4857175351079) ^ 83088 = (7 : ZMod 4857175351079) ^ (41544 + 41544) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 41544 * (7 : ZMod 4857175351079) ^ 41544 := by rw [pow_add]
          _ = 3674061321388 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 4857175351079) ^ 166176 = 4071957397699 := by
        calc
          (7 : ZMod 4857175351079) ^ 166176 = (7 : ZMod 4857175351079) ^ (83088 + 83088) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 83088 * (7 : ZMod 4857175351079) ^ 83088 := by rw [pow_add]
          _ = 4071957397699 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 4857175351079) ^ 332352 = 1733116559730 := by
        calc
          (7 : ZMod 4857175351079) ^ 332352 = (7 : ZMod 4857175351079) ^ (166176 + 166176) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 166176 * (7 : ZMod 4857175351079) ^ 166176 := by rw [pow_add]
          _ = 1733116559730 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 4857175351079) ^ 664705 = 1351694368468 := by
        calc
          (7 : ZMod 4857175351079) ^ 664705 = (7 : ZMod 4857175351079) ^ (332352 + 332352 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 332352 * (7 : ZMod 4857175351079) ^ 332352) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1351694368468 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 4857175351079) ^ 1329410 = 2930793218927 := by
        calc
          (7 : ZMod 4857175351079) ^ 1329410 = (7 : ZMod 4857175351079) ^ (664705 + 664705) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 664705 * (7 : ZMod 4857175351079) ^ 664705 := by rw [pow_add]
          _ = 2930793218927 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 4857175351079) ^ 2658820 = 2731001683225 := by
        calc
          (7 : ZMod 4857175351079) ^ 2658820 = (7 : ZMod 4857175351079) ^ (1329410 + 1329410) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 1329410 * (7 : ZMod 4857175351079) ^ 1329410 := by rw [pow_add]
          _ = 2731001683225 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 4857175351079) ^ 5317640 = 2054038202837 := by
        calc
          (7 : ZMod 4857175351079) ^ 5317640 = (7 : ZMod 4857175351079) ^ (2658820 + 2658820) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 2658820 * (7 : ZMod 4857175351079) ^ 2658820 := by rw [pow_add]
          _ = 2054038202837 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 4857175351079) ^ 10635280 = 3508725326290 := by
        calc
          (7 : ZMod 4857175351079) ^ 10635280 = (7 : ZMod 4857175351079) ^ (5317640 + 5317640) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 5317640 * (7 : ZMod 4857175351079) ^ 5317640 := by rw [pow_add]
          _ = 3508725326290 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 4857175351079) ^ 21270561 = 1086067535150 := by
        calc
          (7 : ZMod 4857175351079) ^ 21270561 = (7 : ZMod 4857175351079) ^ (10635280 + 10635280 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 10635280 * (7 : ZMod 4857175351079) ^ 10635280) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1086067535150 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 4857175351079) ^ 42541123 = 2281466257481 := by
        calc
          (7 : ZMod 4857175351079) ^ 42541123 = (7 : ZMod 4857175351079) ^ (21270561 + 21270561 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 21270561 * (7 : ZMod 4857175351079) ^ 21270561) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2281466257481 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 4857175351079) ^ 85082247 = 2003441120767 := by
        calc
          (7 : ZMod 4857175351079) ^ 85082247 = (7 : ZMod 4857175351079) ^ (42541123 + 42541123 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 42541123 * (7 : ZMod 4857175351079) ^ 42541123) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2003441120767 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 4857175351079) ^ 170164495 = 2943390048372 := by
        calc
          (7 : ZMod 4857175351079) ^ 170164495 = (7 : ZMod 4857175351079) ^ (85082247 + 85082247 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 85082247 * (7 : ZMod 4857175351079) ^ 85082247) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2943390048372 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 4857175351079) ^ 340328990 = 3542481229879 := by
        calc
          (7 : ZMod 4857175351079) ^ 340328990 = (7 : ZMod 4857175351079) ^ (170164495 + 170164495) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 170164495 * (7 : ZMod 4857175351079) ^ 170164495 := by rw [pow_add]
          _ = 3542481229879 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 4857175351079) ^ 680657980 = 4703606083129 := by
        calc
          (7 : ZMod 4857175351079) ^ 680657980 = (7 : ZMod 4857175351079) ^ (340328990 + 340328990) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 340328990 * (7 : ZMod 4857175351079) ^ 340328990 := by rw [pow_add]
          _ = 4703606083129 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 4857175351079) ^ 1361315961 = 1917519332246 := by
        calc
          (7 : ZMod 4857175351079) ^ 1361315961 = (7 : ZMod 4857175351079) ^ (680657980 + 680657980 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 680657980 * (7 : ZMod 4857175351079) ^ 680657980) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 1917519332246 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 4857175351079) ^ 2722631923 = 3104720820104 := by
        calc
          (7 : ZMod 4857175351079) ^ 2722631923 = (7 : ZMod 4857175351079) ^ (1361315961 + 1361315961 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1361315961 * (7 : ZMod 4857175351079) ^ 1361315961) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 3104720820104 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 4857175351079) ^ 5445263846 = 2848458924204 := by
        calc
          (7 : ZMod 4857175351079) ^ 5445263846 = (7 : ZMod 4857175351079) ^ (2722631923 + 2722631923) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 2722631923 * (7 : ZMod 4857175351079) ^ 2722631923 := by rw [pow_add]
          _ = 2848458924204 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 4857175351079) ^ 10890527693 = 2661137418638 := by
        calc
          (7 : ZMod 4857175351079) ^ 10890527693 = (7 : ZMod 4857175351079) ^ (5445263846 + 5445263846 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 5445263846 * (7 : ZMod 4857175351079) ^ 5445263846) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2661137418638 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 4857175351079) ^ 21781055386 = 4489874458807 := by
        calc
          (7 : ZMod 4857175351079) ^ 21781055386 = (7 : ZMod 4857175351079) ^ (10890527693 + 10890527693) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 10890527693 * (7 : ZMod 4857175351079) ^ 10890527693 := by rw [pow_add]
          _ = 4489874458807 := by rw [factor_1_33]; decide
      change (7 : ZMod 4857175351079) ^ 21781055386 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (7 : ZMod 4857175351079) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 4857175351079) ^ 3 = 343 := by
        calc
          (7 : ZMod 4857175351079) ^ 3 = (7 : ZMod 4857175351079) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 1 * (7 : ZMod 4857175351079) ^ 1) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 4857175351079) ^ 6 = 117649 := by
        calc
          (7 : ZMod 4857175351079) ^ 6 = (7 : ZMod 4857175351079) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 3 * (7 : ZMod 4857175351079) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 4857175351079) ^ 13 = 96889010407 := by
        calc
          (7 : ZMod 4857175351079) ^ 13 = (7 : ZMod 4857175351079) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 6 * (7 : ZMod 4857175351079) ^ 6) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 96889010407 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 4857175351079) ^ 27 = 928949219976 := by
        calc
          (7 : ZMod 4857175351079) ^ 27 = (7 : ZMod 4857175351079) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 13 * (7 : ZMod 4857175351079) ^ 13) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 928949219976 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 4857175351079) ^ 55 = 2881403132602 := by
        calc
          (7 : ZMod 4857175351079) ^ 55 = (7 : ZMod 4857175351079) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 27 * (7 : ZMod 4857175351079) ^ 27) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2881403132602 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 4857175351079) ^ 111 = 657000735218 := by
        calc
          (7 : ZMod 4857175351079) ^ 111 = (7 : ZMod 4857175351079) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 55 * (7 : ZMod 4857175351079) ^ 55) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 657000735218 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 4857175351079) ^ 223 = 2585275955880 := by
        calc
          (7 : ZMod 4857175351079) ^ 223 = (7 : ZMod 4857175351079) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = ((7 : ZMod 4857175351079) ^ 111 * (7 : ZMod 4857175351079) ^ 111) * (7 : ZMod 4857175351079) := by rw [pow_succ, pow_add]
          _ = 2585275955880 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 4857175351079) ^ 446 = 214401279339 := by
        calc
          (7 : ZMod 4857175351079) ^ 446 = (7 : ZMod 4857175351079) ^ (223 + 223) :=
            congrArg (fun n : ℕ => (7 : ZMod 4857175351079) ^ n) (by norm_num)
          _ = (7 : ZMod 4857175351079) ^ 223 * (7 : ZMod 4857175351079) ^ 223 := by rw [pow_add]
          _ = 214401279339 := by rw [factor_2_7]; decide
      change (7 : ZMod 4857175351079) ^ 446 ≠ 1
      rw [factor_2_8]
      decide

#print axioms prime_lucas_4857175351079

end TotientTailPeriodKiller
end Erdos249257
