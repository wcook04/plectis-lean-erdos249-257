import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime39547583

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2943763888189 : Nat.Prime 2943763888189 := by
  apply lucas_primality 2943763888189 (2 : ZMod 2943763888189)
  ·
      have fermat_0 : (2 : ZMod 2943763888189) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 2943763888189) ^ 2 = 4 := by
        calc
          (2 : ZMod 2943763888189) ^ 2 = (2 : ZMod 2943763888189) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1 * (2 : ZMod 2943763888189) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 2943763888189) ^ 5 = 32 := by
        calc
          (2 : ZMod 2943763888189) ^ 5 = (2 : ZMod 2943763888189) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 2 * (2 : ZMod 2943763888189) ^ 2) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 2943763888189) ^ 10 = 1024 := by
        calc
          (2 : ZMod 2943763888189) ^ 10 = (2 : ZMod 2943763888189) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5 * (2 : ZMod 2943763888189) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 2943763888189) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 2943763888189) ^ 21 = (2 : ZMod 2943763888189) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 10 * (2 : ZMod 2943763888189) ^ 10) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 2943763888189) ^ 42 = 1454282622915 := by
        calc
          (2 : ZMod 2943763888189) ^ 42 = (2 : ZMod 2943763888189) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 21 * (2 : ZMod 2943763888189) ^ 21 := by rw [pow_add]
          _ = 1454282622915 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 2943763888189) ^ 85 = 2632044014832 := by
        calc
          (2 : ZMod 2943763888189) ^ 85 = (2 : ZMod 2943763888189) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 42 * (2 : ZMod 2943763888189) ^ 42) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2632044014832 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 2943763888189) ^ 171 = 1390088932755 := by
        calc
          (2 : ZMod 2943763888189) ^ 171 = (2 : ZMod 2943763888189) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 85 * (2 : ZMod 2943763888189) ^ 85) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1390088932755 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 2943763888189) ^ 342 = 1089017279136 := by
        calc
          (2 : ZMod 2943763888189) ^ 342 = (2 : ZMod 2943763888189) ^ (171 + 171) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 171 * (2 : ZMod 2943763888189) ^ 171 := by rw [pow_add]
          _ = 1089017279136 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 2943763888189) ^ 685 = 1177058807289 := by
        calc
          (2 : ZMod 2943763888189) ^ 685 = (2 : ZMod 2943763888189) ^ (342 + 342 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 342 * (2 : ZMod 2943763888189) ^ 342) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1177058807289 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 2943763888189) ^ 1370 = 2341689160430 := by
        calc
          (2 : ZMod 2943763888189) ^ 1370 = (2 : ZMod 2943763888189) ^ (685 + 685) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 685 * (2 : ZMod 2943763888189) ^ 685 := by rw [pow_add]
          _ = 2341689160430 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 2943763888189) ^ 2741 = 2103692088391 := by
        calc
          (2 : ZMod 2943763888189) ^ 2741 = (2 : ZMod 2943763888189) ^ (1370 + 1370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 1370 * (2 : ZMod 2943763888189) ^ 1370) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2103692088391 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 2943763888189) ^ 5483 = 301429964391 := by
        calc
          (2 : ZMod 2943763888189) ^ 5483 = (2 : ZMod 2943763888189) ^ (2741 + 2741 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 2741 * (2 : ZMod 2943763888189) ^ 2741) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 301429964391 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 2943763888189) ^ 10966 = 1931596558634 := by
        calc
          (2 : ZMod 2943763888189) ^ 10966 = (2 : ZMod 2943763888189) ^ (5483 + 5483) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5483 * (2 : ZMod 2943763888189) ^ 5483 := by rw [pow_add]
          _ = 1931596558634 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 2943763888189) ^ 21932 = 2890199262750 := by
        calc
          (2 : ZMod 2943763888189) ^ 21932 = (2 : ZMod 2943763888189) ^ (10966 + 10966) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 10966 * (2 : ZMod 2943763888189) ^ 10966 := by rw [pow_add]
          _ = 2890199262750 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 2943763888189) ^ 43865 = 458136605439 := by
        calc
          (2 : ZMod 2943763888189) ^ 43865 = (2 : ZMod 2943763888189) ^ (21932 + 21932 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 21932 * (2 : ZMod 2943763888189) ^ 21932) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 458136605439 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 2943763888189) ^ 87731 = 518408890469 := by
        calc
          (2 : ZMod 2943763888189) ^ 87731 = (2 : ZMod 2943763888189) ^ (43865 + 43865 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 43865 * (2 : ZMod 2943763888189) ^ 43865) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 518408890469 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 2943763888189) ^ 175462 = 1835594293556 := by
        calc
          (2 : ZMod 2943763888189) ^ 175462 = (2 : ZMod 2943763888189) ^ (87731 + 87731) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 87731 * (2 : ZMod 2943763888189) ^ 87731 := by rw [pow_add]
          _ = 1835594293556 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 2943763888189) ^ 350924 = 2395198227715 := by
        calc
          (2 : ZMod 2943763888189) ^ 350924 = (2 : ZMod 2943763888189) ^ (175462 + 175462) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 175462 * (2 : ZMod 2943763888189) ^ 175462 := by rw [pow_add]
          _ = 2395198227715 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 2943763888189) ^ 701848 = 551086355207 := by
        calc
          (2 : ZMod 2943763888189) ^ 701848 = (2 : ZMod 2943763888189) ^ (350924 + 350924) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 350924 * (2 : ZMod 2943763888189) ^ 350924 := by rw [pow_add]
          _ = 551086355207 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 2943763888189) ^ 1403696 = 889666105587 := by
        calc
          (2 : ZMod 2943763888189) ^ 1403696 = (2 : ZMod 2943763888189) ^ (701848 + 701848) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 701848 * (2 : ZMod 2943763888189) ^ 701848 := by rw [pow_add]
          _ = 889666105587 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 2943763888189) ^ 2807392 = 183347021749 := by
        calc
          (2 : ZMod 2943763888189) ^ 2807392 = (2 : ZMod 2943763888189) ^ (1403696 + 1403696) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1403696 * (2 : ZMod 2943763888189) ^ 1403696 := by rw [pow_add]
          _ = 183347021749 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 2943763888189) ^ 5614784 = 1853269849590 := by
        calc
          (2 : ZMod 2943763888189) ^ 5614784 = (2 : ZMod 2943763888189) ^ (2807392 + 2807392) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 2807392 * (2 : ZMod 2943763888189) ^ 2807392 := by rw [pow_add]
          _ = 1853269849590 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 2943763888189) ^ 11229568 = 861421550023 := by
        calc
          (2 : ZMod 2943763888189) ^ 11229568 = (2 : ZMod 2943763888189) ^ (5614784 + 5614784) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5614784 * (2 : ZMod 2943763888189) ^ 5614784 := by rw [pow_add]
          _ = 861421550023 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 2943763888189) ^ 22459136 = 2436402700822 := by
        calc
          (2 : ZMod 2943763888189) ^ 22459136 = (2 : ZMod 2943763888189) ^ (11229568 + 11229568) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 11229568 * (2 : ZMod 2943763888189) ^ 11229568 := by rw [pow_add]
          _ = 2436402700822 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 2943763888189) ^ 44918272 = 365347028107 := by
        calc
          (2 : ZMod 2943763888189) ^ 44918272 = (2 : ZMod 2943763888189) ^ (22459136 + 22459136) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 22459136 * (2 : ZMod 2943763888189) ^ 22459136 := by rw [pow_add]
          _ = 365347028107 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 2943763888189) ^ 89836544 = 2040472799096 := by
        calc
          (2 : ZMod 2943763888189) ^ 89836544 = (2 : ZMod 2943763888189) ^ (44918272 + 44918272) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 44918272 * (2 : ZMod 2943763888189) ^ 44918272 := by rw [pow_add]
          _ = 2040472799096 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 2943763888189) ^ 179673088 = 1891006066749 := by
        calc
          (2 : ZMod 2943763888189) ^ 179673088 = (2 : ZMod 2943763888189) ^ (89836544 + 89836544) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 89836544 * (2 : ZMod 2943763888189) ^ 89836544 := by rw [pow_add]
          _ = 1891006066749 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 2943763888189) ^ 359346177 = 2800692764674 := by
        calc
          (2 : ZMod 2943763888189) ^ 359346177 = (2 : ZMod 2943763888189) ^ (179673088 + 179673088 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 179673088 * (2 : ZMod 2943763888189) ^ 179673088) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2800692764674 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 2943763888189) ^ 718692355 = 1762127173726 := by
        calc
          (2 : ZMod 2943763888189) ^ 718692355 = (2 : ZMod 2943763888189) ^ (359346177 + 359346177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 359346177 * (2 : ZMod 2943763888189) ^ 359346177) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1762127173726 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 2943763888189) ^ 1437384711 = 2290440181291 := by
        calc
          (2 : ZMod 2943763888189) ^ 1437384711 = (2 : ZMod 2943763888189) ^ (718692355 + 718692355 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 718692355 * (2 : ZMod 2943763888189) ^ 718692355) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2290440181291 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 2943763888189) ^ 2874769422 = 2400050205737 := by
        calc
          (2 : ZMod 2943763888189) ^ 2874769422 = (2 : ZMod 2943763888189) ^ (1437384711 + 1437384711) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1437384711 * (2 : ZMod 2943763888189) ^ 1437384711 := by rw [pow_add]
          _ = 2400050205737 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 2943763888189) ^ 5749538844 = 1241231829751 := by
        calc
          (2 : ZMod 2943763888189) ^ 5749538844 = (2 : ZMod 2943763888189) ^ (2874769422 + 2874769422) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 2874769422 * (2 : ZMod 2943763888189) ^ 2874769422 := by rw [pow_add]
          _ = 1241231829751 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 2943763888189) ^ 11499077688 = 1115841237410 := by
        calc
          (2 : ZMod 2943763888189) ^ 11499077688 = (2 : ZMod 2943763888189) ^ (5749538844 + 5749538844) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5749538844 * (2 : ZMod 2943763888189) ^ 5749538844 := by rw [pow_add]
          _ = 1115841237410 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 2943763888189) ^ 22998155376 = 2009846874775 := by
        calc
          (2 : ZMod 2943763888189) ^ 22998155376 = (2 : ZMod 2943763888189) ^ (11499077688 + 11499077688) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 11499077688 * (2 : ZMod 2943763888189) ^ 11499077688 := by rw [pow_add]
          _ = 2009846874775 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 2943763888189) ^ 45996310752 = 2193775769606 := by
        calc
          (2 : ZMod 2943763888189) ^ 45996310752 = (2 : ZMod 2943763888189) ^ (22998155376 + 22998155376) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 22998155376 * (2 : ZMod 2943763888189) ^ 22998155376 := by rw [pow_add]
          _ = 2193775769606 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 2943763888189) ^ 91992621505 = 860919774822 := by
        calc
          (2 : ZMod 2943763888189) ^ 91992621505 = (2 : ZMod 2943763888189) ^ (45996310752 + 45996310752 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 45996310752 * (2 : ZMod 2943763888189) ^ 45996310752) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 860919774822 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 2943763888189) ^ 183985243011 = 475697274000 := by
        calc
          (2 : ZMod 2943763888189) ^ 183985243011 = (2 : ZMod 2943763888189) ^ (91992621505 + 91992621505 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 91992621505 * (2 : ZMod 2943763888189) ^ 91992621505) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 475697274000 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 2943763888189) ^ 367970486023 = 2860003652267 := by
        calc
          (2 : ZMod 2943763888189) ^ 367970486023 = (2 : ZMod 2943763888189) ^ (183985243011 + 183985243011 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 183985243011 * (2 : ZMod 2943763888189) ^ 183985243011) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2860003652267 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 2943763888189) ^ 735940972047 = 2776243416344 := by
        calc
          (2 : ZMod 2943763888189) ^ 735940972047 = (2 : ZMod 2943763888189) ^ (367970486023 + 367970486023 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 367970486023 * (2 : ZMod 2943763888189) ^ 367970486023) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2776243416344 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 2943763888189) ^ 1471881944094 = 2943763888188 := by
        calc
          (2 : ZMod 2943763888189) ^ 1471881944094 = (2 : ZMod 2943763888189) ^ (735940972047 + 735940972047) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 735940972047 * (2 : ZMod 2943763888189) ^ 735940972047 := by rw [pow_add]
          _ = 2943763888188 := by rw [fermat_39]; decide
      have fermat_41 : (2 : ZMod 2943763888189) ^ 2943763888188 = 1 := by
        calc
          (2 : ZMod 2943763888189) ^ 2943763888188 = (2 : ZMod 2943763888189) ^ (1471881944094 + 1471881944094) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1471881944094 * (2 : ZMod 2943763888189) ^ 1471881944094 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (6203, 1), (39547583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (6203, 1), (39547583, 1)] : List FactorBlock).map factorBlockValue).prod = 2943763888189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_39547583) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 2943763888189) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 2943763888189) ^ 2 = 4 := by
        calc
          (2 : ZMod 2943763888189) ^ 2 = (2 : ZMod 2943763888189) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1 * (2 : ZMod 2943763888189) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 2943763888189) ^ 5 = 32 := by
        calc
          (2 : ZMod 2943763888189) ^ 5 = (2 : ZMod 2943763888189) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 2 * (2 : ZMod 2943763888189) ^ 2) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 2943763888189) ^ 10 = 1024 := by
        calc
          (2 : ZMod 2943763888189) ^ 10 = (2 : ZMod 2943763888189) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5 * (2 : ZMod 2943763888189) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 2943763888189) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 2943763888189) ^ 21 = (2 : ZMod 2943763888189) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 10 * (2 : ZMod 2943763888189) ^ 10) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 2943763888189) ^ 42 = 1454282622915 := by
        calc
          (2 : ZMod 2943763888189) ^ 42 = (2 : ZMod 2943763888189) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 21 * (2 : ZMod 2943763888189) ^ 21 := by rw [pow_add]
          _ = 1454282622915 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 2943763888189) ^ 85 = 2632044014832 := by
        calc
          (2 : ZMod 2943763888189) ^ 85 = (2 : ZMod 2943763888189) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 42 * (2 : ZMod 2943763888189) ^ 42) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2632044014832 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 2943763888189) ^ 171 = 1390088932755 := by
        calc
          (2 : ZMod 2943763888189) ^ 171 = (2 : ZMod 2943763888189) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 85 * (2 : ZMod 2943763888189) ^ 85) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1390088932755 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 2943763888189) ^ 342 = 1089017279136 := by
        calc
          (2 : ZMod 2943763888189) ^ 342 = (2 : ZMod 2943763888189) ^ (171 + 171) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 171 * (2 : ZMod 2943763888189) ^ 171 := by rw [pow_add]
          _ = 1089017279136 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 2943763888189) ^ 685 = 1177058807289 := by
        calc
          (2 : ZMod 2943763888189) ^ 685 = (2 : ZMod 2943763888189) ^ (342 + 342 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 342 * (2 : ZMod 2943763888189) ^ 342) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1177058807289 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 2943763888189) ^ 1370 = 2341689160430 := by
        calc
          (2 : ZMod 2943763888189) ^ 1370 = (2 : ZMod 2943763888189) ^ (685 + 685) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 685 * (2 : ZMod 2943763888189) ^ 685 := by rw [pow_add]
          _ = 2341689160430 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 2943763888189) ^ 2741 = 2103692088391 := by
        calc
          (2 : ZMod 2943763888189) ^ 2741 = (2 : ZMod 2943763888189) ^ (1370 + 1370 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 1370 * (2 : ZMod 2943763888189) ^ 1370) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2103692088391 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 2943763888189) ^ 5483 = 301429964391 := by
        calc
          (2 : ZMod 2943763888189) ^ 5483 = (2 : ZMod 2943763888189) ^ (2741 + 2741 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 2741 * (2 : ZMod 2943763888189) ^ 2741) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 301429964391 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 2943763888189) ^ 10966 = 1931596558634 := by
        calc
          (2 : ZMod 2943763888189) ^ 10966 = (2 : ZMod 2943763888189) ^ (5483 + 5483) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5483 * (2 : ZMod 2943763888189) ^ 5483 := by rw [pow_add]
          _ = 1931596558634 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 2943763888189) ^ 21932 = 2890199262750 := by
        calc
          (2 : ZMod 2943763888189) ^ 21932 = (2 : ZMod 2943763888189) ^ (10966 + 10966) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 10966 * (2 : ZMod 2943763888189) ^ 10966 := by rw [pow_add]
          _ = 2890199262750 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 2943763888189) ^ 43865 = 458136605439 := by
        calc
          (2 : ZMod 2943763888189) ^ 43865 = (2 : ZMod 2943763888189) ^ (21932 + 21932 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 21932 * (2 : ZMod 2943763888189) ^ 21932) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 458136605439 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 2943763888189) ^ 87731 = 518408890469 := by
        calc
          (2 : ZMod 2943763888189) ^ 87731 = (2 : ZMod 2943763888189) ^ (43865 + 43865 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 43865 * (2 : ZMod 2943763888189) ^ 43865) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 518408890469 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 2943763888189) ^ 175462 = 1835594293556 := by
        calc
          (2 : ZMod 2943763888189) ^ 175462 = (2 : ZMod 2943763888189) ^ (87731 + 87731) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 87731 * (2 : ZMod 2943763888189) ^ 87731 := by rw [pow_add]
          _ = 1835594293556 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 2943763888189) ^ 350924 = 2395198227715 := by
        calc
          (2 : ZMod 2943763888189) ^ 350924 = (2 : ZMod 2943763888189) ^ (175462 + 175462) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 175462 * (2 : ZMod 2943763888189) ^ 175462 := by rw [pow_add]
          _ = 2395198227715 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 2943763888189) ^ 701848 = 551086355207 := by
        calc
          (2 : ZMod 2943763888189) ^ 701848 = (2 : ZMod 2943763888189) ^ (350924 + 350924) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 350924 * (2 : ZMod 2943763888189) ^ 350924 := by rw [pow_add]
          _ = 551086355207 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 2943763888189) ^ 1403696 = 889666105587 := by
        calc
          (2 : ZMod 2943763888189) ^ 1403696 = (2 : ZMod 2943763888189) ^ (701848 + 701848) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 701848 * (2 : ZMod 2943763888189) ^ 701848 := by rw [pow_add]
          _ = 889666105587 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 2943763888189) ^ 2807392 = 183347021749 := by
        calc
          (2 : ZMod 2943763888189) ^ 2807392 = (2 : ZMod 2943763888189) ^ (1403696 + 1403696) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1403696 * (2 : ZMod 2943763888189) ^ 1403696 := by rw [pow_add]
          _ = 183347021749 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 2943763888189) ^ 5614784 = 1853269849590 := by
        calc
          (2 : ZMod 2943763888189) ^ 5614784 = (2 : ZMod 2943763888189) ^ (2807392 + 2807392) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 2807392 * (2 : ZMod 2943763888189) ^ 2807392 := by rw [pow_add]
          _ = 1853269849590 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 2943763888189) ^ 11229568 = 861421550023 := by
        calc
          (2 : ZMod 2943763888189) ^ 11229568 = (2 : ZMod 2943763888189) ^ (5614784 + 5614784) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5614784 * (2 : ZMod 2943763888189) ^ 5614784 := by rw [pow_add]
          _ = 861421550023 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 2943763888189) ^ 22459136 = 2436402700822 := by
        calc
          (2 : ZMod 2943763888189) ^ 22459136 = (2 : ZMod 2943763888189) ^ (11229568 + 11229568) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 11229568 * (2 : ZMod 2943763888189) ^ 11229568 := by rw [pow_add]
          _ = 2436402700822 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 2943763888189) ^ 44918272 = 365347028107 := by
        calc
          (2 : ZMod 2943763888189) ^ 44918272 = (2 : ZMod 2943763888189) ^ (22459136 + 22459136) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 22459136 * (2 : ZMod 2943763888189) ^ 22459136 := by rw [pow_add]
          _ = 365347028107 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 2943763888189) ^ 89836544 = 2040472799096 := by
        calc
          (2 : ZMod 2943763888189) ^ 89836544 = (2 : ZMod 2943763888189) ^ (44918272 + 44918272) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 44918272 * (2 : ZMod 2943763888189) ^ 44918272 := by rw [pow_add]
          _ = 2040472799096 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 2943763888189) ^ 179673088 = 1891006066749 := by
        calc
          (2 : ZMod 2943763888189) ^ 179673088 = (2 : ZMod 2943763888189) ^ (89836544 + 89836544) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 89836544 * (2 : ZMod 2943763888189) ^ 89836544 := by rw [pow_add]
          _ = 1891006066749 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 2943763888189) ^ 359346177 = 2800692764674 := by
        calc
          (2 : ZMod 2943763888189) ^ 359346177 = (2 : ZMod 2943763888189) ^ (179673088 + 179673088 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 179673088 * (2 : ZMod 2943763888189) ^ 179673088) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2800692764674 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 2943763888189) ^ 718692355 = 1762127173726 := by
        calc
          (2 : ZMod 2943763888189) ^ 718692355 = (2 : ZMod 2943763888189) ^ (359346177 + 359346177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 359346177 * (2 : ZMod 2943763888189) ^ 359346177) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1762127173726 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 2943763888189) ^ 1437384711 = 2290440181291 := by
        calc
          (2 : ZMod 2943763888189) ^ 1437384711 = (2 : ZMod 2943763888189) ^ (718692355 + 718692355 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 718692355 * (2 : ZMod 2943763888189) ^ 718692355) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2290440181291 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 2943763888189) ^ 2874769422 = 2400050205737 := by
        calc
          (2 : ZMod 2943763888189) ^ 2874769422 = (2 : ZMod 2943763888189) ^ (1437384711 + 1437384711) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1437384711 * (2 : ZMod 2943763888189) ^ 1437384711 := by rw [pow_add]
          _ = 2400050205737 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 2943763888189) ^ 5749538844 = 1241231829751 := by
        calc
          (2 : ZMod 2943763888189) ^ 5749538844 = (2 : ZMod 2943763888189) ^ (2874769422 + 2874769422) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 2874769422 * (2 : ZMod 2943763888189) ^ 2874769422 := by rw [pow_add]
          _ = 1241231829751 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 2943763888189) ^ 11499077688 = 1115841237410 := by
        calc
          (2 : ZMod 2943763888189) ^ 11499077688 = (2 : ZMod 2943763888189) ^ (5749538844 + 5749538844) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 5749538844 * (2 : ZMod 2943763888189) ^ 5749538844 := by rw [pow_add]
          _ = 1115841237410 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 2943763888189) ^ 22998155376 = 2009846874775 := by
        calc
          (2 : ZMod 2943763888189) ^ 22998155376 = (2 : ZMod 2943763888189) ^ (11499077688 + 11499077688) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 11499077688 * (2 : ZMod 2943763888189) ^ 11499077688 := by rw [pow_add]
          _ = 2009846874775 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 2943763888189) ^ 45996310752 = 2193775769606 := by
        calc
          (2 : ZMod 2943763888189) ^ 45996310752 = (2 : ZMod 2943763888189) ^ (22998155376 + 22998155376) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 22998155376 * (2 : ZMod 2943763888189) ^ 22998155376 := by rw [pow_add]
          _ = 2193775769606 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 2943763888189) ^ 91992621505 = 860919774822 := by
        calc
          (2 : ZMod 2943763888189) ^ 91992621505 = (2 : ZMod 2943763888189) ^ (45996310752 + 45996310752 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 45996310752 * (2 : ZMod 2943763888189) ^ 45996310752) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 860919774822 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 2943763888189) ^ 183985243011 = 475697274000 := by
        calc
          (2 : ZMod 2943763888189) ^ 183985243011 = (2 : ZMod 2943763888189) ^ (91992621505 + 91992621505 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 91992621505 * (2 : ZMod 2943763888189) ^ 91992621505) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 475697274000 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 2943763888189) ^ 367970486023 = 2860003652267 := by
        calc
          (2 : ZMod 2943763888189) ^ 367970486023 = (2 : ZMod 2943763888189) ^ (183985243011 + 183985243011 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 183985243011 * (2 : ZMod 2943763888189) ^ 183985243011) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2860003652267 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 2943763888189) ^ 735940972047 = 2776243416344 := by
        calc
          (2 : ZMod 2943763888189) ^ 735940972047 = (2 : ZMod 2943763888189) ^ (367970486023 + 367970486023 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 367970486023 * (2 : ZMod 2943763888189) ^ 367970486023) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2776243416344 := by rw [factor_0_38]; decide
      have factor_0_40 : (2 : ZMod 2943763888189) ^ 1471881944094 = 2943763888188 := by
        calc
          (2 : ZMod 2943763888189) ^ 1471881944094 = (2 : ZMod 2943763888189) ^ (735940972047 + 735940972047) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 735940972047 * (2 : ZMod 2943763888189) ^ 735940972047 := by rw [pow_add]
          _ = 2943763888188 := by rw [factor_0_39]; decide
      change (2 : ZMod 2943763888189) ^ 1471881944094 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (2 : ZMod 2943763888189) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 2943763888189) ^ 3 = 8 := by
        calc
          (2 : ZMod 2943763888189) ^ 3 = (2 : ZMod 2943763888189) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 1 * (2 : ZMod 2943763888189) ^ 1) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 2943763888189) ^ 7 = 128 := by
        calc
          (2 : ZMod 2943763888189) ^ 7 = (2 : ZMod 2943763888189) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 3 * (2 : ZMod 2943763888189) ^ 3) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 2943763888189) ^ 14 = 16384 := by
        calc
          (2 : ZMod 2943763888189) ^ 14 = (2 : ZMod 2943763888189) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 7 * (2 : ZMod 2943763888189) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 2943763888189) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 2943763888189) ^ 28 = (2 : ZMod 2943763888189) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 14 * (2 : ZMod 2943763888189) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 2943763888189) ^ 57 = 283165675188 := by
        calc
          (2 : ZMod 2943763888189) ^ 57 = (2 : ZMod 2943763888189) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 28 * (2 : ZMod 2943763888189) ^ 28) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 283165675188 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 2943763888189) ^ 114 = 541278029285 := by
        calc
          (2 : ZMod 2943763888189) ^ 114 = (2 : ZMod 2943763888189) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 57 * (2 : ZMod 2943763888189) ^ 57 := by rw [pow_add]
          _ = 541278029285 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 2943763888189) ^ 228 = 521385916133 := by
        calc
          (2 : ZMod 2943763888189) ^ 228 = (2 : ZMod 2943763888189) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 114 * (2 : ZMod 2943763888189) ^ 114 := by rw [pow_add]
          _ = 521385916133 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 2943763888189) ^ 456 = 67336882949 := by
        calc
          (2 : ZMod 2943763888189) ^ 456 = (2 : ZMod 2943763888189) ^ (228 + 228) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 228 * (2 : ZMod 2943763888189) ^ 228 := by rw [pow_add]
          _ = 67336882949 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 2943763888189) ^ 913 = 655859197992 := by
        calc
          (2 : ZMod 2943763888189) ^ 913 = (2 : ZMod 2943763888189) ^ (456 + 456 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 456 * (2 : ZMod 2943763888189) ^ 456) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 655859197992 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 2943763888189) ^ 1827 = 2203307721281 := by
        calc
          (2 : ZMod 2943763888189) ^ 1827 = (2 : ZMod 2943763888189) ^ (913 + 913 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 913 * (2 : ZMod 2943763888189) ^ 913) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2203307721281 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 2943763888189) ^ 3655 = 2725192017656 := by
        calc
          (2 : ZMod 2943763888189) ^ 3655 = (2 : ZMod 2943763888189) ^ (1827 + 1827 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 1827 * (2 : ZMod 2943763888189) ^ 1827) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2725192017656 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 2943763888189) ^ 7310 = 1809445662314 := by
        calc
          (2 : ZMod 2943763888189) ^ 7310 = (2 : ZMod 2943763888189) ^ (3655 + 3655) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 3655 * (2 : ZMod 2943763888189) ^ 3655 := by rw [pow_add]
          _ = 1809445662314 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 2943763888189) ^ 14621 = 2675114726495 := by
        calc
          (2 : ZMod 2943763888189) ^ 14621 = (2 : ZMod 2943763888189) ^ (7310 + 7310 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 7310 * (2 : ZMod 2943763888189) ^ 7310) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2675114726495 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 2943763888189) ^ 29243 = 1266347106910 := by
        calc
          (2 : ZMod 2943763888189) ^ 29243 = (2 : ZMod 2943763888189) ^ (14621 + 14621 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 14621 * (2 : ZMod 2943763888189) ^ 14621) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1266347106910 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 2943763888189) ^ 58487 = 731864764045 := by
        calc
          (2 : ZMod 2943763888189) ^ 58487 = (2 : ZMod 2943763888189) ^ (29243 + 29243 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 29243 * (2 : ZMod 2943763888189) ^ 29243) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 731864764045 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 2943763888189) ^ 116974 = 1906158877380 := by
        calc
          (2 : ZMod 2943763888189) ^ 116974 = (2 : ZMod 2943763888189) ^ (58487 + 58487) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 58487 * (2 : ZMod 2943763888189) ^ 58487 := by rw [pow_add]
          _ = 1906158877380 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 2943763888189) ^ 233949 = 2001888174187 := by
        calc
          (2 : ZMod 2943763888189) ^ 233949 = (2 : ZMod 2943763888189) ^ (116974 + 116974 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 116974 * (2 : ZMod 2943763888189) ^ 116974) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2001888174187 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 2943763888189) ^ 467898 = 216809492844 := by
        calc
          (2 : ZMod 2943763888189) ^ 467898 = (2 : ZMod 2943763888189) ^ (233949 + 233949) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 233949 * (2 : ZMod 2943763888189) ^ 233949 := by rw [pow_add]
          _ = 216809492844 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 2943763888189) ^ 935797 = 523090546738 := by
        calc
          (2 : ZMod 2943763888189) ^ 935797 = (2 : ZMod 2943763888189) ^ (467898 + 467898 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 467898 * (2 : ZMod 2943763888189) ^ 467898) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 523090546738 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 2943763888189) ^ 1871594 = 78362940776 := by
        calc
          (2 : ZMod 2943763888189) ^ 1871594 = (2 : ZMod 2943763888189) ^ (935797 + 935797) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 935797 * (2 : ZMod 2943763888189) ^ 935797 := by rw [pow_add]
          _ = 78362940776 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 2943763888189) ^ 3743189 = 2388162026397 := by
        calc
          (2 : ZMod 2943763888189) ^ 3743189 = (2 : ZMod 2943763888189) ^ (1871594 + 1871594 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 1871594 * (2 : ZMod 2943763888189) ^ 1871594) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2388162026397 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 2943763888189) ^ 7486378 = 1601547936735 := by
        calc
          (2 : ZMod 2943763888189) ^ 7486378 = (2 : ZMod 2943763888189) ^ (3743189 + 3743189) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 3743189 * (2 : ZMod 2943763888189) ^ 3743189 := by rw [pow_add]
          _ = 1601547936735 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 2943763888189) ^ 14972757 = 381747850284 := by
        calc
          (2 : ZMod 2943763888189) ^ 14972757 = (2 : ZMod 2943763888189) ^ (7486378 + 7486378 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 7486378 * (2 : ZMod 2943763888189) ^ 7486378) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 381747850284 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 2943763888189) ^ 29945514 = 1300551583039 := by
        calc
          (2 : ZMod 2943763888189) ^ 29945514 = (2 : ZMod 2943763888189) ^ (14972757 + 14972757) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 14972757 * (2 : ZMod 2943763888189) ^ 14972757 := by rw [pow_add]
          _ = 1300551583039 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 2943763888189) ^ 59891029 = 1097637332291 := by
        calc
          (2 : ZMod 2943763888189) ^ 59891029 = (2 : ZMod 2943763888189) ^ (29945514 + 29945514 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 29945514 * (2 : ZMod 2943763888189) ^ 29945514) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1097637332291 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 2943763888189) ^ 119782059 = 1764757235882 := by
        calc
          (2 : ZMod 2943763888189) ^ 119782059 = (2 : ZMod 2943763888189) ^ (59891029 + 59891029 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 59891029 * (2 : ZMod 2943763888189) ^ 59891029) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1764757235882 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 2943763888189) ^ 239564118 = 1064274175040 := by
        calc
          (2 : ZMod 2943763888189) ^ 239564118 = (2 : ZMod 2943763888189) ^ (119782059 + 119782059) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 119782059 * (2 : ZMod 2943763888189) ^ 119782059 := by rw [pow_add]
          _ = 1064274175040 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 2943763888189) ^ 479128237 = 992771560185 := by
        calc
          (2 : ZMod 2943763888189) ^ 479128237 = (2 : ZMod 2943763888189) ^ (239564118 + 239564118 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 239564118 * (2 : ZMod 2943763888189) ^ 239564118) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 992771560185 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 2943763888189) ^ 958256474 = 1166814751827 := by
        calc
          (2 : ZMod 2943763888189) ^ 958256474 = (2 : ZMod 2943763888189) ^ (479128237 + 479128237) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 479128237 * (2 : ZMod 2943763888189) ^ 479128237 := by rw [pow_add]
          _ = 1166814751827 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 2943763888189) ^ 1916512948 = 913401229939 := by
        calc
          (2 : ZMod 2943763888189) ^ 1916512948 = (2 : ZMod 2943763888189) ^ (958256474 + 958256474) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 958256474 * (2 : ZMod 2943763888189) ^ 958256474 := by rw [pow_add]
          _ = 913401229939 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 2943763888189) ^ 3833025896 = 130498289640 := by
        calc
          (2 : ZMod 2943763888189) ^ 3833025896 = (2 : ZMod 2943763888189) ^ (1916512948 + 1916512948) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1916512948 * (2 : ZMod 2943763888189) ^ 1916512948 := by rw [pow_add]
          _ = 130498289640 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 2943763888189) ^ 7666051792 = 787233230923 := by
        calc
          (2 : ZMod 2943763888189) ^ 7666051792 = (2 : ZMod 2943763888189) ^ (3833025896 + 3833025896) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 3833025896 * (2 : ZMod 2943763888189) ^ 3833025896 := by rw [pow_add]
          _ = 787233230923 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 2943763888189) ^ 15332103584 = 2940115317973 := by
        calc
          (2 : ZMod 2943763888189) ^ 15332103584 = (2 : ZMod 2943763888189) ^ (7666051792 + 7666051792) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 7666051792 * (2 : ZMod 2943763888189) ^ 7666051792 := by rw [pow_add]
          _ = 2940115317973 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 2943763888189) ^ 30664207168 = 2235733381409 := by
        calc
          (2 : ZMod 2943763888189) ^ 30664207168 = (2 : ZMod 2943763888189) ^ (15332103584 + 15332103584) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 15332103584 * (2 : ZMod 2943763888189) ^ 15332103584 := by rw [pow_add]
          _ = 2235733381409 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 2943763888189) ^ 61328414337 = 2237162365041 := by
        calc
          (2 : ZMod 2943763888189) ^ 61328414337 = (2 : ZMod 2943763888189) ^ (30664207168 + 30664207168 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 30664207168 * (2 : ZMod 2943763888189) ^ 30664207168) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2237162365041 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 2943763888189) ^ 122656828674 = 1486871935390 := by
        calc
          (2 : ZMod 2943763888189) ^ 122656828674 = (2 : ZMod 2943763888189) ^ (61328414337 + 61328414337) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 61328414337 * (2 : ZMod 2943763888189) ^ 61328414337 := by rw [pow_add]
          _ = 1486871935390 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 2943763888189) ^ 245313657349 = 850934632036 := by
        calc
          (2 : ZMod 2943763888189) ^ 245313657349 = (2 : ZMod 2943763888189) ^ (122656828674 + 122656828674 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 122656828674 * (2 : ZMod 2943763888189) ^ 122656828674) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 850934632036 := by rw [factor_1_36]; decide
      have factor_1_38 : (2 : ZMod 2943763888189) ^ 490627314698 = 1955288766899 := by
        calc
          (2 : ZMod 2943763888189) ^ 490627314698 = (2 : ZMod 2943763888189) ^ (245313657349 + 245313657349) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 245313657349 * (2 : ZMod 2943763888189) ^ 245313657349 := by rw [pow_add]
          _ = 1955288766899 := by rw [factor_1_37]; decide
      have factor_1_39 : (2 : ZMod 2943763888189) ^ 981254629396 = 1955288766898 := by
        calc
          (2 : ZMod 2943763888189) ^ 981254629396 = (2 : ZMod 2943763888189) ^ (490627314698 + 490627314698) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 490627314698 * (2 : ZMod 2943763888189) ^ 490627314698 := by rw [pow_add]
          _ = 1955288766898 := by rw [factor_1_38]; decide
      change (2 : ZMod 2943763888189) ^ 981254629396 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (2 : ZMod 2943763888189) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 2943763888189) ^ 3 = 8 := by
        calc
          (2 : ZMod 2943763888189) ^ 3 = (2 : ZMod 2943763888189) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 1 * (2 : ZMod 2943763888189) ^ 1) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 2943763888189) ^ 7 = 128 := by
        calc
          (2 : ZMod 2943763888189) ^ 7 = (2 : ZMod 2943763888189) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 3 * (2 : ZMod 2943763888189) ^ 3) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 2943763888189) ^ 14 = 16384 := by
        calc
          (2 : ZMod 2943763888189) ^ 14 = (2 : ZMod 2943763888189) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 7 * (2 : ZMod 2943763888189) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 2943763888189) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 2943763888189) ^ 28 = (2 : ZMod 2943763888189) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 14 * (2 : ZMod 2943763888189) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 2943763888189) ^ 56 = 141582837594 := by
        calc
          (2 : ZMod 2943763888189) ^ 56 = (2 : ZMod 2943763888189) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 28 * (2 : ZMod 2943763888189) ^ 28 := by rw [pow_add]
          _ = 141582837594 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 2943763888189) ^ 113 = 1742520958737 := by
        calc
          (2 : ZMod 2943763888189) ^ 113 = (2 : ZMod 2943763888189) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 56 * (2 : ZMod 2943763888189) ^ 56) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1742520958737 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 2943763888189) ^ 226 = 2338169395175 := by
        calc
          (2 : ZMod 2943763888189) ^ 226 = (2 : ZMod 2943763888189) ^ (113 + 113) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 113 * (2 : ZMod 2943763888189) ^ 113 := by rw [pow_add]
          _ = 2338169395175 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 2943763888189) ^ 452 = 1292105256267 := by
        calc
          (2 : ZMod 2943763888189) ^ 452 = (2 : ZMod 2943763888189) ^ (226 + 226) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 226 * (2 : ZMod 2943763888189) ^ 226 := by rw [pow_add]
          _ = 1292105256267 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 2943763888189) ^ 905 = 2118392244628 := by
        calc
          (2 : ZMod 2943763888189) ^ 905 = (2 : ZMod 2943763888189) ^ (452 + 452 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 452 * (2 : ZMod 2943763888189) ^ 452) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2118392244628 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 2943763888189) ^ 1810 = 1757466669635 := by
        calc
          (2 : ZMod 2943763888189) ^ 1810 = (2 : ZMod 2943763888189) ^ (905 + 905) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 905 * (2 : ZMod 2943763888189) ^ 905 := by rw [pow_add]
          _ = 1757466669635 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 2943763888189) ^ 3620 = 313365431797 := by
        calc
          (2 : ZMod 2943763888189) ^ 3620 = (2 : ZMod 2943763888189) ^ (1810 + 1810) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1810 * (2 : ZMod 2943763888189) ^ 1810 := by rw [pow_add]
          _ = 313365431797 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 2943763888189) ^ 7241 = 1933648452519 := by
        calc
          (2 : ZMod 2943763888189) ^ 7241 = (2 : ZMod 2943763888189) ^ (3620 + 3620 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 3620 * (2 : ZMod 2943763888189) ^ 3620) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1933648452519 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 2943763888189) ^ 14482 = 1862530809528 := by
        calc
          (2 : ZMod 2943763888189) ^ 14482 = (2 : ZMod 2943763888189) ^ (7241 + 7241) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 7241 * (2 : ZMod 2943763888189) ^ 7241 := by rw [pow_add]
          _ = 1862530809528 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 2943763888189) ^ 28965 = 1655571685832 := by
        calc
          (2 : ZMod 2943763888189) ^ 28965 = (2 : ZMod 2943763888189) ^ (14482 + 14482 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 14482 * (2 : ZMod 2943763888189) ^ 14482) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1655571685832 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 2943763888189) ^ 57931 = 1442715846331 := by
        calc
          (2 : ZMod 2943763888189) ^ 57931 = (2 : ZMod 2943763888189) ^ (28965 + 28965 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 28965 * (2 : ZMod 2943763888189) ^ 28965) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1442715846331 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 2943763888189) ^ 115862 = 2716859940028 := by
        calc
          (2 : ZMod 2943763888189) ^ 115862 = (2 : ZMod 2943763888189) ^ (57931 + 57931) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 57931 * (2 : ZMod 2943763888189) ^ 57931 := by rw [pow_add]
          _ = 2716859940028 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 2943763888189) ^ 231724 = 2577476257105 := by
        calc
          (2 : ZMod 2943763888189) ^ 231724 = (2 : ZMod 2943763888189) ^ (115862 + 115862) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 115862 * (2 : ZMod 2943763888189) ^ 115862 := by rw [pow_add]
          _ = 2577476257105 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 2943763888189) ^ 463448 = 2881163066417 := by
        calc
          (2 : ZMod 2943763888189) ^ 463448 = (2 : ZMod 2943763888189) ^ (231724 + 231724) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 231724 * (2 : ZMod 2943763888189) ^ 231724 := by rw [pow_add]
          _ = 2881163066417 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 2943763888189) ^ 926896 = 998125329222 := by
        calc
          (2 : ZMod 2943763888189) ^ 926896 = (2 : ZMod 2943763888189) ^ (463448 + 463448) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 463448 * (2 : ZMod 2943763888189) ^ 463448 := by rw [pow_add]
          _ = 998125329222 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 2943763888189) ^ 1853792 = 338370856884 := by
        calc
          (2 : ZMod 2943763888189) ^ 1853792 = (2 : ZMod 2943763888189) ^ (926896 + 926896) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 926896 * (2 : ZMod 2943763888189) ^ 926896 := by rw [pow_add]
          _ = 338370856884 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 2943763888189) ^ 3707585 = 385150601184 := by
        calc
          (2 : ZMod 2943763888189) ^ 3707585 = (2 : ZMod 2943763888189) ^ (1853792 + 1853792 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 1853792 * (2 : ZMod 2943763888189) ^ 1853792) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 385150601184 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 2943763888189) ^ 7415171 = 676153679090 := by
        calc
          (2 : ZMod 2943763888189) ^ 7415171 = (2 : ZMod 2943763888189) ^ (3707585 + 3707585 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 3707585 * (2 : ZMod 2943763888189) ^ 3707585) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 676153679090 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 2943763888189) ^ 14830343 = 91605391700 := by
        calc
          (2 : ZMod 2943763888189) ^ 14830343 = (2 : ZMod 2943763888189) ^ (7415171 + 7415171 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 7415171 * (2 : ZMod 2943763888189) ^ 7415171) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 91605391700 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 2943763888189) ^ 29660687 = 1963979092512 := by
        calc
          (2 : ZMod 2943763888189) ^ 29660687 = (2 : ZMod 2943763888189) ^ (14830343 + 14830343 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 14830343 * (2 : ZMod 2943763888189) ^ 14830343) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1963979092512 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 2943763888189) ^ 59321374 = 1161700435072 := by
        calc
          (2 : ZMod 2943763888189) ^ 59321374 = (2 : ZMod 2943763888189) ^ (29660687 + 29660687) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 29660687 * (2 : ZMod 2943763888189) ^ 29660687 := by rw [pow_add]
          _ = 1161700435072 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 2943763888189) ^ 118642749 = 1885476554120 := by
        calc
          (2 : ZMod 2943763888189) ^ 118642749 = (2 : ZMod 2943763888189) ^ (59321374 + 59321374 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 59321374 * (2 : ZMod 2943763888189) ^ 59321374) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1885476554120 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 2943763888189) ^ 237285498 = 386878874422 := by
        calc
          (2 : ZMod 2943763888189) ^ 237285498 = (2 : ZMod 2943763888189) ^ (118642749 + 118642749) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 118642749 * (2 : ZMod 2943763888189) ^ 118642749 := by rw [pow_add]
          _ = 386878874422 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 2943763888189) ^ 474570996 = 2448718016913 := by
        calc
          (2 : ZMod 2943763888189) ^ 474570996 = (2 : ZMod 2943763888189) ^ (237285498 + 237285498) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 237285498 * (2 : ZMod 2943763888189) ^ 237285498 := by rw [pow_add]
          _ = 2448718016913 := by rw [factor_2_27]; decide
      change (2 : ZMod 2943763888189) ^ 474570996 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (2 : ZMod 2943763888189) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 2943763888189) ^ 2 = 4 := by
        calc
          (2 : ZMod 2943763888189) ^ 2 = (2 : ZMod 2943763888189) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1 * (2 : ZMod 2943763888189) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 2943763888189) ^ 4 = 16 := by
        calc
          (2 : ZMod 2943763888189) ^ 4 = (2 : ZMod 2943763888189) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 2 * (2 : ZMod 2943763888189) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 2943763888189) ^ 9 = 512 := by
        calc
          (2 : ZMod 2943763888189) ^ 9 = (2 : ZMod 2943763888189) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 4 * (2 : ZMod 2943763888189) ^ 4) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 2943763888189) ^ 18 = 262144 := by
        calc
          (2 : ZMod 2943763888189) ^ 18 = (2 : ZMod 2943763888189) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 9 * (2 : ZMod 2943763888189) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 2943763888189) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 2943763888189) ^ 36 = (2 : ZMod 2943763888189) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 18 * (2 : ZMod 2943763888189) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 2943763888189) ^ 72 = 29068988656 := by
        calc
          (2 : ZMod 2943763888189) ^ 72 = (2 : ZMod 2943763888189) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 36 * (2 : ZMod 2943763888189) ^ 36 := by rw [pow_add]
          _ = 29068988656 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 2943763888189) ^ 145 = 1199743954583 := by
        calc
          (2 : ZMod 2943763888189) ^ 145 = (2 : ZMod 2943763888189) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 72 * (2 : ZMod 2943763888189) ^ 72) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 1199743954583 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 2943763888189) ^ 290 = 2694853722640 := by
        calc
          (2 : ZMod 2943763888189) ^ 290 = (2 : ZMod 2943763888189) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 145 * (2 : ZMod 2943763888189) ^ 145 := by rw [pow_add]
          _ = 2694853722640 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 2943763888189) ^ 581 = 814731663268 := by
        calc
          (2 : ZMod 2943763888189) ^ 581 = (2 : ZMod 2943763888189) ^ (290 + 290 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 290 * (2 : ZMod 2943763888189) ^ 290) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 814731663268 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 2943763888189) ^ 1163 = 2182677387794 := by
        calc
          (2 : ZMod 2943763888189) ^ 1163 = (2 : ZMod 2943763888189) ^ (581 + 581 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 581 * (2 : ZMod 2943763888189) ^ 581) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 2182677387794 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 2943763888189) ^ 2326 = 2492569987535 := by
        calc
          (2 : ZMod 2943763888189) ^ 2326 = (2 : ZMod 2943763888189) ^ (1163 + 1163) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 1163 * (2 : ZMod 2943763888189) ^ 1163 := by rw [pow_add]
          _ = 2492569987535 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 2943763888189) ^ 4652 = 1561618939974 := by
        calc
          (2 : ZMod 2943763888189) ^ 4652 = (2 : ZMod 2943763888189) ^ (2326 + 2326) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 2326 * (2 : ZMod 2943763888189) ^ 2326 := by rw [pow_add]
          _ = 1561618939974 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 2943763888189) ^ 9304 = 1950228209910 := by
        calc
          (2 : ZMod 2943763888189) ^ 9304 = (2 : ZMod 2943763888189) ^ (4652 + 4652) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 4652 * (2 : ZMod 2943763888189) ^ 4652 := by rw [pow_add]
          _ = 1950228209910 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 2943763888189) ^ 18609 = 29800905531 := by
        calc
          (2 : ZMod 2943763888189) ^ 18609 = (2 : ZMod 2943763888189) ^ (9304 + 9304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = ((2 : ZMod 2943763888189) ^ 9304 * (2 : ZMod 2943763888189) ^ 9304) * (2 : ZMod 2943763888189) := by rw [pow_succ, pow_add]
          _ = 29800905531 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 2943763888189) ^ 37218 = 1969025122200 := by
        calc
          (2 : ZMod 2943763888189) ^ 37218 = (2 : ZMod 2943763888189) ^ (18609 + 18609) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 18609 * (2 : ZMod 2943763888189) ^ 18609 := by rw [pow_add]
          _ = 1969025122200 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 2943763888189) ^ 74436 = 707095022372 := by
        calc
          (2 : ZMod 2943763888189) ^ 74436 = (2 : ZMod 2943763888189) ^ (37218 + 37218) :=
            congrArg (fun n : ℕ => (2 : ZMod 2943763888189) ^ n) (by norm_num)
          _ = (2 : ZMod 2943763888189) ^ 37218 * (2 : ZMod 2943763888189) ^ 37218 := by rw [pow_add]
          _ = 707095022372 := by rw [factor_3_15]; decide
      change (2 : ZMod 2943763888189) ^ 74436 ≠ 1
      rw [factor_3_16]
      decide

#print axioms prime_lucas_2943763888189

end TotientTailPeriodKiller
end Erdos249257
