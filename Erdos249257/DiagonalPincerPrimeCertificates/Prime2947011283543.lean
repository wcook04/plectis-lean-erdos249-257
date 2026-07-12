import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2947011283543 : Nat.Prime 2947011283543 := by
  apply lucas_primality 2947011283543 (3 : ZMod 2947011283543)
  ·
      have fermat_0 : (3 : ZMod 2947011283543) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 2947011283543) ^ 2 = 9 := by
        calc
          (3 : ZMod 2947011283543) ^ 2 = (3 : ZMod 2947011283543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1 * (3 : ZMod 2947011283543) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 2947011283543) ^ 5 = 243 := by
        calc
          (3 : ZMod 2947011283543) ^ 5 = (3 : ZMod 2947011283543) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2 * (3 : ZMod 2947011283543) ^ 2) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 2947011283543) ^ 10 = 59049 := by
        calc
          (3 : ZMod 2947011283543) ^ 10 = (3 : ZMod 2947011283543) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 5 * (3 : ZMod 2947011283543) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 2947011283543) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 2947011283543) ^ 21 = (3 : ZMod 2947011283543) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 10 * (3 : ZMod 2947011283543) ^ 10) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 2947011283543) ^ 42 = 2481123587895 := by
        calc
          (3 : ZMod 2947011283543) ^ 42 = (3 : ZMod 2947011283543) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 21 * (3 : ZMod 2947011283543) ^ 21 := by rw [pow_add]
          _ = 2481123587895 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 2947011283543) ^ 85 = 1641276840284 := by
        calc
          (3 : ZMod 2947011283543) ^ 85 = (3 : ZMod 2947011283543) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 42 * (3 : ZMod 2947011283543) ^ 42) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1641276840284 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 2947011283543) ^ 171 = 2183160796063 := by
        calc
          (3 : ZMod 2947011283543) ^ 171 = (3 : ZMod 2947011283543) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 85 * (3 : ZMod 2947011283543) ^ 85) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2183160796063 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 2947011283543) ^ 343 = 1986490225790 := by
        calc
          (3 : ZMod 2947011283543) ^ 343 = (3 : ZMod 2947011283543) ^ (171 + 171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 171 * (3 : ZMod 2947011283543) ^ 171) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1986490225790 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 2947011283543) ^ 686 = 1847174801253 := by
        calc
          (3 : ZMod 2947011283543) ^ 686 = (3 : ZMod 2947011283543) ^ (343 + 343) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 343 * (3 : ZMod 2947011283543) ^ 343 := by rw [pow_add]
          _ = 1847174801253 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 2947011283543) ^ 1372 = 195503453929 := by
        calc
          (3 : ZMod 2947011283543) ^ 1372 = (3 : ZMod 2947011283543) ^ (686 + 686) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 686 * (3 : ZMod 2947011283543) ^ 686 := by rw [pow_add]
          _ = 195503453929 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 2947011283543) ^ 2744 = 2439875097816 := by
        calc
          (3 : ZMod 2947011283543) ^ 2744 = (3 : ZMod 2947011283543) ^ (1372 + 1372) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1372 * (3 : ZMod 2947011283543) ^ 1372 := by rw [pow_add]
          _ = 2439875097816 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 2947011283543) ^ 5489 = 2294560076904 := by
        calc
          (3 : ZMod 2947011283543) ^ 5489 = (3 : ZMod 2947011283543) ^ (2744 + 2744 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2744 * (3 : ZMod 2947011283543) ^ 2744) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2294560076904 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 2947011283543) ^ 10978 = 1809885312495 := by
        calc
          (3 : ZMod 2947011283543) ^ 10978 = (3 : ZMod 2947011283543) ^ (5489 + 5489) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 5489 * (3 : ZMod 2947011283543) ^ 5489 := by rw [pow_add]
          _ = 1809885312495 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 2947011283543) ^ 21956 = 452296227045 := by
        calc
          (3 : ZMod 2947011283543) ^ 21956 = (3 : ZMod 2947011283543) ^ (10978 + 10978) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 10978 * (3 : ZMod 2947011283543) ^ 10978 := by rw [pow_add]
          _ = 452296227045 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 2947011283543) ^ 43913 = 812959670325 := by
        calc
          (3 : ZMod 2947011283543) ^ 43913 = (3 : ZMod 2947011283543) ^ (21956 + 21956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 21956 * (3 : ZMod 2947011283543) ^ 21956) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 812959670325 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 2947011283543) ^ 87827 = 1962160883968 := by
        calc
          (3 : ZMod 2947011283543) ^ 87827 = (3 : ZMod 2947011283543) ^ (43913 + 43913 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 43913 * (3 : ZMod 2947011283543) ^ 43913) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1962160883968 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 2947011283543) ^ 175655 = 1232251338030 := by
        calc
          (3 : ZMod 2947011283543) ^ 175655 = (3 : ZMod 2947011283543) ^ (87827 + 87827 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 87827 * (3 : ZMod 2947011283543) ^ 87827) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1232251338030 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 2947011283543) ^ 351311 = 1055008997465 := by
        calc
          (3 : ZMod 2947011283543) ^ 351311 = (3 : ZMod 2947011283543) ^ (175655 + 175655 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 175655 * (3 : ZMod 2947011283543) ^ 175655) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1055008997465 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 2947011283543) ^ 702622 = 524188685512 := by
        calc
          (3 : ZMod 2947011283543) ^ 702622 = (3 : ZMod 2947011283543) ^ (351311 + 351311) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 351311 * (3 : ZMod 2947011283543) ^ 351311 := by rw [pow_add]
          _ = 524188685512 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 2947011283543) ^ 1405244 = 2488557748750 := by
        calc
          (3 : ZMod 2947011283543) ^ 1405244 = (3 : ZMod 2947011283543) ^ (702622 + 702622) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 702622 * (3 : ZMod 2947011283543) ^ 702622 := by rw [pow_add]
          _ = 2488557748750 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 2947011283543) ^ 2810488 = 132783411305 := by
        calc
          (3 : ZMod 2947011283543) ^ 2810488 = (3 : ZMod 2947011283543) ^ (1405244 + 1405244) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1405244 * (3 : ZMod 2947011283543) ^ 1405244 := by rw [pow_add]
          _ = 132783411305 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 2947011283543) ^ 5620977 = 960055241846 := by
        calc
          (3 : ZMod 2947011283543) ^ 5620977 = (3 : ZMod 2947011283543) ^ (2810488 + 2810488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2810488 * (3 : ZMod 2947011283543) ^ 2810488) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 960055241846 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 2947011283543) ^ 11241955 = 1515492069504 := by
        calc
          (3 : ZMod 2947011283543) ^ 11241955 = (3 : ZMod 2947011283543) ^ (5620977 + 5620977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 5620977 * (3 : ZMod 2947011283543) ^ 5620977) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1515492069504 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 2947011283543) ^ 22483911 = 2480171309382 := by
        calc
          (3 : ZMod 2947011283543) ^ 22483911 = (3 : ZMod 2947011283543) ^ (11241955 + 11241955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 11241955 * (3 : ZMod 2947011283543) ^ 11241955) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2480171309382 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 2947011283543) ^ 44967823 = 296375322465 := by
        calc
          (3 : ZMod 2947011283543) ^ 44967823 = (3 : ZMod 2947011283543) ^ (22483911 + 22483911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 22483911 * (3 : ZMod 2947011283543) ^ 22483911) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 296375322465 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 2947011283543) ^ 89935647 = 1829681655947 := by
        calc
          (3 : ZMod 2947011283543) ^ 89935647 = (3 : ZMod 2947011283543) ^ (44967823 + 44967823 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 44967823 * (3 : ZMod 2947011283543) ^ 44967823) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1829681655947 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 2947011283543) ^ 179871294 = 831341708411 := by
        calc
          (3 : ZMod 2947011283543) ^ 179871294 = (3 : ZMod 2947011283543) ^ (89935647 + 89935647) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 89935647 * (3 : ZMod 2947011283543) ^ 89935647 := by rw [pow_add]
          _ = 831341708411 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 2947011283543) ^ 359742588 = 1875750006278 := by
        calc
          (3 : ZMod 2947011283543) ^ 359742588 = (3 : ZMod 2947011283543) ^ (179871294 + 179871294) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 179871294 * (3 : ZMod 2947011283543) ^ 179871294 := by rw [pow_add]
          _ = 1875750006278 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 2947011283543) ^ 719485176 = 612874999957 := by
        calc
          (3 : ZMod 2947011283543) ^ 719485176 = (3 : ZMod 2947011283543) ^ (359742588 + 359742588) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 359742588 * (3 : ZMod 2947011283543) ^ 359742588 := by rw [pow_add]
          _ = 612874999957 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 2947011283543) ^ 1438970353 = 1096432078932 := by
        calc
          (3 : ZMod 2947011283543) ^ 1438970353 = (3 : ZMod 2947011283543) ^ (719485176 + 719485176 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 719485176 * (3 : ZMod 2947011283543) ^ 719485176) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1096432078932 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 2947011283543) ^ 2877940706 = 867555248240 := by
        calc
          (3 : ZMod 2947011283543) ^ 2877940706 = (3 : ZMod 2947011283543) ^ (1438970353 + 1438970353) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1438970353 * (3 : ZMod 2947011283543) ^ 1438970353 := by rw [pow_add]
          _ = 867555248240 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 2947011283543) ^ 5755881413 = 2749958052100 := by
        calc
          (3 : ZMod 2947011283543) ^ 5755881413 = (3 : ZMod 2947011283543) ^ (2877940706 + 2877940706 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2877940706 * (3 : ZMod 2947011283543) ^ 2877940706) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2749958052100 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 2947011283543) ^ 11511762826 = 1413155176547 := by
        calc
          (3 : ZMod 2947011283543) ^ 11511762826 = (3 : ZMod 2947011283543) ^ (5755881413 + 5755881413) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 5755881413 * (3 : ZMod 2947011283543) ^ 5755881413 := by rw [pow_add]
          _ = 1413155176547 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 2947011283543) ^ 23023525652 = 2164338941866 := by
        calc
          (3 : ZMod 2947011283543) ^ 23023525652 = (3 : ZMod 2947011283543) ^ (11511762826 + 11511762826) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 11511762826 * (3 : ZMod 2947011283543) ^ 11511762826 := by rw [pow_add]
          _ = 2164338941866 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 2947011283543) ^ 46047051305 = 2639973151594 := by
        calc
          (3 : ZMod 2947011283543) ^ 46047051305 = (3 : ZMod 2947011283543) ^ (23023525652 + 23023525652 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 23023525652 * (3 : ZMod 2947011283543) ^ 23023525652) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2639973151594 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 2947011283543) ^ 92094102610 = 1652977063221 := by
        calc
          (3 : ZMod 2947011283543) ^ 92094102610 = (3 : ZMod 2947011283543) ^ (46047051305 + 46047051305) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 46047051305 * (3 : ZMod 2947011283543) ^ 46047051305 := by rw [pow_add]
          _ = 1652977063221 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 2947011283543) ^ 184188205221 = 1006436514573 := by
        calc
          (3 : ZMod 2947011283543) ^ 184188205221 = (3 : ZMod 2947011283543) ^ (92094102610 + 92094102610 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 92094102610 * (3 : ZMod 2947011283543) ^ 92094102610) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1006436514573 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 2947011283543) ^ 368376410442 = 493824330223 := by
        calc
          (3 : ZMod 2947011283543) ^ 368376410442 = (3 : ZMod 2947011283543) ^ (184188205221 + 184188205221) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 184188205221 * (3 : ZMod 2947011283543) ^ 184188205221 := by rw [pow_add]
          _ = 493824330223 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 2947011283543) ^ 736752820885 = 855880266016 := by
        calc
          (3 : ZMod 2947011283543) ^ 736752820885 = (3 : ZMod 2947011283543) ^ (368376410442 + 368376410442 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 368376410442 * (3 : ZMod 2947011283543) ^ 368376410442) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 855880266016 := by rw [fermat_38]; decide
      have fermat_40 : (3 : ZMod 2947011283543) ^ 1473505641771 = 2947011283542 := by
        calc
          (3 : ZMod 2947011283543) ^ 1473505641771 = (3 : ZMod 2947011283543) ^ (736752820885 + 736752820885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 736752820885 * (3 : ZMod 2947011283543) ^ 736752820885) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2947011283542 := by rw [fermat_39]; decide
      have fermat_41 : (3 : ZMod 2947011283543) ^ 2947011283542 = 1 := by
        calc
          (3 : ZMod 2947011283543) ^ 2947011283542 = (3 : ZMod 2947011283543) ^ (1473505641771 + 1473505641771) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1473505641771 * (3 : ZMod 2947011283543) ^ 1473505641771 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (79, 1), (15319, 1), (405857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (79, 1), (15319, 1), (405857, 1)] : List FactorBlock).map factorBlockValue).prod = 2947011283543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 2947011283543) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 2947011283543) ^ 2 = 9 := by
        calc
          (3 : ZMod 2947011283543) ^ 2 = (3 : ZMod 2947011283543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1 * (3 : ZMod 2947011283543) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 2947011283543) ^ 5 = 243 := by
        calc
          (3 : ZMod 2947011283543) ^ 5 = (3 : ZMod 2947011283543) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2 * (3 : ZMod 2947011283543) ^ 2) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 2947011283543) ^ 10 = 59049 := by
        calc
          (3 : ZMod 2947011283543) ^ 10 = (3 : ZMod 2947011283543) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 5 * (3 : ZMod 2947011283543) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 2947011283543) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 2947011283543) ^ 21 = (3 : ZMod 2947011283543) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 10 * (3 : ZMod 2947011283543) ^ 10) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 2947011283543) ^ 42 = 2481123587895 := by
        calc
          (3 : ZMod 2947011283543) ^ 42 = (3 : ZMod 2947011283543) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 21 * (3 : ZMod 2947011283543) ^ 21 := by rw [pow_add]
          _ = 2481123587895 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 2947011283543) ^ 85 = 1641276840284 := by
        calc
          (3 : ZMod 2947011283543) ^ 85 = (3 : ZMod 2947011283543) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 42 * (3 : ZMod 2947011283543) ^ 42) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1641276840284 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 2947011283543) ^ 171 = 2183160796063 := by
        calc
          (3 : ZMod 2947011283543) ^ 171 = (3 : ZMod 2947011283543) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 85 * (3 : ZMod 2947011283543) ^ 85) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2183160796063 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 2947011283543) ^ 343 = 1986490225790 := by
        calc
          (3 : ZMod 2947011283543) ^ 343 = (3 : ZMod 2947011283543) ^ (171 + 171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 171 * (3 : ZMod 2947011283543) ^ 171) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1986490225790 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 2947011283543) ^ 686 = 1847174801253 := by
        calc
          (3 : ZMod 2947011283543) ^ 686 = (3 : ZMod 2947011283543) ^ (343 + 343) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 343 * (3 : ZMod 2947011283543) ^ 343 := by rw [pow_add]
          _ = 1847174801253 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 2947011283543) ^ 1372 = 195503453929 := by
        calc
          (3 : ZMod 2947011283543) ^ 1372 = (3 : ZMod 2947011283543) ^ (686 + 686) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 686 * (3 : ZMod 2947011283543) ^ 686 := by rw [pow_add]
          _ = 195503453929 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 2947011283543) ^ 2744 = 2439875097816 := by
        calc
          (3 : ZMod 2947011283543) ^ 2744 = (3 : ZMod 2947011283543) ^ (1372 + 1372) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1372 * (3 : ZMod 2947011283543) ^ 1372 := by rw [pow_add]
          _ = 2439875097816 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 2947011283543) ^ 5489 = 2294560076904 := by
        calc
          (3 : ZMod 2947011283543) ^ 5489 = (3 : ZMod 2947011283543) ^ (2744 + 2744 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2744 * (3 : ZMod 2947011283543) ^ 2744) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2294560076904 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 2947011283543) ^ 10978 = 1809885312495 := by
        calc
          (3 : ZMod 2947011283543) ^ 10978 = (3 : ZMod 2947011283543) ^ (5489 + 5489) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 5489 * (3 : ZMod 2947011283543) ^ 5489 := by rw [pow_add]
          _ = 1809885312495 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 2947011283543) ^ 21956 = 452296227045 := by
        calc
          (3 : ZMod 2947011283543) ^ 21956 = (3 : ZMod 2947011283543) ^ (10978 + 10978) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 10978 * (3 : ZMod 2947011283543) ^ 10978 := by rw [pow_add]
          _ = 452296227045 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 2947011283543) ^ 43913 = 812959670325 := by
        calc
          (3 : ZMod 2947011283543) ^ 43913 = (3 : ZMod 2947011283543) ^ (21956 + 21956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 21956 * (3 : ZMod 2947011283543) ^ 21956) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 812959670325 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 2947011283543) ^ 87827 = 1962160883968 := by
        calc
          (3 : ZMod 2947011283543) ^ 87827 = (3 : ZMod 2947011283543) ^ (43913 + 43913 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 43913 * (3 : ZMod 2947011283543) ^ 43913) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1962160883968 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 2947011283543) ^ 175655 = 1232251338030 := by
        calc
          (3 : ZMod 2947011283543) ^ 175655 = (3 : ZMod 2947011283543) ^ (87827 + 87827 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 87827 * (3 : ZMod 2947011283543) ^ 87827) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1232251338030 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 2947011283543) ^ 351311 = 1055008997465 := by
        calc
          (3 : ZMod 2947011283543) ^ 351311 = (3 : ZMod 2947011283543) ^ (175655 + 175655 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 175655 * (3 : ZMod 2947011283543) ^ 175655) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1055008997465 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 2947011283543) ^ 702622 = 524188685512 := by
        calc
          (3 : ZMod 2947011283543) ^ 702622 = (3 : ZMod 2947011283543) ^ (351311 + 351311) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 351311 * (3 : ZMod 2947011283543) ^ 351311 := by rw [pow_add]
          _ = 524188685512 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 2947011283543) ^ 1405244 = 2488557748750 := by
        calc
          (3 : ZMod 2947011283543) ^ 1405244 = (3 : ZMod 2947011283543) ^ (702622 + 702622) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 702622 * (3 : ZMod 2947011283543) ^ 702622 := by rw [pow_add]
          _ = 2488557748750 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 2947011283543) ^ 2810488 = 132783411305 := by
        calc
          (3 : ZMod 2947011283543) ^ 2810488 = (3 : ZMod 2947011283543) ^ (1405244 + 1405244) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1405244 * (3 : ZMod 2947011283543) ^ 1405244 := by rw [pow_add]
          _ = 132783411305 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 2947011283543) ^ 5620977 = 960055241846 := by
        calc
          (3 : ZMod 2947011283543) ^ 5620977 = (3 : ZMod 2947011283543) ^ (2810488 + 2810488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2810488 * (3 : ZMod 2947011283543) ^ 2810488) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 960055241846 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 2947011283543) ^ 11241955 = 1515492069504 := by
        calc
          (3 : ZMod 2947011283543) ^ 11241955 = (3 : ZMod 2947011283543) ^ (5620977 + 5620977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 5620977 * (3 : ZMod 2947011283543) ^ 5620977) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1515492069504 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 2947011283543) ^ 22483911 = 2480171309382 := by
        calc
          (3 : ZMod 2947011283543) ^ 22483911 = (3 : ZMod 2947011283543) ^ (11241955 + 11241955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 11241955 * (3 : ZMod 2947011283543) ^ 11241955) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2480171309382 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 2947011283543) ^ 44967823 = 296375322465 := by
        calc
          (3 : ZMod 2947011283543) ^ 44967823 = (3 : ZMod 2947011283543) ^ (22483911 + 22483911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 22483911 * (3 : ZMod 2947011283543) ^ 22483911) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 296375322465 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 2947011283543) ^ 89935647 = 1829681655947 := by
        calc
          (3 : ZMod 2947011283543) ^ 89935647 = (3 : ZMod 2947011283543) ^ (44967823 + 44967823 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 44967823 * (3 : ZMod 2947011283543) ^ 44967823) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1829681655947 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 2947011283543) ^ 179871294 = 831341708411 := by
        calc
          (3 : ZMod 2947011283543) ^ 179871294 = (3 : ZMod 2947011283543) ^ (89935647 + 89935647) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 89935647 * (3 : ZMod 2947011283543) ^ 89935647 := by rw [pow_add]
          _ = 831341708411 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 2947011283543) ^ 359742588 = 1875750006278 := by
        calc
          (3 : ZMod 2947011283543) ^ 359742588 = (3 : ZMod 2947011283543) ^ (179871294 + 179871294) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 179871294 * (3 : ZMod 2947011283543) ^ 179871294 := by rw [pow_add]
          _ = 1875750006278 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 2947011283543) ^ 719485176 = 612874999957 := by
        calc
          (3 : ZMod 2947011283543) ^ 719485176 = (3 : ZMod 2947011283543) ^ (359742588 + 359742588) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 359742588 * (3 : ZMod 2947011283543) ^ 359742588 := by rw [pow_add]
          _ = 612874999957 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 2947011283543) ^ 1438970353 = 1096432078932 := by
        calc
          (3 : ZMod 2947011283543) ^ 1438970353 = (3 : ZMod 2947011283543) ^ (719485176 + 719485176 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 719485176 * (3 : ZMod 2947011283543) ^ 719485176) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1096432078932 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 2947011283543) ^ 2877940706 = 867555248240 := by
        calc
          (3 : ZMod 2947011283543) ^ 2877940706 = (3 : ZMod 2947011283543) ^ (1438970353 + 1438970353) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1438970353 * (3 : ZMod 2947011283543) ^ 1438970353 := by rw [pow_add]
          _ = 867555248240 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 2947011283543) ^ 5755881413 = 2749958052100 := by
        calc
          (3 : ZMod 2947011283543) ^ 5755881413 = (3 : ZMod 2947011283543) ^ (2877940706 + 2877940706 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2877940706 * (3 : ZMod 2947011283543) ^ 2877940706) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2749958052100 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 2947011283543) ^ 11511762826 = 1413155176547 := by
        calc
          (3 : ZMod 2947011283543) ^ 11511762826 = (3 : ZMod 2947011283543) ^ (5755881413 + 5755881413) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 5755881413 * (3 : ZMod 2947011283543) ^ 5755881413 := by rw [pow_add]
          _ = 1413155176547 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 2947011283543) ^ 23023525652 = 2164338941866 := by
        calc
          (3 : ZMod 2947011283543) ^ 23023525652 = (3 : ZMod 2947011283543) ^ (11511762826 + 11511762826) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 11511762826 * (3 : ZMod 2947011283543) ^ 11511762826 := by rw [pow_add]
          _ = 2164338941866 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 2947011283543) ^ 46047051305 = 2639973151594 := by
        calc
          (3 : ZMod 2947011283543) ^ 46047051305 = (3 : ZMod 2947011283543) ^ (23023525652 + 23023525652 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 23023525652 * (3 : ZMod 2947011283543) ^ 23023525652) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2639973151594 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 2947011283543) ^ 92094102610 = 1652977063221 := by
        calc
          (3 : ZMod 2947011283543) ^ 92094102610 = (3 : ZMod 2947011283543) ^ (46047051305 + 46047051305) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 46047051305 * (3 : ZMod 2947011283543) ^ 46047051305 := by rw [pow_add]
          _ = 1652977063221 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 2947011283543) ^ 184188205221 = 1006436514573 := by
        calc
          (3 : ZMod 2947011283543) ^ 184188205221 = (3 : ZMod 2947011283543) ^ (92094102610 + 92094102610 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 92094102610 * (3 : ZMod 2947011283543) ^ 92094102610) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1006436514573 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 2947011283543) ^ 368376410442 = 493824330223 := by
        calc
          (3 : ZMod 2947011283543) ^ 368376410442 = (3 : ZMod 2947011283543) ^ (184188205221 + 184188205221) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 184188205221 * (3 : ZMod 2947011283543) ^ 184188205221 := by rw [pow_add]
          _ = 493824330223 := by rw [factor_0_37]; decide
      have factor_0_39 : (3 : ZMod 2947011283543) ^ 736752820885 = 855880266016 := by
        calc
          (3 : ZMod 2947011283543) ^ 736752820885 = (3 : ZMod 2947011283543) ^ (368376410442 + 368376410442 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 368376410442 * (3 : ZMod 2947011283543) ^ 368376410442) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 855880266016 := by rw [factor_0_38]; decide
      have factor_0_40 : (3 : ZMod 2947011283543) ^ 1473505641771 = 2947011283542 := by
        calc
          (3 : ZMod 2947011283543) ^ 1473505641771 = (3 : ZMod 2947011283543) ^ (736752820885 + 736752820885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 736752820885 * (3 : ZMod 2947011283543) ^ 736752820885) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2947011283542 := by rw [factor_0_39]; decide
      change (3 : ZMod 2947011283543) ^ 1473505641771 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (3 : ZMod 2947011283543) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 2947011283543) ^ 3 = 27 := by
        calc
          (3 : ZMod 2947011283543) ^ 3 = (3 : ZMod 2947011283543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1 * (3 : ZMod 2947011283543) ^ 1) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 2947011283543) ^ 7 = 2187 := by
        calc
          (3 : ZMod 2947011283543) ^ 7 = (3 : ZMod 2947011283543) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 3 * (3 : ZMod 2947011283543) ^ 3) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 2947011283543) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 2947011283543) ^ 14 = (3 : ZMod 2947011283543) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 7 * (3 : ZMod 2947011283543) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 2947011283543) ^ 28 = 2247713470160 := by
        calc
          (3 : ZMod 2947011283543) ^ 28 = (3 : ZMod 2947011283543) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 14 * (3 : ZMod 2947011283543) ^ 14 := by rw [pow_add]
          _ = 2247713470160 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 2947011283543) ^ 57 = 549212499663 := by
        calc
          (3 : ZMod 2947011283543) ^ 57 = (3 : ZMod 2947011283543) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 28 * (3 : ZMod 2947011283543) ^ 28) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 549212499663 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 2947011283543) ^ 114 = 456349541277 := by
        calc
          (3 : ZMod 2947011283543) ^ 114 = (3 : ZMod 2947011283543) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 57 * (3 : ZMod 2947011283543) ^ 57 := by rw [pow_add]
          _ = 456349541277 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 2947011283543) ^ 228 = 764279419676 := by
        calc
          (3 : ZMod 2947011283543) ^ 228 = (3 : ZMod 2947011283543) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 114 * (3 : ZMod 2947011283543) ^ 114 := by rw [pow_add]
          _ = 764279419676 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 2947011283543) ^ 457 = 1900075375563 := by
        calc
          (3 : ZMod 2947011283543) ^ 457 = (3 : ZMod 2947011283543) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 228 * (3 : ZMod 2947011283543) ^ 228) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1900075375563 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 2947011283543) ^ 914 = 601734698835 := by
        calc
          (3 : ZMod 2947011283543) ^ 914 = (3 : ZMod 2947011283543) ^ (457 + 457) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 457 * (3 : ZMod 2947011283543) ^ 457 := by rw [pow_add]
          _ = 601734698835 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 2947011283543) ^ 1829 = 568873172426 := by
        calc
          (3 : ZMod 2947011283543) ^ 1829 = (3 : ZMod 2947011283543) ^ (914 + 914 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 914 * (3 : ZMod 2947011283543) ^ 914) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 568873172426 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 2947011283543) ^ 3659 = 2813596389293 := by
        calc
          (3 : ZMod 2947011283543) ^ 3659 = (3 : ZMod 2947011283543) ^ (1829 + 1829 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1829 * (3 : ZMod 2947011283543) ^ 1829) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2813596389293 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 2947011283543) ^ 7318 = 1581650643833 := by
        calc
          (3 : ZMod 2947011283543) ^ 7318 = (3 : ZMod 2947011283543) ^ (3659 + 3659) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 3659 * (3 : ZMod 2947011283543) ^ 3659 := by rw [pow_add]
          _ = 1581650643833 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 2947011283543) ^ 14637 = 2560607847907 := by
        calc
          (3 : ZMod 2947011283543) ^ 14637 = (3 : ZMod 2947011283543) ^ (7318 + 7318 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 7318 * (3 : ZMod 2947011283543) ^ 7318) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2560607847907 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 2947011283543) ^ 29275 = 1543607630226 := by
        calc
          (3 : ZMod 2947011283543) ^ 29275 = (3 : ZMod 2947011283543) ^ (14637 + 14637 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 14637 * (3 : ZMod 2947011283543) ^ 14637) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1543607630226 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 2947011283543) ^ 58551 = 883046816122 := by
        calc
          (3 : ZMod 2947011283543) ^ 58551 = (3 : ZMod 2947011283543) ^ (29275 + 29275 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 29275 * (3 : ZMod 2947011283543) ^ 29275) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 883046816122 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 2947011283543) ^ 117103 = 658422429613 := by
        calc
          (3 : ZMod 2947011283543) ^ 117103 = (3 : ZMod 2947011283543) ^ (58551 + 58551 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 58551 * (3 : ZMod 2947011283543) ^ 58551) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 658422429613 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 2947011283543) ^ 234207 = 24839236140 := by
        calc
          (3 : ZMod 2947011283543) ^ 234207 = (3 : ZMod 2947011283543) ^ (117103 + 117103 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 117103 * (3 : ZMod 2947011283543) ^ 117103) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 24839236140 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 2947011283543) ^ 468414 = 2282884055648 := by
        calc
          (3 : ZMod 2947011283543) ^ 468414 = (3 : ZMod 2947011283543) ^ (234207 + 234207) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 234207 * (3 : ZMod 2947011283543) ^ 234207 := by rw [pow_add]
          _ = 2282884055648 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 2947011283543) ^ 936829 = 339302824528 := by
        calc
          (3 : ZMod 2947011283543) ^ 936829 = (3 : ZMod 2947011283543) ^ (468414 + 468414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 468414 * (3 : ZMod 2947011283543) ^ 468414) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 339302824528 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 2947011283543) ^ 1873659 = 1437724622022 := by
        calc
          (3 : ZMod 2947011283543) ^ 1873659 = (3 : ZMod 2947011283543) ^ (936829 + 936829 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 936829 * (3 : ZMod 2947011283543) ^ 936829) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1437724622022 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 2947011283543) ^ 3747318 = 2611161955833 := by
        calc
          (3 : ZMod 2947011283543) ^ 3747318 = (3 : ZMod 2947011283543) ^ (1873659 + 1873659) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1873659 * (3 : ZMod 2947011283543) ^ 1873659 := by rw [pow_add]
          _ = 2611161955833 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 2947011283543) ^ 7494637 = 479110034623 := by
        calc
          (3 : ZMod 2947011283543) ^ 7494637 = (3 : ZMod 2947011283543) ^ (3747318 + 3747318 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 3747318 * (3 : ZMod 2947011283543) ^ 3747318) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 479110034623 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 2947011283543) ^ 14989274 = 1980606046947 := by
        calc
          (3 : ZMod 2947011283543) ^ 14989274 = (3 : ZMod 2947011283543) ^ (7494637 + 7494637) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 7494637 * (3 : ZMod 2947011283543) ^ 7494637 := by rw [pow_add]
          _ = 1980606046947 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 2947011283543) ^ 29978549 = 2509684059440 := by
        calc
          (3 : ZMod 2947011283543) ^ 29978549 = (3 : ZMod 2947011283543) ^ (14989274 + 14989274 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 14989274 * (3 : ZMod 2947011283543) ^ 14989274) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2509684059440 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 2947011283543) ^ 59957098 = 894932644419 := by
        calc
          (3 : ZMod 2947011283543) ^ 59957098 = (3 : ZMod 2947011283543) ^ (29978549 + 29978549) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 29978549 * (3 : ZMod 2947011283543) ^ 29978549 := by rw [pow_add]
          _ = 894932644419 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 2947011283543) ^ 119914196 = 2579237277824 := by
        calc
          (3 : ZMod 2947011283543) ^ 119914196 = (3 : ZMod 2947011283543) ^ (59957098 + 59957098) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 59957098 * (3 : ZMod 2947011283543) ^ 59957098 := by rw [pow_add]
          _ = 2579237277824 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 2947011283543) ^ 239828392 = 580078996152 := by
        calc
          (3 : ZMod 2947011283543) ^ 239828392 = (3 : ZMod 2947011283543) ^ (119914196 + 119914196) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 119914196 * (3 : ZMod 2947011283543) ^ 119914196 := by rw [pow_add]
          _ = 580078996152 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 2947011283543) ^ 479656784 = 2386749832120 := by
        calc
          (3 : ZMod 2947011283543) ^ 479656784 = (3 : ZMod 2947011283543) ^ (239828392 + 239828392) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 239828392 * (3 : ZMod 2947011283543) ^ 239828392 := by rw [pow_add]
          _ = 2386749832120 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 2947011283543) ^ 959313568 = 1809874574843 := by
        calc
          (3 : ZMod 2947011283543) ^ 959313568 = (3 : ZMod 2947011283543) ^ (479656784 + 479656784) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 479656784 * (3 : ZMod 2947011283543) ^ 479656784 := by rw [pow_add]
          _ = 1809874574843 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 2947011283543) ^ 1918627137 = 1927745373576 := by
        calc
          (3 : ZMod 2947011283543) ^ 1918627137 = (3 : ZMod 2947011283543) ^ (959313568 + 959313568 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 959313568 * (3 : ZMod 2947011283543) ^ 959313568) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1927745373576 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 2947011283543) ^ 3837254275 = 2052247999224 := by
        calc
          (3 : ZMod 2947011283543) ^ 3837254275 = (3 : ZMod 2947011283543) ^ (1918627137 + 1918627137 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1918627137 * (3 : ZMod 2947011283543) ^ 1918627137) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2052247999224 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 2947011283543) ^ 7674508550 = 2218348085368 := by
        calc
          (3 : ZMod 2947011283543) ^ 7674508550 = (3 : ZMod 2947011283543) ^ (3837254275 + 3837254275) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 3837254275 * (3 : ZMod 2947011283543) ^ 3837254275 := by rw [pow_add]
          _ = 2218348085368 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 2947011283543) ^ 15349017101 = 439727184636 := by
        calc
          (3 : ZMod 2947011283543) ^ 15349017101 = (3 : ZMod 2947011283543) ^ (7674508550 + 7674508550 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 7674508550 * (3 : ZMod 2947011283543) ^ 7674508550) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 439727184636 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 2947011283543) ^ 30698034203 = 2555386737456 := by
        calc
          (3 : ZMod 2947011283543) ^ 30698034203 = (3 : ZMod 2947011283543) ^ (15349017101 + 15349017101 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 15349017101 * (3 : ZMod 2947011283543) ^ 15349017101) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2555386737456 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 2947011283543) ^ 61396068407 = 2249661843524 := by
        calc
          (3 : ZMod 2947011283543) ^ 61396068407 = (3 : ZMod 2947011283543) ^ (30698034203 + 30698034203 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 30698034203 * (3 : ZMod 2947011283543) ^ 30698034203) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2249661843524 := by rw [factor_1_34]; decide
      have factor_1_36 : (3 : ZMod 2947011283543) ^ 122792136814 = 816497296905 := by
        calc
          (3 : ZMod 2947011283543) ^ 122792136814 = (3 : ZMod 2947011283543) ^ (61396068407 + 61396068407) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 61396068407 * (3 : ZMod 2947011283543) ^ 61396068407 := by rw [pow_add]
          _ = 816497296905 := by rw [factor_1_35]; decide
      have factor_1_37 : (3 : ZMod 2947011283543) ^ 245584273628 = 1901445774779 := by
        calc
          (3 : ZMod 2947011283543) ^ 245584273628 = (3 : ZMod 2947011283543) ^ (122792136814 + 122792136814) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 122792136814 * (3 : ZMod 2947011283543) ^ 122792136814 := by rw [pow_add]
          _ = 1901445774779 := by rw [factor_1_36]; decide
      have factor_1_38 : (3 : ZMod 2947011283543) ^ 491168547257 = 189685242748 := by
        calc
          (3 : ZMod 2947011283543) ^ 491168547257 = (3 : ZMod 2947011283543) ^ (245584273628 + 245584273628 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 245584273628 * (3 : ZMod 2947011283543) ^ 245584273628) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 189685242748 := by rw [factor_1_37]; decide
      have factor_1_39 : (3 : ZMod 2947011283543) ^ 982337094514 = 189685242747 := by
        calc
          (3 : ZMod 2947011283543) ^ 982337094514 = (3 : ZMod 2947011283543) ^ (491168547257 + 491168547257) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 491168547257 * (3 : ZMod 2947011283543) ^ 491168547257 := by rw [pow_add]
          _ = 189685242747 := by rw [factor_1_38]; decide
      change (3 : ZMod 2947011283543) ^ 982337094514 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (3 : ZMod 2947011283543) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 2947011283543) ^ 2 = 9 := by
        calc
          (3 : ZMod 2947011283543) ^ 2 = (3 : ZMod 2947011283543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1 * (3 : ZMod 2947011283543) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 2947011283543) ^ 4 = 81 := by
        calc
          (3 : ZMod 2947011283543) ^ 4 = (3 : ZMod 2947011283543) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 2 * (3 : ZMod 2947011283543) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 2947011283543) ^ 8 = 6561 := by
        calc
          (3 : ZMod 2947011283543) ^ 8 = (3 : ZMod 2947011283543) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 4 * (3 : ZMod 2947011283543) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 2947011283543) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 2947011283543) ^ 17 = (3 : ZMod 2947011283543) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 8 * (3 : ZMod 2947011283543) ^ 8) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 2947011283543) ^ 34 = 44846096732 := by
        calc
          (3 : ZMod 2947011283543) ^ 34 = (3 : ZMod 2947011283543) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 17 * (3 : ZMod 2947011283543) ^ 17 := by rw [pow_add]
          _ = 44846096732 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 2947011283543) ^ 69 = 2042511305663 := by
        calc
          (3 : ZMod 2947011283543) ^ 69 = (3 : ZMod 2947011283543) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 34 * (3 : ZMod 2947011283543) ^ 34) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2042511305663 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 2947011283543) ^ 138 = 675790431672 := by
        calc
          (3 : ZMod 2947011283543) ^ 138 = (3 : ZMod 2947011283543) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 69 * (3 : ZMod 2947011283543) ^ 69 := by rw [pow_add]
          _ = 675790431672 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 2947011283543) ^ 277 = 976062640055 := by
        calc
          (3 : ZMod 2947011283543) ^ 277 = (3 : ZMod 2947011283543) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 138 * (3 : ZMod 2947011283543) ^ 138) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 976062640055 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 2947011283543) ^ 555 = 1441825758583 := by
        calc
          (3 : ZMod 2947011283543) ^ 555 = (3 : ZMod 2947011283543) ^ (277 + 277 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 277 * (3 : ZMod 2947011283543) ^ 277) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1441825758583 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 2947011283543) ^ 1111 = 847180359098 := by
        calc
          (3 : ZMod 2947011283543) ^ 1111 = (3 : ZMod 2947011283543) ^ (555 + 555 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 555 * (3 : ZMod 2947011283543) ^ 555) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 847180359098 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 2947011283543) ^ 2223 = 1973598955405 := by
        calc
          (3 : ZMod 2947011283543) ^ 2223 = (3 : ZMod 2947011283543) ^ (1111 + 1111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1111 * (3 : ZMod 2947011283543) ^ 1111) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1973598955405 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 2947011283543) ^ 4446 = 967157463816 := by
        calc
          (3 : ZMod 2947011283543) ^ 4446 = (3 : ZMod 2947011283543) ^ (2223 + 2223) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 2223 * (3 : ZMod 2947011283543) ^ 2223 := by rw [pow_add]
          _ = 967157463816 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 2947011283543) ^ 8893 = 1236942125712 := by
        calc
          (3 : ZMod 2947011283543) ^ 8893 = (3 : ZMod 2947011283543) ^ (4446 + 4446 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 4446 * (3 : ZMod 2947011283543) ^ 4446) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1236942125712 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 2947011283543) ^ 17787 = 996001025330 := by
        calc
          (3 : ZMod 2947011283543) ^ 17787 = (3 : ZMod 2947011283543) ^ (8893 + 8893 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 8893 * (3 : ZMod 2947011283543) ^ 8893) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 996001025330 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 2947011283543) ^ 35575 = 374263921191 := by
        calc
          (3 : ZMod 2947011283543) ^ 35575 = (3 : ZMod 2947011283543) ^ (17787 + 17787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 17787 * (3 : ZMod 2947011283543) ^ 17787) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 374263921191 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 2947011283543) ^ 71151 = 2690875250384 := by
        calc
          (3 : ZMod 2947011283543) ^ 71151 = (3 : ZMod 2947011283543) ^ (35575 + 35575 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 35575 * (3 : ZMod 2947011283543) ^ 35575) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2690875250384 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 2947011283543) ^ 142303 = 2922471241937 := by
        calc
          (3 : ZMod 2947011283543) ^ 142303 = (3 : ZMod 2947011283543) ^ (71151 + 71151 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 71151 * (3 : ZMod 2947011283543) ^ 71151) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2922471241937 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 2947011283543) ^ 284606 = 2301273886658 := by
        calc
          (3 : ZMod 2947011283543) ^ 284606 = (3 : ZMod 2947011283543) ^ (142303 + 142303) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 142303 * (3 : ZMod 2947011283543) ^ 142303 := by rw [pow_add]
          _ = 2301273886658 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 2947011283543) ^ 569212 = 1253055976234 := by
        calc
          (3 : ZMod 2947011283543) ^ 569212 = (3 : ZMod 2947011283543) ^ (284606 + 284606) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 284606 * (3 : ZMod 2947011283543) ^ 284606 := by rw [pow_add]
          _ = 1253055976234 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 2947011283543) ^ 1138425 = 909695250828 := by
        calc
          (3 : ZMod 2947011283543) ^ 1138425 = (3 : ZMod 2947011283543) ^ (569212 + 569212 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 569212 * (3 : ZMod 2947011283543) ^ 569212) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 909695250828 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 2947011283543) ^ 2276851 = 2889276320647 := by
        calc
          (3 : ZMod 2947011283543) ^ 2276851 = (3 : ZMod 2947011283543) ^ (1138425 + 1138425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1138425 * (3 : ZMod 2947011283543) ^ 1138425) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2889276320647 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 2947011283543) ^ 4553703 = 408512359193 := by
        calc
          (3 : ZMod 2947011283543) ^ 4553703 = (3 : ZMod 2947011283543) ^ (2276851 + 2276851 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2276851 * (3 : ZMod 2947011283543) ^ 2276851) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 408512359193 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 2947011283543) ^ 9107407 = 851809972699 := by
        calc
          (3 : ZMod 2947011283543) ^ 9107407 = (3 : ZMod 2947011283543) ^ (4553703 + 4553703 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 4553703 * (3 : ZMod 2947011283543) ^ 4553703) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 851809972699 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 2947011283543) ^ 18214814 = 1438005224601 := by
        calc
          (3 : ZMod 2947011283543) ^ 18214814 = (3 : ZMod 2947011283543) ^ (9107407 + 9107407) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 9107407 * (3 : ZMod 2947011283543) ^ 9107407 := by rw [pow_add]
          _ = 1438005224601 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 2947011283543) ^ 36429629 = 596417156401 := by
        calc
          (3 : ZMod 2947011283543) ^ 36429629 = (3 : ZMod 2947011283543) ^ (18214814 + 18214814 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 18214814 * (3 : ZMod 2947011283543) ^ 18214814) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 596417156401 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 2947011283543) ^ 72859258 = 2503244566931 := by
        calc
          (3 : ZMod 2947011283543) ^ 72859258 = (3 : ZMod 2947011283543) ^ (36429629 + 36429629) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 36429629 * (3 : ZMod 2947011283543) ^ 36429629 := by rw [pow_add]
          _ = 2503244566931 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 2947011283543) ^ 145718516 = 1380894486320 := by
        calc
          (3 : ZMod 2947011283543) ^ 145718516 = (3 : ZMod 2947011283543) ^ (72859258 + 72859258) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 72859258 * (3 : ZMod 2947011283543) ^ 72859258 := by rw [pow_add]
          _ = 1380894486320 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 2947011283543) ^ 291437033 = 2245744464060 := by
        calc
          (3 : ZMod 2947011283543) ^ 291437033 = (3 : ZMod 2947011283543) ^ (145718516 + 145718516 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 145718516 * (3 : ZMod 2947011283543) ^ 145718516) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2245744464060 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 2947011283543) ^ 582874067 = 150392082452 := by
        calc
          (3 : ZMod 2947011283543) ^ 582874067 = (3 : ZMod 2947011283543) ^ (291437033 + 291437033 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 291437033 * (3 : ZMod 2947011283543) ^ 291437033) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 150392082452 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 2947011283543) ^ 1165748134 = 973924529348 := by
        calc
          (3 : ZMod 2947011283543) ^ 1165748134 = (3 : ZMod 2947011283543) ^ (582874067 + 582874067) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 582874067 * (3 : ZMod 2947011283543) ^ 582874067 := by rw [pow_add]
          _ = 973924529348 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 2947011283543) ^ 2331496268 = 2332768095050 := by
        calc
          (3 : ZMod 2947011283543) ^ 2331496268 = (3 : ZMod 2947011283543) ^ (1165748134 + 1165748134) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1165748134 * (3 : ZMod 2947011283543) ^ 1165748134 := by rw [pow_add]
          _ = 2332768095050 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 2947011283543) ^ 4662992537 = 994290540102 := by
        calc
          (3 : ZMod 2947011283543) ^ 4662992537 = (3 : ZMod 2947011283543) ^ (2331496268 + 2331496268 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2331496268 * (3 : ZMod 2947011283543) ^ 2331496268) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 994290540102 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 2947011283543) ^ 9325985074 = 2326711257695 := by
        calc
          (3 : ZMod 2947011283543) ^ 9325985074 = (3 : ZMod 2947011283543) ^ (4662992537 + 4662992537) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 4662992537 * (3 : ZMod 2947011283543) ^ 4662992537 := by rw [pow_add]
          _ = 2326711257695 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 2947011283543) ^ 18651970149 = 442155428254 := by
        calc
          (3 : ZMod 2947011283543) ^ 18651970149 = (3 : ZMod 2947011283543) ^ (9325985074 + 9325985074 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 9325985074 * (3 : ZMod 2947011283543) ^ 9325985074) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 442155428254 := by rw [factor_2_33]; decide
      have factor_2_35 : (3 : ZMod 2947011283543) ^ 37303940298 = 36858415852 := by
        calc
          (3 : ZMod 2947011283543) ^ 37303940298 = (3 : ZMod 2947011283543) ^ (18651970149 + 18651970149) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 18651970149 * (3 : ZMod 2947011283543) ^ 18651970149 := by rw [pow_add]
          _ = 36858415852 := by rw [factor_2_34]; decide
      change (3 : ZMod 2947011283543) ^ 37303940298 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (3 : ZMod 2947011283543) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 2947011283543) ^ 2 = 9 := by
        calc
          (3 : ZMod 2947011283543) ^ 2 = (3 : ZMod 2947011283543) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1 * (3 : ZMod 2947011283543) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 2947011283543) ^ 5 = 243 := by
        calc
          (3 : ZMod 2947011283543) ^ 5 = (3 : ZMod 2947011283543) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 2 * (3 : ZMod 2947011283543) ^ 2) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 2947011283543) ^ 11 = 177147 := by
        calc
          (3 : ZMod 2947011283543) ^ 11 = (3 : ZMod 2947011283543) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 5 * (3 : ZMod 2947011283543) ^ 5) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 2947011283543) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 2947011283543) ^ 22 = (3 : ZMod 2947011283543) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 11 * (3 : ZMod 2947011283543) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 2947011283543) ^ 45 = 2156088635219 := by
        calc
          (3 : ZMod 2947011283543) ^ 45 = (3 : ZMod 2947011283543) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 22 * (3 : ZMod 2947011283543) ^ 22) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2156088635219 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 2947011283543) ^ 91 = 4235448578 := by
        calc
          (3 : ZMod 2947011283543) ^ 91 = (3 : ZMod 2947011283543) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 45 * (3 : ZMod 2947011283543) ^ 45) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 4235448578 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 2947011283543) ^ 183 = 496357338941 := by
        calc
          (3 : ZMod 2947011283543) ^ 183 = (3 : ZMod 2947011283543) ^ (91 + 91 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 91 * (3 : ZMod 2947011283543) ^ 91) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 496357338941 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 2947011283543) ^ 366 = 2385036746273 := by
        calc
          (3 : ZMod 2947011283543) ^ 366 = (3 : ZMod 2947011283543) ^ (183 + 183) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 183 * (3 : ZMod 2947011283543) ^ 183 := by rw [pow_add]
          _ = 2385036746273 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 2947011283543) ^ 733 = 544467484978 := by
        calc
          (3 : ZMod 2947011283543) ^ 733 = (3 : ZMod 2947011283543) ^ (366 + 366 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 366 * (3 : ZMod 2947011283543) ^ 366) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 544467484978 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 2947011283543) ^ 1467 = 2798777901298 := by
        calc
          (3 : ZMod 2947011283543) ^ 1467 = (3 : ZMod 2947011283543) ^ (733 + 733 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 733 * (3 : ZMod 2947011283543) ^ 733) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2798777901298 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 2947011283543) ^ 2935 = 249960274671 := by
        calc
          (3 : ZMod 2947011283543) ^ 2935 = (3 : ZMod 2947011283543) ^ (1467 + 1467 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1467 * (3 : ZMod 2947011283543) ^ 1467) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 249960274671 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 2947011283543) ^ 5870 = 2816482936935 := by
        calc
          (3 : ZMod 2947011283543) ^ 5870 = (3 : ZMod 2947011283543) ^ (2935 + 2935) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 2935 * (3 : ZMod 2947011283543) ^ 2935 := by rw [pow_add]
          _ = 2816482936935 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 2947011283543) ^ 11741 = 2010638031477 := by
        calc
          (3 : ZMod 2947011283543) ^ 11741 = (3 : ZMod 2947011283543) ^ (5870 + 5870 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 5870 * (3 : ZMod 2947011283543) ^ 5870) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2010638031477 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 2947011283543) ^ 23483 = 1369989758873 := by
        calc
          (3 : ZMod 2947011283543) ^ 23483 = (3 : ZMod 2947011283543) ^ (11741 + 11741 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 11741 * (3 : ZMod 2947011283543) ^ 11741) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1369989758873 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 2947011283543) ^ 46966 = 766520181737 := by
        calc
          (3 : ZMod 2947011283543) ^ 46966 = (3 : ZMod 2947011283543) ^ (23483 + 23483) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 23483 * (3 : ZMod 2947011283543) ^ 23483 := by rw [pow_add]
          _ = 766520181737 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 2947011283543) ^ 93933 = 807051957971 := by
        calc
          (3 : ZMod 2947011283543) ^ 93933 = (3 : ZMod 2947011283543) ^ (46966 + 46966 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 46966 * (3 : ZMod 2947011283543) ^ 46966) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 807051957971 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 2947011283543) ^ 187867 = 1361100119980 := by
        calc
          (3 : ZMod 2947011283543) ^ 187867 = (3 : ZMod 2947011283543) ^ (93933 + 93933 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 93933 * (3 : ZMod 2947011283543) ^ 93933) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1361100119980 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 2947011283543) ^ 375734 = 2883733763535 := by
        calc
          (3 : ZMod 2947011283543) ^ 375734 = (3 : ZMod 2947011283543) ^ (187867 + 187867) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 187867 * (3 : ZMod 2947011283543) ^ 187867 := by rw [pow_add]
          _ = 2883733763535 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 2947011283543) ^ 751469 = 326554434130 := by
        calc
          (3 : ZMod 2947011283543) ^ 751469 = (3 : ZMod 2947011283543) ^ (375734 + 375734 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 375734 * (3 : ZMod 2947011283543) ^ 375734) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 326554434130 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 2947011283543) ^ 1502939 = 2780539067691 := by
        calc
          (3 : ZMod 2947011283543) ^ 1502939 = (3 : ZMod 2947011283543) ^ (751469 + 751469 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 751469 * (3 : ZMod 2947011283543) ^ 751469) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2780539067691 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 2947011283543) ^ 3005878 = 2482300114931 := by
        calc
          (3 : ZMod 2947011283543) ^ 3005878 = (3 : ZMod 2947011283543) ^ (1502939 + 1502939) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 1502939 * (3 : ZMod 2947011283543) ^ 1502939 := by rw [pow_add]
          _ = 2482300114931 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 2947011283543) ^ 6011756 = 512715512159 := by
        calc
          (3 : ZMod 2947011283543) ^ 6011756 = (3 : ZMod 2947011283543) ^ (3005878 + 3005878) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 3005878 * (3 : ZMod 2947011283543) ^ 3005878 := by rw [pow_add]
          _ = 512715512159 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 2947011283543) ^ 12023513 = 2937644617263 := by
        calc
          (3 : ZMod 2947011283543) ^ 12023513 = (3 : ZMod 2947011283543) ^ (6011756 + 6011756 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 6011756 * (3 : ZMod 2947011283543) ^ 6011756) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2937644617263 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 2947011283543) ^ 24047027 = 1932495294065 := by
        calc
          (3 : ZMod 2947011283543) ^ 24047027 = (3 : ZMod 2947011283543) ^ (12023513 + 12023513 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 12023513 * (3 : ZMod 2947011283543) ^ 12023513) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1932495294065 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 2947011283543) ^ 48094054 = 1888320789999 := by
        calc
          (3 : ZMod 2947011283543) ^ 48094054 = (3 : ZMod 2947011283543) ^ (24047027 + 24047027) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 24047027 * (3 : ZMod 2947011283543) ^ 24047027 := by rw [pow_add]
          _ = 1888320789999 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 2947011283543) ^ 96188109 = 1477802624959 := by
        calc
          (3 : ZMod 2947011283543) ^ 96188109 = (3 : ZMod 2947011283543) ^ (48094054 + 48094054 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 48094054 * (3 : ZMod 2947011283543) ^ 48094054) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1477802624959 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 2947011283543) ^ 192376218 = 2211041778906 := by
        calc
          (3 : ZMod 2947011283543) ^ 192376218 = (3 : ZMod 2947011283543) ^ (96188109 + 96188109) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 96188109 * (3 : ZMod 2947011283543) ^ 96188109 := by rw [pow_add]
          _ = 2211041778906 := by rw [factor_3_26]; decide
      change (3 : ZMod 2947011283543) ^ 192376218 ≠ 1
      rw [factor_3_27]
      decide
    ·
      have factor_4_0 : (3 : ZMod 2947011283543) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 2947011283543) ^ 3 = 27 := by
        calc
          (3 : ZMod 2947011283543) ^ 3 = (3 : ZMod 2947011283543) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1 * (3 : ZMod 2947011283543) ^ 1) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 2947011283543) ^ 6 = 729 := by
        calc
          (3 : ZMod 2947011283543) ^ 6 = (3 : ZMod 2947011283543) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 3 * (3 : ZMod 2947011283543) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 2947011283543) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 2947011283543) ^ 13 = (3 : ZMod 2947011283543) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 6 * (3 : ZMod 2947011283543) ^ 6) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 2947011283543) ^ 27 = 1731574917901 := by
        calc
          (3 : ZMod 2947011283543) ^ 27 = (3 : ZMod 2947011283543) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 13 * (3 : ZMod 2947011283543) ^ 13) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1731574917901 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 2947011283543) ^ 55 = 1043360705588 := by
        calc
          (3 : ZMod 2947011283543) ^ 55 = (3 : ZMod 2947011283543) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 27 * (3 : ZMod 2947011283543) ^ 27) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1043360705588 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 2947011283543) ^ 110 = 2188605266097 := by
        calc
          (3 : ZMod 2947011283543) ^ 110 = (3 : ZMod 2947011283543) ^ (55 + 55) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 55 * (3 : ZMod 2947011283543) ^ 55 := by rw [pow_add]
          _ = 2188605266097 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 2947011283543) ^ 221 = 1735946416380 := by
        calc
          (3 : ZMod 2947011283543) ^ 221 = (3 : ZMod 2947011283543) ^ (110 + 110 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 110 * (3 : ZMod 2947011283543) ^ 110) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1735946416380 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 2947011283543) ^ 443 = 2099089486227 := by
        calc
          (3 : ZMod 2947011283543) ^ 443 = (3 : ZMod 2947011283543) ^ (221 + 221 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 221 * (3 : ZMod 2947011283543) ^ 221) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2099089486227 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 2947011283543) ^ 886 = 1853304779099 := by
        calc
          (3 : ZMod 2947011283543) ^ 886 = (3 : ZMod 2947011283543) ^ (443 + 443) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 443 * (3 : ZMod 2947011283543) ^ 443 := by rw [pow_add]
          _ = 1853304779099 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 2947011283543) ^ 1772 = 2919076630464 := by
        calc
          (3 : ZMod 2947011283543) ^ 1772 = (3 : ZMod 2947011283543) ^ (886 + 886) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 886 * (3 : ZMod 2947011283543) ^ 886 := by rw [pow_add]
          _ = 2919076630464 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 2947011283543) ^ 3545 = 2389450425662 := by
        calc
          (3 : ZMod 2947011283543) ^ 3545 = (3 : ZMod 2947011283543) ^ (1772 + 1772 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1772 * (3 : ZMod 2947011283543) ^ 1772) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 2389450425662 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 2947011283543) ^ 7091 = 453586774129 := by
        calc
          (3 : ZMod 2947011283543) ^ 7091 = (3 : ZMod 2947011283543) ^ (3545 + 3545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 3545 * (3 : ZMod 2947011283543) ^ 3545) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 453586774129 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 2947011283543) ^ 14182 = 2761510057249 := by
        calc
          (3 : ZMod 2947011283543) ^ 14182 = (3 : ZMod 2947011283543) ^ (7091 + 7091) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 7091 * (3 : ZMod 2947011283543) ^ 7091 := by rw [pow_add]
          _ = 2761510057249 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 2947011283543) ^ 28364 = 368765351312 := by
        calc
          (3 : ZMod 2947011283543) ^ 28364 = (3 : ZMod 2947011283543) ^ (14182 + 14182) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 14182 * (3 : ZMod 2947011283543) ^ 14182 := by rw [pow_add]
          _ = 368765351312 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 2947011283543) ^ 56728 = 904397984622 := by
        calc
          (3 : ZMod 2947011283543) ^ 56728 = (3 : ZMod 2947011283543) ^ (28364 + 28364) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 28364 * (3 : ZMod 2947011283543) ^ 28364 := by rw [pow_add]
          _ = 904397984622 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 2947011283543) ^ 113456 = 2821272358933 := by
        calc
          (3 : ZMod 2947011283543) ^ 113456 = (3 : ZMod 2947011283543) ^ (56728 + 56728) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 56728 * (3 : ZMod 2947011283543) ^ 56728 := by rw [pow_add]
          _ = 2821272358933 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 2947011283543) ^ 226912 = 2640529523979 := by
        calc
          (3 : ZMod 2947011283543) ^ 226912 = (3 : ZMod 2947011283543) ^ (113456 + 113456) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 113456 * (3 : ZMod 2947011283543) ^ 113456 := by rw [pow_add]
          _ = 2640529523979 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 2947011283543) ^ 453825 = 1436175354303 := by
        calc
          (3 : ZMod 2947011283543) ^ 453825 = (3 : ZMod 2947011283543) ^ (226912 + 226912 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 226912 * (3 : ZMod 2947011283543) ^ 226912) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1436175354303 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 2947011283543) ^ 907650 = 2063590153174 := by
        calc
          (3 : ZMod 2947011283543) ^ 907650 = (3 : ZMod 2947011283543) ^ (453825 + 453825) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 453825 * (3 : ZMod 2947011283543) ^ 453825 := by rw [pow_add]
          _ = 2063590153174 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 2947011283543) ^ 1815301 = 1367177106719 := by
        calc
          (3 : ZMod 2947011283543) ^ 1815301 = (3 : ZMod 2947011283543) ^ (907650 + 907650 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 907650 * (3 : ZMod 2947011283543) ^ 907650) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 1367177106719 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 2947011283543) ^ 3630603 = 122491562603 := by
        calc
          (3 : ZMod 2947011283543) ^ 3630603 = (3 : ZMod 2947011283543) ^ (1815301 + 1815301 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = ((3 : ZMod 2947011283543) ^ 1815301 * (3 : ZMod 2947011283543) ^ 1815301) * (3 : ZMod 2947011283543) := by rw [pow_succ, pow_add]
          _ = 122491562603 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 2947011283543) ^ 7261206 = 1242770940032 := by
        calc
          (3 : ZMod 2947011283543) ^ 7261206 = (3 : ZMod 2947011283543) ^ (3630603 + 3630603) :=
            congrArg (fun n : ℕ => (3 : ZMod 2947011283543) ^ n) (by norm_num)
          _ = (3 : ZMod 2947011283543) ^ 3630603 * (3 : ZMod 2947011283543) ^ 3630603 := by rw [pow_add]
          _ = 1242770940032 := by rw [factor_4_21]; decide
      change (3 : ZMod 2947011283543) ^ 7261206 ≠ 1
      rw [factor_4_22]
      decide

#print axioms prime_lucas_2947011283543

end TotientTailPeriodKiller
end Erdos249257
