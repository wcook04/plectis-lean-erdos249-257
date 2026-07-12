import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1566225930287 : Nat.Prime 1566225930287 := by
  apply lucas_primality 1566225930287 (5 : ZMod 1566225930287)
  ·
      have fermat_0 : (5 : ZMod 1566225930287) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 1566225930287) ^ 2 = 25 := by
        calc
          (5 : ZMod 1566225930287) ^ 2 = (5 : ZMod 1566225930287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1 * (5 : ZMod 1566225930287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 1566225930287) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1566225930287) ^ 5 = (5 : ZMod 1566225930287) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2 * (5 : ZMod 1566225930287) ^ 2) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 1566225930287) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1566225930287) ^ 11 = (5 : ZMod 1566225930287) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 5 * (5 : ZMod 1566225930287) ^ 5) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 1566225930287) ^ 22 = 389925118811 := by
        calc
          (5 : ZMod 1566225930287) ^ 22 = (5 : ZMod 1566225930287) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 11 * (5 : ZMod 1566225930287) ^ 11 := by rw [pow_add]
          _ = 389925118811 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 1566225930287) ^ 45 = 1358307827350 := by
        calc
          (5 : ZMod 1566225930287) ^ 45 = (5 : ZMod 1566225930287) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 22 * (5 : ZMod 1566225930287) ^ 22) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1358307827350 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 1566225930287) ^ 91 = 208455410222 := by
        calc
          (5 : ZMod 1566225930287) ^ 91 = (5 : ZMod 1566225930287) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 45 * (5 : ZMod 1566225930287) ^ 45) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 208455410222 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 1566225930287) ^ 182 = 8818920923 := by
        calc
          (5 : ZMod 1566225930287) ^ 182 = (5 : ZMod 1566225930287) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 91 * (5 : ZMod 1566225930287) ^ 91 := by rw [pow_add]
          _ = 8818920923 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 1566225930287) ^ 364 = 991115754088 := by
        calc
          (5 : ZMod 1566225930287) ^ 364 = (5 : ZMod 1566225930287) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 182 * (5 : ZMod 1566225930287) ^ 182 := by rw [pow_add]
          _ = 991115754088 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 1566225930287) ^ 729 = 235602198783 := by
        calc
          (5 : ZMod 1566225930287) ^ 729 = (5 : ZMod 1566225930287) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 364 * (5 : ZMod 1566225930287) ^ 364) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 235602198783 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 1566225930287) ^ 1458 = 417169437612 := by
        calc
          (5 : ZMod 1566225930287) ^ 1458 = (5 : ZMod 1566225930287) ^ (729 + 729) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 729 * (5 : ZMod 1566225930287) ^ 729 := by rw [pow_add]
          _ = 417169437612 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 1566225930287) ^ 2917 = 285773789429 := by
        calc
          (5 : ZMod 1566225930287) ^ 2917 = (5 : ZMod 1566225930287) ^ (1458 + 1458 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1458 * (5 : ZMod 1566225930287) ^ 1458) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 285773789429 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 1566225930287) ^ 5834 = 715972176161 := by
        calc
          (5 : ZMod 1566225930287) ^ 5834 = (5 : ZMod 1566225930287) ^ (2917 + 2917) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 2917 * (5 : ZMod 1566225930287) ^ 2917 := by rw [pow_add]
          _ = 715972176161 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 1566225930287) ^ 11669 = 114556264093 := by
        calc
          (5 : ZMod 1566225930287) ^ 11669 = (5 : ZMod 1566225930287) ^ (5834 + 5834 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 5834 * (5 : ZMod 1566225930287) ^ 5834) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 114556264093 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 1566225930287) ^ 23338 = 1519819803537 := by
        calc
          (5 : ZMod 1566225930287) ^ 23338 = (5 : ZMod 1566225930287) ^ (11669 + 11669) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 11669 * (5 : ZMod 1566225930287) ^ 11669 := by rw [pow_add]
          _ = 1519819803537 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 1566225930287) ^ 46677 = 861649081210 := by
        calc
          (5 : ZMod 1566225930287) ^ 46677 = (5 : ZMod 1566225930287) ^ (23338 + 23338 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 23338 * (5 : ZMod 1566225930287) ^ 23338) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 861649081210 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 1566225930287) ^ 93354 = 439868867070 := by
        calc
          (5 : ZMod 1566225930287) ^ 93354 = (5 : ZMod 1566225930287) ^ (46677 + 46677) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 46677 * (5 : ZMod 1566225930287) ^ 46677 := by rw [pow_add]
          _ = 439868867070 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 1566225930287) ^ 186708 = 478212941014 := by
        calc
          (5 : ZMod 1566225930287) ^ 186708 = (5 : ZMod 1566225930287) ^ (93354 + 93354) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 93354 * (5 : ZMod 1566225930287) ^ 93354 := by rw [pow_add]
          _ = 478212941014 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 1566225930287) ^ 373417 = 1379277845537 := by
        calc
          (5 : ZMod 1566225930287) ^ 373417 = (5 : ZMod 1566225930287) ^ (186708 + 186708 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 186708 * (5 : ZMod 1566225930287) ^ 186708) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1379277845537 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 1566225930287) ^ 746834 = 527152653127 := by
        calc
          (5 : ZMod 1566225930287) ^ 746834 = (5 : ZMod 1566225930287) ^ (373417 + 373417) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 373417 * (5 : ZMod 1566225930287) ^ 373417 := by rw [pow_add]
          _ = 527152653127 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 1566225930287) ^ 1493669 = 503355569042 := by
        calc
          (5 : ZMod 1566225930287) ^ 1493669 = (5 : ZMod 1566225930287) ^ (746834 + 746834 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 746834 * (5 : ZMod 1566225930287) ^ 746834) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 503355569042 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 1566225930287) ^ 2987338 = 18163485832 := by
        calc
          (5 : ZMod 1566225930287) ^ 2987338 = (5 : ZMod 1566225930287) ^ (1493669 + 1493669) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1493669 * (5 : ZMod 1566225930287) ^ 1493669 := by rw [pow_add]
          _ = 18163485832 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 1566225930287) ^ 5974677 = 294014613606 := by
        calc
          (5 : ZMod 1566225930287) ^ 5974677 = (5 : ZMod 1566225930287) ^ (2987338 + 2987338 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2987338 * (5 : ZMod 1566225930287) ^ 2987338) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 294014613606 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 1566225930287) ^ 11949355 = 1512555398056 := by
        calc
          (5 : ZMod 1566225930287) ^ 11949355 = (5 : ZMod 1566225930287) ^ (5974677 + 5974677 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 5974677 * (5 : ZMod 1566225930287) ^ 5974677) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1512555398056 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 1566225930287) ^ 23898711 = 956087261625 := by
        calc
          (5 : ZMod 1566225930287) ^ 23898711 = (5 : ZMod 1566225930287) ^ (11949355 + 11949355 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 11949355 * (5 : ZMod 1566225930287) ^ 11949355) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 956087261625 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 1566225930287) ^ 47797422 = 436081499181 := by
        calc
          (5 : ZMod 1566225930287) ^ 47797422 = (5 : ZMod 1566225930287) ^ (23898711 + 23898711) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 23898711 * (5 : ZMod 1566225930287) ^ 23898711 := by rw [pow_add]
          _ = 436081499181 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 1566225930287) ^ 95594844 = 2275672537 := by
        calc
          (5 : ZMod 1566225930287) ^ 95594844 = (5 : ZMod 1566225930287) ^ (47797422 + 47797422) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 47797422 * (5 : ZMod 1566225930287) ^ 47797422 := by rw [pow_add]
          _ = 2275672537 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 1566225930287) ^ 191189688 = 179036238331 := by
        calc
          (5 : ZMod 1566225930287) ^ 191189688 = (5 : ZMod 1566225930287) ^ (95594844 + 95594844) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 95594844 * (5 : ZMod 1566225930287) ^ 95594844 := by rw [pow_add]
          _ = 179036238331 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 1566225930287) ^ 382379377 = 1078570737454 := by
        calc
          (5 : ZMod 1566225930287) ^ 382379377 = (5 : ZMod 1566225930287) ^ (191189688 + 191189688 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 191189688 * (5 : ZMod 1566225930287) ^ 191189688) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1078570737454 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 1566225930287) ^ 764758755 = 756293387732 := by
        calc
          (5 : ZMod 1566225930287) ^ 764758755 = (5 : ZMod 1566225930287) ^ (382379377 + 382379377 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 382379377 * (5 : ZMod 1566225930287) ^ 382379377) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 756293387732 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 1566225930287) ^ 1529517510 = 1438461826230 := by
        calc
          (5 : ZMod 1566225930287) ^ 1529517510 = (5 : ZMod 1566225930287) ^ (764758755 + 764758755) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 764758755 * (5 : ZMod 1566225930287) ^ 764758755 := by rw [pow_add]
          _ = 1438461826230 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 1566225930287) ^ 3059035020 = 1279274463646 := by
        calc
          (5 : ZMod 1566225930287) ^ 3059035020 = (5 : ZMod 1566225930287) ^ (1529517510 + 1529517510) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1529517510 * (5 : ZMod 1566225930287) ^ 1529517510 := by rw [pow_add]
          _ = 1279274463646 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 1566225930287) ^ 6118070040 = 381598942975 := by
        calc
          (5 : ZMod 1566225930287) ^ 6118070040 = (5 : ZMod 1566225930287) ^ (3059035020 + 3059035020) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 3059035020 * (5 : ZMod 1566225930287) ^ 3059035020 := by rw [pow_add]
          _ = 381598942975 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 1566225930287) ^ 12236140080 = 600946215497 := by
        calc
          (5 : ZMod 1566225930287) ^ 12236140080 = (5 : ZMod 1566225930287) ^ (6118070040 + 6118070040) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 6118070040 * (5 : ZMod 1566225930287) ^ 6118070040 := by rw [pow_add]
          _ = 600946215497 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 1566225930287) ^ 24472280160 = 755621683060 := by
        calc
          (5 : ZMod 1566225930287) ^ 24472280160 = (5 : ZMod 1566225930287) ^ (12236140080 + 12236140080) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 12236140080 * (5 : ZMod 1566225930287) ^ 12236140080 := by rw [pow_add]
          _ = 755621683060 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 1566225930287) ^ 48944560321 = 1490430706731 := by
        calc
          (5 : ZMod 1566225930287) ^ 48944560321 = (5 : ZMod 1566225930287) ^ (24472280160 + 24472280160 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 24472280160 * (5 : ZMod 1566225930287) ^ 24472280160) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1490430706731 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 1566225930287) ^ 97889120642 = 386525731506 := by
        calc
          (5 : ZMod 1566225930287) ^ 97889120642 = (5 : ZMod 1566225930287) ^ (48944560321 + 48944560321) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 48944560321 * (5 : ZMod 1566225930287) ^ 48944560321 := by rw [pow_add]
          _ = 386525731506 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 1566225930287) ^ 195778241285 = 747641275104 := by
        calc
          (5 : ZMod 1566225930287) ^ 195778241285 = (5 : ZMod 1566225930287) ^ (97889120642 + 97889120642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 97889120642 * (5 : ZMod 1566225930287) ^ 97889120642) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 747641275104 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 1566225930287) ^ 391556482571 = 1465560892794 := by
        calc
          (5 : ZMod 1566225930287) ^ 391556482571 = (5 : ZMod 1566225930287) ^ (195778241285 + 195778241285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 195778241285 * (5 : ZMod 1566225930287) ^ 195778241285) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1465560892794 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 1566225930287) ^ 783112965143 = 1566225930286 := by
        calc
          (5 : ZMod 1566225930287) ^ 783112965143 = (5 : ZMod 1566225930287) ^ (391556482571 + 391556482571 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 391556482571 * (5 : ZMod 1566225930287) ^ 391556482571) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1566225930286 := by rw [fermat_38]; decide
      have fermat_40 : (5 : ZMod 1566225930287) ^ 1566225930286 = 1 := by
        calc
          (5 : ZMod 1566225930287) ^ 1566225930286 = (5 : ZMod 1566225930287) ^ (783112965143 + 783112965143) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 783112965143 * (5 : ZMod 1566225930287) ^ 783112965143 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (41, 1), (14737, 1), (41809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (41, 1), (14737, 1), (41809, 1)] : List FactorBlock).map factorBlockValue).prod = 1566225930287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 1566225930287) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 1566225930287) ^ 2 = 25 := by
        calc
          (5 : ZMod 1566225930287) ^ 2 = (5 : ZMod 1566225930287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1 * (5 : ZMod 1566225930287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 1566225930287) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1566225930287) ^ 5 = (5 : ZMod 1566225930287) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2 * (5 : ZMod 1566225930287) ^ 2) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 1566225930287) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1566225930287) ^ 11 = (5 : ZMod 1566225930287) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 5 * (5 : ZMod 1566225930287) ^ 5) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 1566225930287) ^ 22 = 389925118811 := by
        calc
          (5 : ZMod 1566225930287) ^ 22 = (5 : ZMod 1566225930287) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 11 * (5 : ZMod 1566225930287) ^ 11 := by rw [pow_add]
          _ = 389925118811 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 1566225930287) ^ 45 = 1358307827350 := by
        calc
          (5 : ZMod 1566225930287) ^ 45 = (5 : ZMod 1566225930287) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 22 * (5 : ZMod 1566225930287) ^ 22) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1358307827350 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 1566225930287) ^ 91 = 208455410222 := by
        calc
          (5 : ZMod 1566225930287) ^ 91 = (5 : ZMod 1566225930287) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 45 * (5 : ZMod 1566225930287) ^ 45) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 208455410222 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 1566225930287) ^ 182 = 8818920923 := by
        calc
          (5 : ZMod 1566225930287) ^ 182 = (5 : ZMod 1566225930287) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 91 * (5 : ZMod 1566225930287) ^ 91 := by rw [pow_add]
          _ = 8818920923 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 1566225930287) ^ 364 = 991115754088 := by
        calc
          (5 : ZMod 1566225930287) ^ 364 = (5 : ZMod 1566225930287) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 182 * (5 : ZMod 1566225930287) ^ 182 := by rw [pow_add]
          _ = 991115754088 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 1566225930287) ^ 729 = 235602198783 := by
        calc
          (5 : ZMod 1566225930287) ^ 729 = (5 : ZMod 1566225930287) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 364 * (5 : ZMod 1566225930287) ^ 364) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 235602198783 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 1566225930287) ^ 1458 = 417169437612 := by
        calc
          (5 : ZMod 1566225930287) ^ 1458 = (5 : ZMod 1566225930287) ^ (729 + 729) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 729 * (5 : ZMod 1566225930287) ^ 729 := by rw [pow_add]
          _ = 417169437612 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 1566225930287) ^ 2917 = 285773789429 := by
        calc
          (5 : ZMod 1566225930287) ^ 2917 = (5 : ZMod 1566225930287) ^ (1458 + 1458 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1458 * (5 : ZMod 1566225930287) ^ 1458) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 285773789429 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 1566225930287) ^ 5834 = 715972176161 := by
        calc
          (5 : ZMod 1566225930287) ^ 5834 = (5 : ZMod 1566225930287) ^ (2917 + 2917) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 2917 * (5 : ZMod 1566225930287) ^ 2917 := by rw [pow_add]
          _ = 715972176161 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 1566225930287) ^ 11669 = 114556264093 := by
        calc
          (5 : ZMod 1566225930287) ^ 11669 = (5 : ZMod 1566225930287) ^ (5834 + 5834 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 5834 * (5 : ZMod 1566225930287) ^ 5834) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 114556264093 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 1566225930287) ^ 23338 = 1519819803537 := by
        calc
          (5 : ZMod 1566225930287) ^ 23338 = (5 : ZMod 1566225930287) ^ (11669 + 11669) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 11669 * (5 : ZMod 1566225930287) ^ 11669 := by rw [pow_add]
          _ = 1519819803537 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 1566225930287) ^ 46677 = 861649081210 := by
        calc
          (5 : ZMod 1566225930287) ^ 46677 = (5 : ZMod 1566225930287) ^ (23338 + 23338 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 23338 * (5 : ZMod 1566225930287) ^ 23338) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 861649081210 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 1566225930287) ^ 93354 = 439868867070 := by
        calc
          (5 : ZMod 1566225930287) ^ 93354 = (5 : ZMod 1566225930287) ^ (46677 + 46677) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 46677 * (5 : ZMod 1566225930287) ^ 46677 := by rw [pow_add]
          _ = 439868867070 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 1566225930287) ^ 186708 = 478212941014 := by
        calc
          (5 : ZMod 1566225930287) ^ 186708 = (5 : ZMod 1566225930287) ^ (93354 + 93354) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 93354 * (5 : ZMod 1566225930287) ^ 93354 := by rw [pow_add]
          _ = 478212941014 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 1566225930287) ^ 373417 = 1379277845537 := by
        calc
          (5 : ZMod 1566225930287) ^ 373417 = (5 : ZMod 1566225930287) ^ (186708 + 186708 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 186708 * (5 : ZMod 1566225930287) ^ 186708) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1379277845537 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 1566225930287) ^ 746834 = 527152653127 := by
        calc
          (5 : ZMod 1566225930287) ^ 746834 = (5 : ZMod 1566225930287) ^ (373417 + 373417) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 373417 * (5 : ZMod 1566225930287) ^ 373417 := by rw [pow_add]
          _ = 527152653127 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 1566225930287) ^ 1493669 = 503355569042 := by
        calc
          (5 : ZMod 1566225930287) ^ 1493669 = (5 : ZMod 1566225930287) ^ (746834 + 746834 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 746834 * (5 : ZMod 1566225930287) ^ 746834) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 503355569042 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 1566225930287) ^ 2987338 = 18163485832 := by
        calc
          (5 : ZMod 1566225930287) ^ 2987338 = (5 : ZMod 1566225930287) ^ (1493669 + 1493669) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1493669 * (5 : ZMod 1566225930287) ^ 1493669 := by rw [pow_add]
          _ = 18163485832 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 1566225930287) ^ 5974677 = 294014613606 := by
        calc
          (5 : ZMod 1566225930287) ^ 5974677 = (5 : ZMod 1566225930287) ^ (2987338 + 2987338 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2987338 * (5 : ZMod 1566225930287) ^ 2987338) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 294014613606 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 1566225930287) ^ 11949355 = 1512555398056 := by
        calc
          (5 : ZMod 1566225930287) ^ 11949355 = (5 : ZMod 1566225930287) ^ (5974677 + 5974677 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 5974677 * (5 : ZMod 1566225930287) ^ 5974677) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1512555398056 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 1566225930287) ^ 23898711 = 956087261625 := by
        calc
          (5 : ZMod 1566225930287) ^ 23898711 = (5 : ZMod 1566225930287) ^ (11949355 + 11949355 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 11949355 * (5 : ZMod 1566225930287) ^ 11949355) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 956087261625 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 1566225930287) ^ 47797422 = 436081499181 := by
        calc
          (5 : ZMod 1566225930287) ^ 47797422 = (5 : ZMod 1566225930287) ^ (23898711 + 23898711) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 23898711 * (5 : ZMod 1566225930287) ^ 23898711 := by rw [pow_add]
          _ = 436081499181 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 1566225930287) ^ 95594844 = 2275672537 := by
        calc
          (5 : ZMod 1566225930287) ^ 95594844 = (5 : ZMod 1566225930287) ^ (47797422 + 47797422) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 47797422 * (5 : ZMod 1566225930287) ^ 47797422 := by rw [pow_add]
          _ = 2275672537 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 1566225930287) ^ 191189688 = 179036238331 := by
        calc
          (5 : ZMod 1566225930287) ^ 191189688 = (5 : ZMod 1566225930287) ^ (95594844 + 95594844) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 95594844 * (5 : ZMod 1566225930287) ^ 95594844 := by rw [pow_add]
          _ = 179036238331 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 1566225930287) ^ 382379377 = 1078570737454 := by
        calc
          (5 : ZMod 1566225930287) ^ 382379377 = (5 : ZMod 1566225930287) ^ (191189688 + 191189688 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 191189688 * (5 : ZMod 1566225930287) ^ 191189688) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1078570737454 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 1566225930287) ^ 764758755 = 756293387732 := by
        calc
          (5 : ZMod 1566225930287) ^ 764758755 = (5 : ZMod 1566225930287) ^ (382379377 + 382379377 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 382379377 * (5 : ZMod 1566225930287) ^ 382379377) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 756293387732 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 1566225930287) ^ 1529517510 = 1438461826230 := by
        calc
          (5 : ZMod 1566225930287) ^ 1529517510 = (5 : ZMod 1566225930287) ^ (764758755 + 764758755) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 764758755 * (5 : ZMod 1566225930287) ^ 764758755 := by rw [pow_add]
          _ = 1438461826230 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 1566225930287) ^ 3059035020 = 1279274463646 := by
        calc
          (5 : ZMod 1566225930287) ^ 3059035020 = (5 : ZMod 1566225930287) ^ (1529517510 + 1529517510) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1529517510 * (5 : ZMod 1566225930287) ^ 1529517510 := by rw [pow_add]
          _ = 1279274463646 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 1566225930287) ^ 6118070040 = 381598942975 := by
        calc
          (5 : ZMod 1566225930287) ^ 6118070040 = (5 : ZMod 1566225930287) ^ (3059035020 + 3059035020) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 3059035020 * (5 : ZMod 1566225930287) ^ 3059035020 := by rw [pow_add]
          _ = 381598942975 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 1566225930287) ^ 12236140080 = 600946215497 := by
        calc
          (5 : ZMod 1566225930287) ^ 12236140080 = (5 : ZMod 1566225930287) ^ (6118070040 + 6118070040) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 6118070040 * (5 : ZMod 1566225930287) ^ 6118070040 := by rw [pow_add]
          _ = 600946215497 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 1566225930287) ^ 24472280160 = 755621683060 := by
        calc
          (5 : ZMod 1566225930287) ^ 24472280160 = (5 : ZMod 1566225930287) ^ (12236140080 + 12236140080) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 12236140080 * (5 : ZMod 1566225930287) ^ 12236140080 := by rw [pow_add]
          _ = 755621683060 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 1566225930287) ^ 48944560321 = 1490430706731 := by
        calc
          (5 : ZMod 1566225930287) ^ 48944560321 = (5 : ZMod 1566225930287) ^ (24472280160 + 24472280160 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 24472280160 * (5 : ZMod 1566225930287) ^ 24472280160) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1490430706731 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 1566225930287) ^ 97889120642 = 386525731506 := by
        calc
          (5 : ZMod 1566225930287) ^ 97889120642 = (5 : ZMod 1566225930287) ^ (48944560321 + 48944560321) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 48944560321 * (5 : ZMod 1566225930287) ^ 48944560321 := by rw [pow_add]
          _ = 386525731506 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 1566225930287) ^ 195778241285 = 747641275104 := by
        calc
          (5 : ZMod 1566225930287) ^ 195778241285 = (5 : ZMod 1566225930287) ^ (97889120642 + 97889120642 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 97889120642 * (5 : ZMod 1566225930287) ^ 97889120642) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 747641275104 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 1566225930287) ^ 391556482571 = 1465560892794 := by
        calc
          (5 : ZMod 1566225930287) ^ 391556482571 = (5 : ZMod 1566225930287) ^ (195778241285 + 195778241285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 195778241285 * (5 : ZMod 1566225930287) ^ 195778241285) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1465560892794 := by rw [factor_0_37]; decide
      have factor_0_39 : (5 : ZMod 1566225930287) ^ 783112965143 = 1566225930286 := by
        calc
          (5 : ZMod 1566225930287) ^ 783112965143 = (5 : ZMod 1566225930287) ^ (391556482571 + 391556482571 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 391556482571 * (5 : ZMod 1566225930287) ^ 391556482571) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1566225930286 := by rw [factor_0_38]; decide
      change (5 : ZMod 1566225930287) ^ 783112965143 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (5 : ZMod 1566225930287) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 1566225930287) ^ 2 = 25 := by
        calc
          (5 : ZMod 1566225930287) ^ 2 = (5 : ZMod 1566225930287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1 * (5 : ZMod 1566225930287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 1566225930287) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1566225930287) ^ 5 = (5 : ZMod 1566225930287) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2 * (5 : ZMod 1566225930287) ^ 2) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 1566225930287) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1566225930287) ^ 11 = (5 : ZMod 1566225930287) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 5 * (5 : ZMod 1566225930287) ^ 5) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 1566225930287) ^ 23 = 383399663768 := by
        calc
          (5 : ZMod 1566225930287) ^ 23 = (5 : ZMod 1566225930287) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 11 * (5 : ZMod 1566225930287) ^ 11) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 383399663768 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 1566225930287) ^ 47 = 1066951147723 := by
        calc
          (5 : ZMod 1566225930287) ^ 47 = (5 : ZMod 1566225930287) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 23 * (5 : ZMod 1566225930287) ^ 23) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1066951147723 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 1566225930287) ^ 94 = 997311393158 := by
        calc
          (5 : ZMod 1566225930287) ^ 94 = (5 : ZMod 1566225930287) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 47 * (5 : ZMod 1566225930287) ^ 47 := by rw [pow_add]
          _ = 997311393158 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 1566225930287) ^ 188 = 1533983486906 := by
        calc
          (5 : ZMod 1566225930287) ^ 188 = (5 : ZMod 1566225930287) ^ (94 + 94) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 94 * (5 : ZMod 1566225930287) ^ 94 := by rw [pow_add]
          _ = 1533983486906 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 1566225930287) ^ 376 = 392959250016 := by
        calc
          (5 : ZMod 1566225930287) ^ 376 = (5 : ZMod 1566225930287) ^ (188 + 188) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 188 * (5 : ZMod 1566225930287) ^ 188 := by rw [pow_add]
          _ = 392959250016 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 1566225930287) ^ 752 = 460953979885 := by
        calc
          (5 : ZMod 1566225930287) ^ 752 = (5 : ZMod 1566225930287) ^ (376 + 376) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 376 * (5 : ZMod 1566225930287) ^ 376 := by rw [pow_add]
          _ = 460953979885 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 1566225930287) ^ 1505 = 188184975413 := by
        calc
          (5 : ZMod 1566225930287) ^ 1505 = (5 : ZMod 1566225930287) ^ (752 + 752 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 752 * (5 : ZMod 1566225930287) ^ 752) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 188184975413 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 1566225930287) ^ 3011 = 925535445526 := by
        calc
          (5 : ZMod 1566225930287) ^ 3011 = (5 : ZMod 1566225930287) ^ (1505 + 1505 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1505 * (5 : ZMod 1566225930287) ^ 1505) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 925535445526 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 1566225930287) ^ 6022 = 724679352199 := by
        calc
          (5 : ZMod 1566225930287) ^ 6022 = (5 : ZMod 1566225930287) ^ (3011 + 3011) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 3011 * (5 : ZMod 1566225930287) ^ 3011 := by rw [pow_add]
          _ = 724679352199 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 1566225930287) ^ 12045 = 1268047180624 := by
        calc
          (5 : ZMod 1566225930287) ^ 12045 = (5 : ZMod 1566225930287) ^ (6022 + 6022 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 6022 * (5 : ZMod 1566225930287) ^ 6022) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1268047180624 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 1566225930287) ^ 24091 = 321452515373 := by
        calc
          (5 : ZMod 1566225930287) ^ 24091 = (5 : ZMod 1566225930287) ^ (12045 + 12045 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 12045 * (5 : ZMod 1566225930287) ^ 12045) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 321452515373 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 1566225930287) ^ 48182 = 1415250956488 := by
        calc
          (5 : ZMod 1566225930287) ^ 48182 = (5 : ZMod 1566225930287) ^ (24091 + 24091) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 24091 * (5 : ZMod 1566225930287) ^ 24091 := by rw [pow_add]
          _ = 1415250956488 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 1566225930287) ^ 96365 = 291030335196 := by
        calc
          (5 : ZMod 1566225930287) ^ 96365 = (5 : ZMod 1566225930287) ^ (48182 + 48182 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 48182 * (5 : ZMod 1566225930287) ^ 48182) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 291030335196 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 1566225930287) ^ 192731 = 314690085747 := by
        calc
          (5 : ZMod 1566225930287) ^ 192731 = (5 : ZMod 1566225930287) ^ (96365 + 96365 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 96365 * (5 : ZMod 1566225930287) ^ 96365) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 314690085747 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 1566225930287) ^ 385463 = 1517259755380 := by
        calc
          (5 : ZMod 1566225930287) ^ 385463 = (5 : ZMod 1566225930287) ^ (192731 + 192731 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 192731 * (5 : ZMod 1566225930287) ^ 192731) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1517259755380 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 1566225930287) ^ 770926 = 1459873466296 := by
        calc
          (5 : ZMod 1566225930287) ^ 770926 = (5 : ZMod 1566225930287) ^ (385463 + 385463) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 385463 * (5 : ZMod 1566225930287) ^ 385463 := by rw [pow_add]
          _ = 1459873466296 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 1566225930287) ^ 1541852 = 998569468588 := by
        calc
          (5 : ZMod 1566225930287) ^ 1541852 = (5 : ZMod 1566225930287) ^ (770926 + 770926) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 770926 * (5 : ZMod 1566225930287) ^ 770926 := by rw [pow_add]
          _ = 998569468588 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 1566225930287) ^ 3083704 = 1301173705861 := by
        calc
          (5 : ZMod 1566225930287) ^ 3083704 = (5 : ZMod 1566225930287) ^ (1541852 + 1541852) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1541852 * (5 : ZMod 1566225930287) ^ 1541852 := by rw [pow_add]
          _ = 1301173705861 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 1566225930287) ^ 6167409 = 1156809985635 := by
        calc
          (5 : ZMod 1566225930287) ^ 6167409 = (5 : ZMod 1566225930287) ^ (3083704 + 3083704 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 3083704 * (5 : ZMod 1566225930287) ^ 3083704) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1156809985635 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 1566225930287) ^ 12334818 = 694885327621 := by
        calc
          (5 : ZMod 1566225930287) ^ 12334818 = (5 : ZMod 1566225930287) ^ (6167409 + 6167409) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 6167409 * (5 : ZMod 1566225930287) ^ 6167409 := by rw [pow_add]
          _ = 694885327621 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 1566225930287) ^ 24669637 = 522148513669 := by
        calc
          (5 : ZMod 1566225930287) ^ 24669637 = (5 : ZMod 1566225930287) ^ (12334818 + 12334818 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 12334818 * (5 : ZMod 1566225930287) ^ 12334818) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 522148513669 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 1566225930287) ^ 49339274 = 1400341670345 := by
        calc
          (5 : ZMod 1566225930287) ^ 49339274 = (5 : ZMod 1566225930287) ^ (24669637 + 24669637) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 24669637 * (5 : ZMod 1566225930287) ^ 24669637 := by rw [pow_add]
          _ = 1400341670345 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 1566225930287) ^ 98678549 = 572679741683 := by
        calc
          (5 : ZMod 1566225930287) ^ 98678549 = (5 : ZMod 1566225930287) ^ (49339274 + 49339274 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 49339274 * (5 : ZMod 1566225930287) ^ 49339274) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 572679741683 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 1566225930287) ^ 197357098 = 1520320927486 := by
        calc
          (5 : ZMod 1566225930287) ^ 197357098 = (5 : ZMod 1566225930287) ^ (98678549 + 98678549) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 98678549 * (5 : ZMod 1566225930287) ^ 98678549 := by rw [pow_add]
          _ = 1520320927486 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 1566225930287) ^ 394714196 = 44529487314 := by
        calc
          (5 : ZMod 1566225930287) ^ 394714196 = (5 : ZMod 1566225930287) ^ (197357098 + 197357098) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 197357098 * (5 : ZMod 1566225930287) ^ 197357098 := by rw [pow_add]
          _ = 44529487314 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 1566225930287) ^ 789428392 = 883493198761 := by
        calc
          (5 : ZMod 1566225930287) ^ 789428392 = (5 : ZMod 1566225930287) ^ (394714196 + 394714196) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 394714196 * (5 : ZMod 1566225930287) ^ 394714196 := by rw [pow_add]
          _ = 883493198761 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 1566225930287) ^ 1578856784 = 252858518316 := by
        calc
          (5 : ZMod 1566225930287) ^ 1578856784 = (5 : ZMod 1566225930287) ^ (789428392 + 789428392) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 789428392 * (5 : ZMod 1566225930287) ^ 789428392 := by rw [pow_add]
          _ = 252858518316 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 1566225930287) ^ 3157713569 = 625833315155 := by
        calc
          (5 : ZMod 1566225930287) ^ 3157713569 = (5 : ZMod 1566225930287) ^ (1578856784 + 1578856784 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1578856784 * (5 : ZMod 1566225930287) ^ 1578856784) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 625833315155 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 1566225930287) ^ 6315427138 = 60939802837 := by
        calc
          (5 : ZMod 1566225930287) ^ 6315427138 = (5 : ZMod 1566225930287) ^ (3157713569 + 3157713569) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 3157713569 * (5 : ZMod 1566225930287) ^ 3157713569 := by rw [pow_add]
          _ = 60939802837 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 1566225930287) ^ 12630854276 = 137279711376 := by
        calc
          (5 : ZMod 1566225930287) ^ 12630854276 = (5 : ZMod 1566225930287) ^ (6315427138 + 6315427138) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 6315427138 * (5 : ZMod 1566225930287) ^ 6315427138 := by rw [pow_add]
          _ = 137279711376 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 1566225930287) ^ 25261708553 = 779495879529 := by
        calc
          (5 : ZMod 1566225930287) ^ 25261708553 = (5 : ZMod 1566225930287) ^ (12630854276 + 12630854276 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 12630854276 * (5 : ZMod 1566225930287) ^ 12630854276) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 779495879529 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 1566225930287) ^ 50523417106 = 180571759956 := by
        calc
          (5 : ZMod 1566225930287) ^ 50523417106 = (5 : ZMod 1566225930287) ^ (25261708553 + 25261708553) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 25261708553 * (5 : ZMod 1566225930287) ^ 25261708553 := by rw [pow_add]
          _ = 180571759956 := by rw [factor_1_34]; decide
      change (5 : ZMod 1566225930287) ^ 50523417106 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (5 : ZMod 1566225930287) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 1566225930287) ^ 2 = 25 := by
        calc
          (5 : ZMod 1566225930287) ^ 2 = (5 : ZMod 1566225930287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1 * (5 : ZMod 1566225930287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 1566225930287) ^ 4 = 625 := by
        calc
          (5 : ZMod 1566225930287) ^ 4 = (5 : ZMod 1566225930287) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 2 * (5 : ZMod 1566225930287) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 1566225930287) ^ 8 = 390625 := by
        calc
          (5 : ZMod 1566225930287) ^ 8 = (5 : ZMod 1566225930287) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 4 * (5 : ZMod 1566225930287) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 1566225930287) ^ 17 = 762939453125 := by
        calc
          (5 : ZMod 1566225930287) ^ 17 = (5 : ZMod 1566225930287) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 8 * (5 : ZMod 1566225930287) ^ 8) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 762939453125 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 1566225930287) ^ 35 = 400605147405 := by
        calc
          (5 : ZMod 1566225930287) ^ 35 = (5 : ZMod 1566225930287) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 17 * (5 : ZMod 1566225930287) ^ 17) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 400605147405 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 1566225930287) ^ 71 = 851512544696 := by
        calc
          (5 : ZMod 1566225930287) ^ 71 = (5 : ZMod 1566225930287) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 35 * (5 : ZMod 1566225930287) ^ 35) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 851512544696 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 1566225930287) ^ 142 = 485805967588 := by
        calc
          (5 : ZMod 1566225930287) ^ 142 = (5 : ZMod 1566225930287) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 71 * (5 : ZMod 1566225930287) ^ 71 := by rw [pow_add]
          _ = 485805967588 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 1566225930287) ^ 284 = 1081759279239 := by
        calc
          (5 : ZMod 1566225930287) ^ 284 = (5 : ZMod 1566225930287) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 142 * (5 : ZMod 1566225930287) ^ 142 := by rw [pow_add]
          _ = 1081759279239 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 1566225930287) ^ 569 = 182502762082 := by
        calc
          (5 : ZMod 1566225930287) ^ 569 = (5 : ZMod 1566225930287) ^ (284 + 284 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 284 * (5 : ZMod 1566225930287) ^ 284) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 182502762082 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 1566225930287) ^ 1138 = 1274792141125 := by
        calc
          (5 : ZMod 1566225930287) ^ 1138 = (5 : ZMod 1566225930287) ^ (569 + 569) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 569 * (5 : ZMod 1566225930287) ^ 569 := by rw [pow_add]
          _ = 1274792141125 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 1566225930287) ^ 2276 = 1253536646164 := by
        calc
          (5 : ZMod 1566225930287) ^ 2276 = (5 : ZMod 1566225930287) ^ (1138 + 1138) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1138 * (5 : ZMod 1566225930287) ^ 1138 := by rw [pow_add]
          _ = 1253536646164 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 1566225930287) ^ 4553 = 611174112431 := by
        calc
          (5 : ZMod 1566225930287) ^ 4553 = (5 : ZMod 1566225930287) ^ (2276 + 2276 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2276 * (5 : ZMod 1566225930287) ^ 2276) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 611174112431 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 1566225930287) ^ 9107 = 1019074574793 := by
        calc
          (5 : ZMod 1566225930287) ^ 9107 = (5 : ZMod 1566225930287) ^ (4553 + 4553 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 4553 * (5 : ZMod 1566225930287) ^ 4553) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1019074574793 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 1566225930287) ^ 18215 = 538989182495 := by
        calc
          (5 : ZMod 1566225930287) ^ 18215 = (5 : ZMod 1566225930287) ^ (9107 + 9107 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 9107 * (5 : ZMod 1566225930287) ^ 9107) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 538989182495 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 1566225930287) ^ 36430 = 974634673575 := by
        calc
          (5 : ZMod 1566225930287) ^ 36430 = (5 : ZMod 1566225930287) ^ (18215 + 18215) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 18215 * (5 : ZMod 1566225930287) ^ 18215 := by rw [pow_add]
          _ = 974634673575 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 1566225930287) ^ 72861 = 612115381566 := by
        calc
          (5 : ZMod 1566225930287) ^ 72861 = (5 : ZMod 1566225930287) ^ (36430 + 36430 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 36430 * (5 : ZMod 1566225930287) ^ 36430) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 612115381566 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 1566225930287) ^ 145723 = 593114865932 := by
        calc
          (5 : ZMod 1566225930287) ^ 145723 = (5 : ZMod 1566225930287) ^ (72861 + 72861 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 72861 * (5 : ZMod 1566225930287) ^ 72861) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 593114865932 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 1566225930287) ^ 291447 = 1465244941363 := by
        calc
          (5 : ZMod 1566225930287) ^ 291447 = (5 : ZMod 1566225930287) ^ (145723 + 145723 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 145723 * (5 : ZMod 1566225930287) ^ 145723) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1465244941363 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 1566225930287) ^ 582895 = 854572982333 := by
        calc
          (5 : ZMod 1566225930287) ^ 582895 = (5 : ZMod 1566225930287) ^ (291447 + 291447 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 291447 * (5 : ZMod 1566225930287) ^ 291447) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 854572982333 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 1566225930287) ^ 1165790 = 1512004219854 := by
        calc
          (5 : ZMod 1566225930287) ^ 1165790 = (5 : ZMod 1566225930287) ^ (582895 + 582895) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 582895 * (5 : ZMod 1566225930287) ^ 582895 := by rw [pow_add]
          _ = 1512004219854 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 1566225930287) ^ 2331581 = 1407117712290 := by
        calc
          (5 : ZMod 1566225930287) ^ 2331581 = (5 : ZMod 1566225930287) ^ (1165790 + 1165790 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1165790 * (5 : ZMod 1566225930287) ^ 1165790) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1407117712290 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 1566225930287) ^ 4663163 = 820294013475 := by
        calc
          (5 : ZMod 1566225930287) ^ 4663163 = (5 : ZMod 1566225930287) ^ (2331581 + 2331581 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2331581 * (5 : ZMod 1566225930287) ^ 2331581) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 820294013475 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 1566225930287) ^ 9326326 = 1211509016470 := by
        calc
          (5 : ZMod 1566225930287) ^ 9326326 = (5 : ZMod 1566225930287) ^ (4663163 + 4663163) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 4663163 * (5 : ZMod 1566225930287) ^ 4663163 := by rw [pow_add]
          _ = 1211509016470 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 1566225930287) ^ 18652652 = 486149319218 := by
        calc
          (5 : ZMod 1566225930287) ^ 18652652 = (5 : ZMod 1566225930287) ^ (9326326 + 9326326) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 9326326 * (5 : ZMod 1566225930287) ^ 9326326 := by rw [pow_add]
          _ = 486149319218 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 1566225930287) ^ 37305305 = 627658220273 := by
        calc
          (5 : ZMod 1566225930287) ^ 37305305 = (5 : ZMod 1566225930287) ^ (18652652 + 18652652 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 18652652 * (5 : ZMod 1566225930287) ^ 18652652) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 627658220273 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 1566225930287) ^ 74610610 = 532305659165 := by
        calc
          (5 : ZMod 1566225930287) ^ 74610610 = (5 : ZMod 1566225930287) ^ (37305305 + 37305305) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 37305305 * (5 : ZMod 1566225930287) ^ 37305305 := by rw [pow_add]
          _ = 532305659165 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 1566225930287) ^ 149221220 = 50565948592 := by
        calc
          (5 : ZMod 1566225930287) ^ 149221220 = (5 : ZMod 1566225930287) ^ (74610610 + 74610610) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 74610610 * (5 : ZMod 1566225930287) ^ 74610610 := by rw [pow_add]
          _ = 50565948592 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 1566225930287) ^ 298442440 = 591523777474 := by
        calc
          (5 : ZMod 1566225930287) ^ 298442440 = (5 : ZMod 1566225930287) ^ (149221220 + 149221220) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 149221220 * (5 : ZMod 1566225930287) ^ 149221220 := by rw [pow_add]
          _ = 591523777474 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 1566225930287) ^ 596884881 = 1145271612856 := by
        calc
          (5 : ZMod 1566225930287) ^ 596884881 = (5 : ZMod 1566225930287) ^ (298442440 + 298442440 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 298442440 * (5 : ZMod 1566225930287) ^ 298442440) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1145271612856 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 1566225930287) ^ 1193769763 = 444044195989 := by
        calc
          (5 : ZMod 1566225930287) ^ 1193769763 = (5 : ZMod 1566225930287) ^ (596884881 + 596884881 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 596884881 * (5 : ZMod 1566225930287) ^ 596884881) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 444044195989 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 1566225930287) ^ 2387539527 = 543680636028 := by
        calc
          (5 : ZMod 1566225930287) ^ 2387539527 = (5 : ZMod 1566225930287) ^ (1193769763 + 1193769763 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1193769763 * (5 : ZMod 1566225930287) ^ 1193769763) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 543680636028 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 1566225930287) ^ 4775079055 = 620754611441 := by
        calc
          (5 : ZMod 1566225930287) ^ 4775079055 = (5 : ZMod 1566225930287) ^ (2387539527 + 2387539527 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2387539527 * (5 : ZMod 1566225930287) ^ 2387539527) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 620754611441 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 1566225930287) ^ 9550158111 = 61212793608 := by
        calc
          (5 : ZMod 1566225930287) ^ 9550158111 = (5 : ZMod 1566225930287) ^ (4775079055 + 4775079055 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 4775079055 * (5 : ZMod 1566225930287) ^ 4775079055) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 61212793608 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 1566225930287) ^ 19100316223 = 1514713363579 := by
        calc
          (5 : ZMod 1566225930287) ^ 19100316223 = (5 : ZMod 1566225930287) ^ (9550158111 + 9550158111 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 9550158111 * (5 : ZMod 1566225930287) ^ 9550158111) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1514713363579 := by rw [factor_2_33]; decide
      have factor_2_35 : (5 : ZMod 1566225930287) ^ 38200632446 = 192423822401 := by
        calc
          (5 : ZMod 1566225930287) ^ 38200632446 = (5 : ZMod 1566225930287) ^ (19100316223 + 19100316223) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 19100316223 * (5 : ZMod 1566225930287) ^ 19100316223 := by rw [pow_add]
          _ = 192423822401 := by rw [factor_2_34]; decide
      change (5 : ZMod 1566225930287) ^ 38200632446 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (5 : ZMod 1566225930287) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 1566225930287) ^ 3 = 125 := by
        calc
          (5 : ZMod 1566225930287) ^ 3 = (5 : ZMod 1566225930287) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1 * (5 : ZMod 1566225930287) ^ 1) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 1566225930287) ^ 6 = 15625 := by
        calc
          (5 : ZMod 1566225930287) ^ 6 = (5 : ZMod 1566225930287) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 3 * (5 : ZMod 1566225930287) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 1566225930287) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 1566225930287) ^ 12 = (5 : ZMod 1566225930287) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 6 * (5 : ZMod 1566225930287) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 1566225930287) ^ 25 = 187636012478 := by
        calc
          (5 : ZMod 1566225930287) ^ 25 = (5 : ZMod 1566225930287) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 12 * (5 : ZMod 1566225930287) ^ 12) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 187636012478 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 1566225930287) ^ 50 = 239689390980 := by
        calc
          (5 : ZMod 1566225930287) ^ 50 = (5 : ZMod 1566225930287) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 25 * (5 : ZMod 1566225930287) ^ 25 := by rw [pow_add]
          _ = 239689390980 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 1566225930287) ^ 101 = 1477462411648 := by
        calc
          (5 : ZMod 1566225930287) ^ 101 = (5 : ZMod 1566225930287) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 50 * (5 : ZMod 1566225930287) ^ 50) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1477462411648 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 1566225930287) ^ 202 = 1277131593424 := by
        calc
          (5 : ZMod 1566225930287) ^ 202 = (5 : ZMod 1566225930287) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 101 * (5 : ZMod 1566225930287) ^ 101 := by rw [pow_add]
          _ = 1277131593424 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 1566225930287) ^ 405 = 511435404819 := by
        calc
          (5 : ZMod 1566225930287) ^ 405 = (5 : ZMod 1566225930287) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 202 * (5 : ZMod 1566225930287) ^ 202) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 511435404819 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 1566225930287) ^ 810 = 1557860978323 := by
        calc
          (5 : ZMod 1566225930287) ^ 810 = (5 : ZMod 1566225930287) ^ (405 + 405) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 405 * (5 : ZMod 1566225930287) ^ 405 := by rw [pow_add]
          _ = 1557860978323 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 1566225930287) ^ 1621 = 986709020807 := by
        calc
          (5 : ZMod 1566225930287) ^ 1621 = (5 : ZMod 1566225930287) ^ (810 + 810 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 810 * (5 : ZMod 1566225930287) ^ 810) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 986709020807 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 1566225930287) ^ 3243 = 857781556680 := by
        calc
          (5 : ZMod 1566225930287) ^ 3243 = (5 : ZMod 1566225930287) ^ (1621 + 1621 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 1621 * (5 : ZMod 1566225930287) ^ 1621) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 857781556680 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 1566225930287) ^ 6486 = 392434324505 := by
        calc
          (5 : ZMod 1566225930287) ^ 6486 = (5 : ZMod 1566225930287) ^ (3243 + 3243) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 3243 * (5 : ZMod 1566225930287) ^ 3243 := by rw [pow_add]
          _ = 392434324505 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 1566225930287) ^ 12973 = 315968264111 := by
        calc
          (5 : ZMod 1566225930287) ^ 12973 = (5 : ZMod 1566225930287) ^ (6486 + 6486 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 6486 * (5 : ZMod 1566225930287) ^ 6486) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 315968264111 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 1566225930287) ^ 25946 = 1386541674954 := by
        calc
          (5 : ZMod 1566225930287) ^ 25946 = (5 : ZMod 1566225930287) ^ (12973 + 12973) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 12973 * (5 : ZMod 1566225930287) ^ 12973 := by rw [pow_add]
          _ = 1386541674954 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 1566225930287) ^ 51893 = 180916437140 := by
        calc
          (5 : ZMod 1566225930287) ^ 51893 = (5 : ZMod 1566225930287) ^ (25946 + 25946 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 25946 * (5 : ZMod 1566225930287) ^ 25946) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 180916437140 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 1566225930287) ^ 103787 = 407112381612 := by
        calc
          (5 : ZMod 1566225930287) ^ 103787 = (5 : ZMod 1566225930287) ^ (51893 + 51893 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 51893 * (5 : ZMod 1566225930287) ^ 51893) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 407112381612 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 1566225930287) ^ 207575 = 147924422604 := by
        calc
          (5 : ZMod 1566225930287) ^ 207575 = (5 : ZMod 1566225930287) ^ (103787 + 103787 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 103787 * (5 : ZMod 1566225930287) ^ 103787) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 147924422604 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 1566225930287) ^ 415150 = 888686720631 := by
        calc
          (5 : ZMod 1566225930287) ^ 415150 = (5 : ZMod 1566225930287) ^ (207575 + 207575) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 207575 * (5 : ZMod 1566225930287) ^ 207575 := by rw [pow_add]
          _ = 888686720631 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 1566225930287) ^ 830300 = 602017165202 := by
        calc
          (5 : ZMod 1566225930287) ^ 830300 = (5 : ZMod 1566225930287) ^ (415150 + 415150) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 415150 * (5 : ZMod 1566225930287) ^ 415150 := by rw [pow_add]
          _ = 602017165202 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 1566225930287) ^ 1660601 = 1111191589669 := by
        calc
          (5 : ZMod 1566225930287) ^ 1660601 = (5 : ZMod 1566225930287) ^ (830300 + 830300 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 830300 * (5 : ZMod 1566225930287) ^ 830300) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1111191589669 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 1566225930287) ^ 3321202 = 890613146671 := by
        calc
          (5 : ZMod 1566225930287) ^ 3321202 = (5 : ZMod 1566225930287) ^ (1660601 + 1660601) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1660601 * (5 : ZMod 1566225930287) ^ 1660601 := by rw [pow_add]
          _ = 890613146671 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 1566225930287) ^ 6642404 = 575545679019 := by
        calc
          (5 : ZMod 1566225930287) ^ 6642404 = (5 : ZMod 1566225930287) ^ (3321202 + 3321202) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 3321202 * (5 : ZMod 1566225930287) ^ 3321202 := by rw [pow_add]
          _ = 575545679019 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 1566225930287) ^ 13284809 = 1445999519634 := by
        calc
          (5 : ZMod 1566225930287) ^ 13284809 = (5 : ZMod 1566225930287) ^ (6642404 + 6642404 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 6642404 * (5 : ZMod 1566225930287) ^ 6642404) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1445999519634 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 1566225930287) ^ 26569619 = 1150617140392 := by
        calc
          (5 : ZMod 1566225930287) ^ 26569619 = (5 : ZMod 1566225930287) ^ (13284809 + 13284809 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 13284809 * (5 : ZMod 1566225930287) ^ 13284809) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1150617140392 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 1566225930287) ^ 53139239 = 1287291339059 := by
        calc
          (5 : ZMod 1566225930287) ^ 53139239 = (5 : ZMod 1566225930287) ^ (26569619 + 26569619 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 26569619 * (5 : ZMod 1566225930287) ^ 26569619) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1287291339059 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 1566225930287) ^ 106278478 = 1351619018837 := by
        calc
          (5 : ZMod 1566225930287) ^ 106278478 = (5 : ZMod 1566225930287) ^ (53139239 + 53139239) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 53139239 * (5 : ZMod 1566225930287) ^ 53139239 := by rw [pow_add]
          _ = 1351619018837 := by rw [factor_3_25]; decide
      change (5 : ZMod 1566225930287) ^ 106278478 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (5 : ZMod 1566225930287) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 1566225930287) ^ 2 = 25 := by
        calc
          (5 : ZMod 1566225930287) ^ 2 = (5 : ZMod 1566225930287) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1 * (5 : ZMod 1566225930287) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 1566225930287) ^ 4 = 625 := by
        calc
          (5 : ZMod 1566225930287) ^ 4 = (5 : ZMod 1566225930287) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 2 * (5 : ZMod 1566225930287) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 1566225930287) ^ 8 = 390625 := by
        calc
          (5 : ZMod 1566225930287) ^ 8 = (5 : ZMod 1566225930287) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 4 * (5 : ZMod 1566225930287) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 1566225930287) ^ 17 = 762939453125 := by
        calc
          (5 : ZMod 1566225930287) ^ 17 = (5 : ZMod 1566225930287) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 8 * (5 : ZMod 1566225930287) ^ 8) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 762939453125 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 1566225930287) ^ 35 = 400605147405 := by
        calc
          (5 : ZMod 1566225930287) ^ 35 = (5 : ZMod 1566225930287) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 17 * (5 : ZMod 1566225930287) ^ 17) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 400605147405 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 1566225930287) ^ 71 = 851512544696 := by
        calc
          (5 : ZMod 1566225930287) ^ 71 = (5 : ZMod 1566225930287) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 35 * (5 : ZMod 1566225930287) ^ 35) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 851512544696 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 1566225930287) ^ 142 = 485805967588 := by
        calc
          (5 : ZMod 1566225930287) ^ 142 = (5 : ZMod 1566225930287) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 71 * (5 : ZMod 1566225930287) ^ 71 := by rw [pow_add]
          _ = 485805967588 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 1566225930287) ^ 285 = 710118605334 := by
        calc
          (5 : ZMod 1566225930287) ^ 285 = (5 : ZMod 1566225930287) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 142 * (5 : ZMod 1566225930287) ^ 142) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 710118605334 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 1566225930287) ^ 571 = 1430117191476 := by
        calc
          (5 : ZMod 1566225930287) ^ 571 = (5 : ZMod 1566225930287) ^ (285 + 285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 285 * (5 : ZMod 1566225930287) ^ 285) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1430117191476 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 1566225930287) ^ 1143 = 812900295784 := by
        calc
          (5 : ZMod 1566225930287) ^ 1143 = (5 : ZMod 1566225930287) ^ (571 + 571 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 571 * (5 : ZMod 1566225930287) ^ 571) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 812900295784 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 1566225930287) ^ 2286 = 190753750258 := by
        calc
          (5 : ZMod 1566225930287) ^ 2286 = (5 : ZMod 1566225930287) ^ (1143 + 1143) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1143 * (5 : ZMod 1566225930287) ^ 1143 := by rw [pow_add]
          _ = 190753750258 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 1566225930287) ^ 4572 = 1048080337873 := by
        calc
          (5 : ZMod 1566225930287) ^ 4572 = (5 : ZMod 1566225930287) ^ (2286 + 2286) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 2286 * (5 : ZMod 1566225930287) ^ 2286 := by rw [pow_add]
          _ = 1048080337873 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 1566225930287) ^ 9145 = 608105064384 := by
        calc
          (5 : ZMod 1566225930287) ^ 9145 = (5 : ZMod 1566225930287) ^ (4572 + 4572 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 4572 * (5 : ZMod 1566225930287) ^ 4572) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 608105064384 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 1566225930287) ^ 18291 = 135728618452 := by
        calc
          (5 : ZMod 1566225930287) ^ 18291 = (5 : ZMod 1566225930287) ^ (9145 + 9145 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 9145 * (5 : ZMod 1566225930287) ^ 9145) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 135728618452 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 1566225930287) ^ 36583 = 388909722243 := by
        calc
          (5 : ZMod 1566225930287) ^ 36583 = (5 : ZMod 1566225930287) ^ (18291 + 18291 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 18291 * (5 : ZMod 1566225930287) ^ 18291) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 388909722243 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 1566225930287) ^ 73166 = 956703854039 := by
        calc
          (5 : ZMod 1566225930287) ^ 73166 = (5 : ZMod 1566225930287) ^ (36583 + 36583) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 36583 * (5 : ZMod 1566225930287) ^ 36583 := by rw [pow_add]
          _ = 956703854039 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 1566225930287) ^ 146333 = 1231537091427 := by
        calc
          (5 : ZMod 1566225930287) ^ 146333 = (5 : ZMod 1566225930287) ^ (73166 + 73166 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 73166 * (5 : ZMod 1566225930287) ^ 73166) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1231537091427 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 1566225930287) ^ 292667 = 678943551758 := by
        calc
          (5 : ZMod 1566225930287) ^ 292667 = (5 : ZMod 1566225930287) ^ (146333 + 146333 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 146333 * (5 : ZMod 1566225930287) ^ 146333) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 678943551758 := by rw [factor_4_17]; decide
      have factor_4_19 : (5 : ZMod 1566225930287) ^ 585335 = 903066812051 := by
        calc
          (5 : ZMod 1566225930287) ^ 585335 = (5 : ZMod 1566225930287) ^ (292667 + 292667 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 292667 * (5 : ZMod 1566225930287) ^ 292667) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 903066812051 := by rw [factor_4_18]; decide
      have factor_4_20 : (5 : ZMod 1566225930287) ^ 1170670 = 1404672433182 := by
        calc
          (5 : ZMod 1566225930287) ^ 1170670 = (5 : ZMod 1566225930287) ^ (585335 + 585335) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 585335 * (5 : ZMod 1566225930287) ^ 585335 := by rw [pow_add]
          _ = 1404672433182 := by rw [factor_4_19]; decide
      have factor_4_21 : (5 : ZMod 1566225930287) ^ 2341340 = 1093495599958 := by
        calc
          (5 : ZMod 1566225930287) ^ 2341340 = (5 : ZMod 1566225930287) ^ (1170670 + 1170670) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 1170670 * (5 : ZMod 1566225930287) ^ 1170670 := by rw [pow_add]
          _ = 1093495599958 := by rw [factor_4_20]; decide
      have factor_4_22 : (5 : ZMod 1566225930287) ^ 4682681 = 1338500264526 := by
        calc
          (5 : ZMod 1566225930287) ^ 4682681 = (5 : ZMod 1566225930287) ^ (2341340 + 2341340 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 2341340 * (5 : ZMod 1566225930287) ^ 2341340) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1338500264526 := by rw [factor_4_21]; decide
      have factor_4_23 : (5 : ZMod 1566225930287) ^ 9365363 = 1222182051600 := by
        calc
          (5 : ZMod 1566225930287) ^ 9365363 = (5 : ZMod 1566225930287) ^ (4682681 + 4682681 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 4682681 * (5 : ZMod 1566225930287) ^ 4682681) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 1222182051600 := by rw [factor_4_22]; decide
      have factor_4_24 : (5 : ZMod 1566225930287) ^ 18730727 = 927003432147 := by
        calc
          (5 : ZMod 1566225930287) ^ 18730727 = (5 : ZMod 1566225930287) ^ (9365363 + 9365363 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = ((5 : ZMod 1566225930287) ^ 9365363 * (5 : ZMod 1566225930287) ^ 9365363) * (5 : ZMod 1566225930287) := by rw [pow_succ, pow_add]
          _ = 927003432147 := by rw [factor_4_23]; decide
      have factor_4_25 : (5 : ZMod 1566225930287) ^ 37461454 = 974120610141 := by
        calc
          (5 : ZMod 1566225930287) ^ 37461454 = (5 : ZMod 1566225930287) ^ (18730727 + 18730727) :=
            congrArg (fun n : ℕ => (5 : ZMod 1566225930287) ^ n) (by norm_num)
          _ = (5 : ZMod 1566225930287) ^ 18730727 * (5 : ZMod 1566225930287) ^ 18730727 := by rw [pow_add]
          _ = 974120610141 := by rw [factor_4_24]; decide
      change (5 : ZMod 1566225930287) ^ 37461454 ≠ 1
      rw [factor_4_25]
      decide

#print axioms prime_lucas_1566225930287

end TotientTailPeriodKiller
end Erdos249257
