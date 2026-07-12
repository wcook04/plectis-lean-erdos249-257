import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_665454160801 : Nat.Prime 665454160801 := by
  apply lucas_primality 665454160801 (7 : ZMod 665454160801)
  ·
      have fermat_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 665454160801) ^ 2 = 49 := by
        calc
          (7 : ZMod 665454160801) ^ 2 = (7 : ZMod 665454160801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 665454160801) ^ 4 = 2401 := by
        calc
          (7 : ZMod 665454160801) ^ 4 = (7 : ZMod 665454160801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2 * (7 : ZMod 665454160801) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 665454160801) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 665454160801) ^ 9 = (7 : ZMod 665454160801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 4 * (7 : ZMod 665454160801) ^ 4) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 665454160801) ^ 19 = 330865012814 := by
        calc
          (7 : ZMod 665454160801) ^ 19 = (7 : ZMod 665454160801) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 9 * (7 : ZMod 665454160801) ^ 9) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 330865012814 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 665454160801) ^ 38 = 527263809163 := by
        calc
          (7 : ZMod 665454160801) ^ 38 = (7 : ZMod 665454160801) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 19 * (7 : ZMod 665454160801) ^ 19 := by rw [pow_add]
          _ = 527263809163 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 665454160801) ^ 77 = 11653271484 := by
        calc
          (7 : ZMod 665454160801) ^ 77 = (7 : ZMod 665454160801) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 38 * (7 : ZMod 665454160801) ^ 38) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 11653271484 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 665454160801) ^ 154 = 117588967399 := by
        calc
          (7 : ZMod 665454160801) ^ 154 = (7 : ZMod 665454160801) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 77 * (7 : ZMod 665454160801) ^ 77 := by rw [pow_add]
          _ = 117588967399 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 665454160801) ^ 309 = 265276066386 := by
        calc
          (7 : ZMod 665454160801) ^ 309 = (7 : ZMod 665454160801) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 154 * (7 : ZMod 665454160801) ^ 154) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 265276066386 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 665454160801) ^ 619 = 387463541288 := by
        calc
          (7 : ZMod 665454160801) ^ 619 = (7 : ZMod 665454160801) ^ (309 + 309 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 309 * (7 : ZMod 665454160801) ^ 309) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 387463541288 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 665454160801) ^ 1239 = 60580570317 := by
        calc
          (7 : ZMod 665454160801) ^ 1239 = (7 : ZMod 665454160801) ^ (619 + 619 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 619 * (7 : ZMod 665454160801) ^ 619) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 60580570317 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 665454160801) ^ 2479 = 247215791197 := by
        calc
          (7 : ZMod 665454160801) ^ 2479 = (7 : ZMod 665454160801) ^ (1239 + 1239 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1239 * (7 : ZMod 665454160801) ^ 1239) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 247215791197 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 665454160801) ^ 4958 = 426189901954 := by
        calc
          (7 : ZMod 665454160801) ^ 4958 = (7 : ZMod 665454160801) ^ (2479 + 2479) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2479 * (7 : ZMod 665454160801) ^ 2479 := by rw [pow_add]
          _ = 426189901954 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 665454160801) ^ 9916 = 512226475719 := by
        calc
          (7 : ZMod 665454160801) ^ 9916 = (7 : ZMod 665454160801) ^ (4958 + 4958) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4958 * (7 : ZMod 665454160801) ^ 4958 := by rw [pow_add]
          _ = 512226475719 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 665454160801) ^ 19832 = 214908991599 := by
        calc
          (7 : ZMod 665454160801) ^ 19832 = (7 : ZMod 665454160801) ^ (9916 + 9916) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 9916 * (7 : ZMod 665454160801) ^ 9916 := by rw [pow_add]
          _ = 214908991599 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 665454160801) ^ 39664 = 554929184164 := by
        calc
          (7 : ZMod 665454160801) ^ 39664 = (7 : ZMod 665454160801) ^ (19832 + 19832) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 19832 * (7 : ZMod 665454160801) ^ 19832 := by rw [pow_add]
          _ = 554929184164 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 665454160801) ^ 79328 = 587326928646 := by
        calc
          (7 : ZMod 665454160801) ^ 79328 = (7 : ZMod 665454160801) ^ (39664 + 39664) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 39664 * (7 : ZMod 665454160801) ^ 39664 := by rw [pow_add]
          _ = 587326928646 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 665454160801) ^ 158656 = 286066878492 := by
        calc
          (7 : ZMod 665454160801) ^ 158656 = (7 : ZMod 665454160801) ^ (79328 + 79328) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 79328 * (7 : ZMod 665454160801) ^ 79328 := by rw [pow_add]
          _ = 286066878492 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 665454160801) ^ 317313 = 100844348777 := by
        calc
          (7 : ZMod 665454160801) ^ 317313 = (7 : ZMod 665454160801) ^ (158656 + 158656 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 158656 * (7 : ZMod 665454160801) ^ 158656) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 100844348777 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 665454160801) ^ 634626 = 655736668731 := by
        calc
          (7 : ZMod 665454160801) ^ 634626 = (7 : ZMod 665454160801) ^ (317313 + 317313) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 317313 * (7 : ZMod 665454160801) ^ 317313 := by rw [pow_add]
          _ = 655736668731 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 665454160801) ^ 1269253 = 91408033947 := by
        calc
          (7 : ZMod 665454160801) ^ 1269253 = (7 : ZMod 665454160801) ^ (634626 + 634626 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 634626 * (7 : ZMod 665454160801) ^ 634626) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 91408033947 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 665454160801) ^ 2538506 = 608768657907 := by
        calc
          (7 : ZMod 665454160801) ^ 2538506 = (7 : ZMod 665454160801) ^ (1269253 + 1269253) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1269253 * (7 : ZMod 665454160801) ^ 1269253 := by rw [pow_add]
          _ = 608768657907 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 665454160801) ^ 5077012 = 623605076527 := by
        calc
          (7 : ZMod 665454160801) ^ 5077012 = (7 : ZMod 665454160801) ^ (2538506 + 2538506) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2538506 * (7 : ZMod 665454160801) ^ 2538506 := by rw [pow_add]
          _ = 623605076527 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 665454160801) ^ 10154024 = 58359820875 := by
        calc
          (7 : ZMod 665454160801) ^ 10154024 = (7 : ZMod 665454160801) ^ (5077012 + 5077012) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 5077012 * (7 : ZMod 665454160801) ^ 5077012 := by rw [pow_add]
          _ = 58359820875 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 665454160801) ^ 20308049 = 40416981029 := by
        calc
          (7 : ZMod 665454160801) ^ 20308049 = (7 : ZMod 665454160801) ^ (10154024 + 10154024 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 10154024 * (7 : ZMod 665454160801) ^ 10154024) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 40416981029 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 665454160801) ^ 40616098 = 222805811686 := by
        calc
          (7 : ZMod 665454160801) ^ 40616098 = (7 : ZMod 665454160801) ^ (20308049 + 20308049) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 20308049 * (7 : ZMod 665454160801) ^ 20308049 := by rw [pow_add]
          _ = 222805811686 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 665454160801) ^ 81232197 = 317147564479 := by
        calc
          (7 : ZMod 665454160801) ^ 81232197 = (7 : ZMod 665454160801) ^ (40616098 + 40616098 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 40616098 * (7 : ZMod 665454160801) ^ 40616098) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 317147564479 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 665454160801) ^ 162464394 = 67958142204 := by
        calc
          (7 : ZMod 665454160801) ^ 162464394 = (7 : ZMod 665454160801) ^ (81232197 + 81232197) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 81232197 * (7 : ZMod 665454160801) ^ 81232197 := by rw [pow_add]
          _ = 67958142204 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 665454160801) ^ 324928789 = 114347992651 := by
        calc
          (7 : ZMod 665454160801) ^ 324928789 = (7 : ZMod 665454160801) ^ (162464394 + 162464394 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 162464394 * (7 : ZMod 665454160801) ^ 162464394) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 114347992651 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 665454160801) ^ 649857578 = 377159314399 := by
        calc
          (7 : ZMod 665454160801) ^ 649857578 = (7 : ZMod 665454160801) ^ (324928789 + 324928789) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 324928789 * (7 : ZMod 665454160801) ^ 324928789 := by rw [pow_add]
          _ = 377159314399 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 665454160801) ^ 1299715157 = 466206097951 := by
        calc
          (7 : ZMod 665454160801) ^ 1299715157 = (7 : ZMod 665454160801) ^ (649857578 + 649857578 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 649857578 * (7 : ZMod 665454160801) ^ 649857578) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 466206097951 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 665454160801) ^ 2599430315 = 143903952929 := by
        calc
          (7 : ZMod 665454160801) ^ 2599430315 = (7 : ZMod 665454160801) ^ (1299715157 + 1299715157 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1299715157 * (7 : ZMod 665454160801) ^ 1299715157) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 143903952929 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 665454160801) ^ 5198860631 = 130027092358 := by
        calc
          (7 : ZMod 665454160801) ^ 5198860631 = (7 : ZMod 665454160801) ^ (2599430315 + 2599430315 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 2599430315 * (7 : ZMod 665454160801) ^ 2599430315) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 130027092358 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 665454160801) ^ 10397721262 = 569569770647 := by
        calc
          (7 : ZMod 665454160801) ^ 10397721262 = (7 : ZMod 665454160801) ^ (5198860631 + 5198860631) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 5198860631 * (7 : ZMod 665454160801) ^ 5198860631 := by rw [pow_add]
          _ = 569569770647 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 665454160801) ^ 20795442525 = 534215075605 := by
        calc
          (7 : ZMod 665454160801) ^ 20795442525 = (7 : ZMod 665454160801) ^ (10397721262 + 10397721262 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 10397721262 * (7 : ZMod 665454160801) ^ 10397721262) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 534215075605 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 665454160801) ^ 41590885050 = 219220483548 := by
        calc
          (7 : ZMod 665454160801) ^ 41590885050 = (7 : ZMod 665454160801) ^ (20795442525 + 20795442525) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 20795442525 * (7 : ZMod 665454160801) ^ 20795442525 := by rw [pow_add]
          _ = 219220483548 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 665454160801) ^ 83181770100 = 301214548576 := by
        calc
          (7 : ZMod 665454160801) ^ 83181770100 = (7 : ZMod 665454160801) ^ (41590885050 + 41590885050) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 41590885050 * (7 : ZMod 665454160801) ^ 41590885050 := by rw [pow_add]
          _ = 301214548576 := by rw [fermat_35]; decide
      have fermat_37 : (7 : ZMod 665454160801) ^ 166363540200 = 290266142622 := by
        calc
          (7 : ZMod 665454160801) ^ 166363540200 = (7 : ZMod 665454160801) ^ (83181770100 + 83181770100) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 83181770100 * (7 : ZMod 665454160801) ^ 83181770100 := by rw [pow_add]
          _ = 290266142622 := by rw [fermat_36]; decide
      have fermat_38 : (7 : ZMod 665454160801) ^ 332727080400 = 665454160800 := by
        calc
          (7 : ZMod 665454160801) ^ 332727080400 = (7 : ZMod 665454160801) ^ (166363540200 + 166363540200) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 166363540200 * (7 : ZMod 665454160801) ^ 166363540200 := by rw [pow_add]
          _ = 665454160800 := by rw [fermat_37]; decide
      have fermat_39 : (7 : ZMod 665454160801) ^ 665454160800 = 1 := by
        calc
          (7 : ZMod 665454160801) ^ 665454160800 = (7 : ZMod 665454160801) ^ (332727080400 + 332727080400) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 332727080400 * (7 : ZMod 665454160801) ^ 332727080400 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 665454160801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 665454160801) ^ 2 = 49 := by
        calc
          (7 : ZMod 665454160801) ^ 2 = (7 : ZMod 665454160801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 665454160801) ^ 4 = 2401 := by
        calc
          (7 : ZMod 665454160801) ^ 4 = (7 : ZMod 665454160801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2 * (7 : ZMod 665454160801) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 665454160801) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 665454160801) ^ 9 = (7 : ZMod 665454160801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 4 * (7 : ZMod 665454160801) ^ 4) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 665454160801) ^ 19 = 330865012814 := by
        calc
          (7 : ZMod 665454160801) ^ 19 = (7 : ZMod 665454160801) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 9 * (7 : ZMod 665454160801) ^ 9) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 330865012814 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 665454160801) ^ 38 = 527263809163 := by
        calc
          (7 : ZMod 665454160801) ^ 38 = (7 : ZMod 665454160801) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 19 * (7 : ZMod 665454160801) ^ 19 := by rw [pow_add]
          _ = 527263809163 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 665454160801) ^ 77 = 11653271484 := by
        calc
          (7 : ZMod 665454160801) ^ 77 = (7 : ZMod 665454160801) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 38 * (7 : ZMod 665454160801) ^ 38) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 11653271484 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 665454160801) ^ 154 = 117588967399 := by
        calc
          (7 : ZMod 665454160801) ^ 154 = (7 : ZMod 665454160801) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 77 * (7 : ZMod 665454160801) ^ 77 := by rw [pow_add]
          _ = 117588967399 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 665454160801) ^ 309 = 265276066386 := by
        calc
          (7 : ZMod 665454160801) ^ 309 = (7 : ZMod 665454160801) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 154 * (7 : ZMod 665454160801) ^ 154) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 265276066386 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 665454160801) ^ 619 = 387463541288 := by
        calc
          (7 : ZMod 665454160801) ^ 619 = (7 : ZMod 665454160801) ^ (309 + 309 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 309 * (7 : ZMod 665454160801) ^ 309) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 387463541288 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 665454160801) ^ 1239 = 60580570317 := by
        calc
          (7 : ZMod 665454160801) ^ 1239 = (7 : ZMod 665454160801) ^ (619 + 619 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 619 * (7 : ZMod 665454160801) ^ 619) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 60580570317 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 665454160801) ^ 2479 = 247215791197 := by
        calc
          (7 : ZMod 665454160801) ^ 2479 = (7 : ZMod 665454160801) ^ (1239 + 1239 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1239 * (7 : ZMod 665454160801) ^ 1239) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 247215791197 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 665454160801) ^ 4958 = 426189901954 := by
        calc
          (7 : ZMod 665454160801) ^ 4958 = (7 : ZMod 665454160801) ^ (2479 + 2479) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2479 * (7 : ZMod 665454160801) ^ 2479 := by rw [pow_add]
          _ = 426189901954 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 665454160801) ^ 9916 = 512226475719 := by
        calc
          (7 : ZMod 665454160801) ^ 9916 = (7 : ZMod 665454160801) ^ (4958 + 4958) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4958 * (7 : ZMod 665454160801) ^ 4958 := by rw [pow_add]
          _ = 512226475719 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 665454160801) ^ 19832 = 214908991599 := by
        calc
          (7 : ZMod 665454160801) ^ 19832 = (7 : ZMod 665454160801) ^ (9916 + 9916) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 9916 * (7 : ZMod 665454160801) ^ 9916 := by rw [pow_add]
          _ = 214908991599 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 665454160801) ^ 39664 = 554929184164 := by
        calc
          (7 : ZMod 665454160801) ^ 39664 = (7 : ZMod 665454160801) ^ (19832 + 19832) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 19832 * (7 : ZMod 665454160801) ^ 19832 := by rw [pow_add]
          _ = 554929184164 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 665454160801) ^ 79328 = 587326928646 := by
        calc
          (7 : ZMod 665454160801) ^ 79328 = (7 : ZMod 665454160801) ^ (39664 + 39664) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 39664 * (7 : ZMod 665454160801) ^ 39664 := by rw [pow_add]
          _ = 587326928646 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 665454160801) ^ 158656 = 286066878492 := by
        calc
          (7 : ZMod 665454160801) ^ 158656 = (7 : ZMod 665454160801) ^ (79328 + 79328) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 79328 * (7 : ZMod 665454160801) ^ 79328 := by rw [pow_add]
          _ = 286066878492 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 665454160801) ^ 317313 = 100844348777 := by
        calc
          (7 : ZMod 665454160801) ^ 317313 = (7 : ZMod 665454160801) ^ (158656 + 158656 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 158656 * (7 : ZMod 665454160801) ^ 158656) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 100844348777 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 665454160801) ^ 634626 = 655736668731 := by
        calc
          (7 : ZMod 665454160801) ^ 634626 = (7 : ZMod 665454160801) ^ (317313 + 317313) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 317313 * (7 : ZMod 665454160801) ^ 317313 := by rw [pow_add]
          _ = 655736668731 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 665454160801) ^ 1269253 = 91408033947 := by
        calc
          (7 : ZMod 665454160801) ^ 1269253 = (7 : ZMod 665454160801) ^ (634626 + 634626 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 634626 * (7 : ZMod 665454160801) ^ 634626) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 91408033947 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 665454160801) ^ 2538506 = 608768657907 := by
        calc
          (7 : ZMod 665454160801) ^ 2538506 = (7 : ZMod 665454160801) ^ (1269253 + 1269253) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1269253 * (7 : ZMod 665454160801) ^ 1269253 := by rw [pow_add]
          _ = 608768657907 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 665454160801) ^ 5077012 = 623605076527 := by
        calc
          (7 : ZMod 665454160801) ^ 5077012 = (7 : ZMod 665454160801) ^ (2538506 + 2538506) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2538506 * (7 : ZMod 665454160801) ^ 2538506 := by rw [pow_add]
          _ = 623605076527 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 665454160801) ^ 10154024 = 58359820875 := by
        calc
          (7 : ZMod 665454160801) ^ 10154024 = (7 : ZMod 665454160801) ^ (5077012 + 5077012) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 5077012 * (7 : ZMod 665454160801) ^ 5077012 := by rw [pow_add]
          _ = 58359820875 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 665454160801) ^ 20308049 = 40416981029 := by
        calc
          (7 : ZMod 665454160801) ^ 20308049 = (7 : ZMod 665454160801) ^ (10154024 + 10154024 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 10154024 * (7 : ZMod 665454160801) ^ 10154024) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 40416981029 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 665454160801) ^ 40616098 = 222805811686 := by
        calc
          (7 : ZMod 665454160801) ^ 40616098 = (7 : ZMod 665454160801) ^ (20308049 + 20308049) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 20308049 * (7 : ZMod 665454160801) ^ 20308049 := by rw [pow_add]
          _ = 222805811686 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 665454160801) ^ 81232197 = 317147564479 := by
        calc
          (7 : ZMod 665454160801) ^ 81232197 = (7 : ZMod 665454160801) ^ (40616098 + 40616098 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 40616098 * (7 : ZMod 665454160801) ^ 40616098) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 317147564479 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 665454160801) ^ 162464394 = 67958142204 := by
        calc
          (7 : ZMod 665454160801) ^ 162464394 = (7 : ZMod 665454160801) ^ (81232197 + 81232197) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 81232197 * (7 : ZMod 665454160801) ^ 81232197 := by rw [pow_add]
          _ = 67958142204 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 665454160801) ^ 324928789 = 114347992651 := by
        calc
          (7 : ZMod 665454160801) ^ 324928789 = (7 : ZMod 665454160801) ^ (162464394 + 162464394 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 162464394 * (7 : ZMod 665454160801) ^ 162464394) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 114347992651 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 665454160801) ^ 649857578 = 377159314399 := by
        calc
          (7 : ZMod 665454160801) ^ 649857578 = (7 : ZMod 665454160801) ^ (324928789 + 324928789) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 324928789 * (7 : ZMod 665454160801) ^ 324928789 := by rw [pow_add]
          _ = 377159314399 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 665454160801) ^ 1299715157 = 466206097951 := by
        calc
          (7 : ZMod 665454160801) ^ 1299715157 = (7 : ZMod 665454160801) ^ (649857578 + 649857578 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 649857578 * (7 : ZMod 665454160801) ^ 649857578) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 466206097951 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 665454160801) ^ 2599430315 = 143903952929 := by
        calc
          (7 : ZMod 665454160801) ^ 2599430315 = (7 : ZMod 665454160801) ^ (1299715157 + 1299715157 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1299715157 * (7 : ZMod 665454160801) ^ 1299715157) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 143903952929 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 665454160801) ^ 5198860631 = 130027092358 := by
        calc
          (7 : ZMod 665454160801) ^ 5198860631 = (7 : ZMod 665454160801) ^ (2599430315 + 2599430315 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 2599430315 * (7 : ZMod 665454160801) ^ 2599430315) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 130027092358 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 665454160801) ^ 10397721262 = 569569770647 := by
        calc
          (7 : ZMod 665454160801) ^ 10397721262 = (7 : ZMod 665454160801) ^ (5198860631 + 5198860631) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 5198860631 * (7 : ZMod 665454160801) ^ 5198860631 := by rw [pow_add]
          _ = 569569770647 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 665454160801) ^ 20795442525 = 534215075605 := by
        calc
          (7 : ZMod 665454160801) ^ 20795442525 = (7 : ZMod 665454160801) ^ (10397721262 + 10397721262 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 10397721262 * (7 : ZMod 665454160801) ^ 10397721262) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 534215075605 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 665454160801) ^ 41590885050 = 219220483548 := by
        calc
          (7 : ZMod 665454160801) ^ 41590885050 = (7 : ZMod 665454160801) ^ (20795442525 + 20795442525) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 20795442525 * (7 : ZMod 665454160801) ^ 20795442525 := by rw [pow_add]
          _ = 219220483548 := by rw [factor_0_34]; decide
      have factor_0_36 : (7 : ZMod 665454160801) ^ 83181770100 = 301214548576 := by
        calc
          (7 : ZMod 665454160801) ^ 83181770100 = (7 : ZMod 665454160801) ^ (41590885050 + 41590885050) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 41590885050 * (7 : ZMod 665454160801) ^ 41590885050 := by rw [pow_add]
          _ = 301214548576 := by rw [factor_0_35]; decide
      have factor_0_37 : (7 : ZMod 665454160801) ^ 166363540200 = 290266142622 := by
        calc
          (7 : ZMod 665454160801) ^ 166363540200 = (7 : ZMod 665454160801) ^ (83181770100 + 83181770100) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 83181770100 * (7 : ZMod 665454160801) ^ 83181770100 := by rw [pow_add]
          _ = 290266142622 := by rw [factor_0_36]; decide
      have factor_0_38 : (7 : ZMod 665454160801) ^ 332727080400 = 665454160800 := by
        calc
          (7 : ZMod 665454160801) ^ 332727080400 = (7 : ZMod 665454160801) ^ (166363540200 + 166363540200) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 166363540200 * (7 : ZMod 665454160801) ^ 166363540200 := by rw [pow_add]
          _ = 665454160800 := by rw [factor_0_37]; decide
      change (7 : ZMod 665454160801) ^ 332727080400 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 665454160801) ^ 3 = 343 := by
        calc
          (7 : ZMod 665454160801) ^ 3 = (7 : ZMod 665454160801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 665454160801) ^ 6 = 117649 := by
        calc
          (7 : ZMod 665454160801) ^ 6 = (7 : ZMod 665454160801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3 * (7 : ZMod 665454160801) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 665454160801) ^ 12 = 13841287201 := by
        calc
          (7 : ZMod 665454160801) ^ 12 = (7 : ZMod 665454160801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 6 * (7 : ZMod 665454160801) ^ 6 := by rw [pow_add]
          _ = 13841287201 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 665454160801) ^ 25 = 196756499791 := by
        calc
          (7 : ZMod 665454160801) ^ 25 = (7 : ZMod 665454160801) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 12 * (7 : ZMod 665454160801) ^ 12) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 196756499791 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 665454160801) ^ 51 = 151326842904 := by
        calc
          (7 : ZMod 665454160801) ^ 51 = (7 : ZMod 665454160801) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 25 * (7 : ZMod 665454160801) ^ 25) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 151326842904 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 665454160801) ^ 103 = 134764528575 := by
        calc
          (7 : ZMod 665454160801) ^ 103 = (7 : ZMod 665454160801) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 51 * (7 : ZMod 665454160801) ^ 51) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 134764528575 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 665454160801) ^ 206 = 426967161682 := by
        calc
          (7 : ZMod 665454160801) ^ 206 = (7 : ZMod 665454160801) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 103 * (7 : ZMod 665454160801) ^ 103 := by rw [pow_add]
          _ = 426967161682 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 665454160801) ^ 413 = 488296484555 := by
        calc
          (7 : ZMod 665454160801) ^ 413 = (7 : ZMod 665454160801) ^ (206 + 206 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 206 * (7 : ZMod 665454160801) ^ 206) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 488296484555 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 665454160801) ^ 826 = 102800190140 := by
        calc
          (7 : ZMod 665454160801) ^ 826 = (7 : ZMod 665454160801) ^ (413 + 413) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 413 * (7 : ZMod 665454160801) ^ 413 := by rw [pow_add]
          _ = 102800190140 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 665454160801) ^ 1652 = 242952273795 := by
        calc
          (7 : ZMod 665454160801) ^ 1652 = (7 : ZMod 665454160801) ^ (826 + 826) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 826 * (7 : ZMod 665454160801) ^ 826 := by rw [pow_add]
          _ = 242952273795 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 665454160801) ^ 3305 = 30525608499 := by
        calc
          (7 : ZMod 665454160801) ^ 3305 = (7 : ZMod 665454160801) ^ (1652 + 1652 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1652 * (7 : ZMod 665454160801) ^ 1652) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 30525608499 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 665454160801) ^ 6610 = 193284921494 := by
        calc
          (7 : ZMod 665454160801) ^ 6610 = (7 : ZMod 665454160801) ^ (3305 + 3305) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3305 * (7 : ZMod 665454160801) ^ 3305 := by rw [pow_add]
          _ = 193284921494 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 665454160801) ^ 13221 = 133840641929 := by
        calc
          (7 : ZMod 665454160801) ^ 13221 = (7 : ZMod 665454160801) ^ (6610 + 6610 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 6610 * (7 : ZMod 665454160801) ^ 6610) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 133840641929 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 665454160801) ^ 26442 = 125202067443 := by
        calc
          (7 : ZMod 665454160801) ^ 26442 = (7 : ZMod 665454160801) ^ (13221 + 13221) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 13221 * (7 : ZMod 665454160801) ^ 13221 := by rw [pow_add]
          _ = 125202067443 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 665454160801) ^ 52885 = 455594869316 := by
        calc
          (7 : ZMod 665454160801) ^ 52885 = (7 : ZMod 665454160801) ^ (26442 + 26442 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 26442 * (7 : ZMod 665454160801) ^ 26442) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 455594869316 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 665454160801) ^ 105771 = 80334318332 := by
        calc
          (7 : ZMod 665454160801) ^ 105771 = (7 : ZMod 665454160801) ^ (52885 + 52885 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 52885 * (7 : ZMod 665454160801) ^ 52885) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 80334318332 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 665454160801) ^ 211542 = 558978938172 := by
        calc
          (7 : ZMod 665454160801) ^ 211542 = (7 : ZMod 665454160801) ^ (105771 + 105771) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 105771 * (7 : ZMod 665454160801) ^ 105771 := by rw [pow_add]
          _ = 558978938172 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 665454160801) ^ 423084 = 398527999707 := by
        calc
          (7 : ZMod 665454160801) ^ 423084 = (7 : ZMod 665454160801) ^ (211542 + 211542) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 211542 * (7 : ZMod 665454160801) ^ 211542 := by rw [pow_add]
          _ = 398527999707 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 665454160801) ^ 846168 = 69271320761 := by
        calc
          (7 : ZMod 665454160801) ^ 846168 = (7 : ZMod 665454160801) ^ (423084 + 423084) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 423084 * (7 : ZMod 665454160801) ^ 423084 := by rw [pow_add]
          _ = 69271320761 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 665454160801) ^ 1692337 = 288924865037 := by
        calc
          (7 : ZMod 665454160801) ^ 1692337 = (7 : ZMod 665454160801) ^ (846168 + 846168 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 846168 * (7 : ZMod 665454160801) ^ 846168) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 288924865037 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 665454160801) ^ 3384674 = 29774028390 := by
        calc
          (7 : ZMod 665454160801) ^ 3384674 = (7 : ZMod 665454160801) ^ (1692337 + 1692337) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1692337 * (7 : ZMod 665454160801) ^ 1692337 := by rw [pow_add]
          _ = 29774028390 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 665454160801) ^ 6769349 = 583802556082 := by
        calc
          (7 : ZMod 665454160801) ^ 6769349 = (7 : ZMod 665454160801) ^ (3384674 + 3384674 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 3384674 * (7 : ZMod 665454160801) ^ 3384674) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 583802556082 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 665454160801) ^ 13538699 = 566216770548 := by
        calc
          (7 : ZMod 665454160801) ^ 13538699 = (7 : ZMod 665454160801) ^ (6769349 + 6769349 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 6769349 * (7 : ZMod 665454160801) ^ 6769349) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 566216770548 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 665454160801) ^ 27077399 = 346971190462 := by
        calc
          (7 : ZMod 665454160801) ^ 27077399 = (7 : ZMod 665454160801) ^ (13538699 + 13538699 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 13538699 * (7 : ZMod 665454160801) ^ 13538699) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 346971190462 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 665454160801) ^ 54154798 = 120933465042 := by
        calc
          (7 : ZMod 665454160801) ^ 54154798 = (7 : ZMod 665454160801) ^ (27077399 + 27077399) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 27077399 * (7 : ZMod 665454160801) ^ 27077399 := by rw [pow_add]
          _ = 120933465042 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 665454160801) ^ 108309596 = 302783211859 := by
        calc
          (7 : ZMod 665454160801) ^ 108309596 = (7 : ZMod 665454160801) ^ (54154798 + 54154798) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 54154798 * (7 : ZMod 665454160801) ^ 54154798 := by rw [pow_add]
          _ = 302783211859 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 665454160801) ^ 216619192 = 373256236726 := by
        calc
          (7 : ZMod 665454160801) ^ 216619192 = (7 : ZMod 665454160801) ^ (108309596 + 108309596) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 108309596 * (7 : ZMod 665454160801) ^ 108309596 := by rw [pow_add]
          _ = 373256236726 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 665454160801) ^ 433238385 = 46952552397 := by
        calc
          (7 : ZMod 665454160801) ^ 433238385 = (7 : ZMod 665454160801) ^ (216619192 + 216619192 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 216619192 * (7 : ZMod 665454160801) ^ 216619192) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 46952552397 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 665454160801) ^ 866476771 = 438604263230 := by
        calc
          (7 : ZMod 665454160801) ^ 866476771 = (7 : ZMod 665454160801) ^ (433238385 + 433238385 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 433238385 * (7 : ZMod 665454160801) ^ 433238385) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 438604263230 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 665454160801) ^ 1732953543 = 451933684687 := by
        calc
          (7 : ZMod 665454160801) ^ 1732953543 = (7 : ZMod 665454160801) ^ (866476771 + 866476771 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 866476771 * (7 : ZMod 665454160801) ^ 866476771) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 451933684687 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 665454160801) ^ 3465907087 = 430407424006 := by
        calc
          (7 : ZMod 665454160801) ^ 3465907087 = (7 : ZMod 665454160801) ^ (1732953543 + 1732953543 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1732953543 * (7 : ZMod 665454160801) ^ 1732953543) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 430407424006 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 665454160801) ^ 6931814175 = 580933203225 := by
        calc
          (7 : ZMod 665454160801) ^ 6931814175 = (7 : ZMod 665454160801) ^ (3465907087 + 3465907087 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 3465907087 * (7 : ZMod 665454160801) ^ 3465907087) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 580933203225 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 665454160801) ^ 13863628350 = 498161329009 := by
        calc
          (7 : ZMod 665454160801) ^ 13863628350 = (7 : ZMod 665454160801) ^ (6931814175 + 6931814175) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 6931814175 * (7 : ZMod 665454160801) ^ 6931814175 := by rw [pow_add]
          _ = 498161329009 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 665454160801) ^ 27727256700 = 330993438684 := by
        calc
          (7 : ZMod 665454160801) ^ 27727256700 = (7 : ZMod 665454160801) ^ (13863628350 + 13863628350) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 13863628350 * (7 : ZMod 665454160801) ^ 13863628350 := by rw [pow_add]
          _ = 330993438684 := by rw [factor_1_33]; decide
      have factor_1_35 : (7 : ZMod 665454160801) ^ 55454513400 = 364834382488 := by
        calc
          (7 : ZMod 665454160801) ^ 55454513400 = (7 : ZMod 665454160801) ^ (27727256700 + 27727256700) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 27727256700 * (7 : ZMod 665454160801) ^ 27727256700 := by rw [pow_add]
          _ = 364834382488 := by rw [factor_1_34]; decide
      have factor_1_36 : (7 : ZMod 665454160801) ^ 110909026800 = 52186561681 := by
        calc
          (7 : ZMod 665454160801) ^ 110909026800 = (7 : ZMod 665454160801) ^ (55454513400 + 55454513400) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 55454513400 * (7 : ZMod 665454160801) ^ 55454513400 := by rw [pow_add]
          _ = 52186561681 := by rw [factor_1_35]; decide
      have factor_1_37 : (7 : ZMod 665454160801) ^ 221818053600 = 52186561680 := by
        calc
          (7 : ZMod 665454160801) ^ 221818053600 = (7 : ZMod 665454160801) ^ (110909026800 + 110909026800) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 110909026800 * (7 : ZMod 665454160801) ^ 110909026800 := by rw [pow_add]
          _ = 52186561680 := by rw [factor_1_36]; decide
      change (7 : ZMod 665454160801) ^ 221818053600 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 665454160801) ^ 3 = 343 := by
        calc
          (7 : ZMod 665454160801) ^ 3 = (7 : ZMod 665454160801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 665454160801) ^ 7 = 823543 := by
        calc
          (7 : ZMod 665454160801) ^ 7 = (7 : ZMod 665454160801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 3 * (7 : ZMod 665454160801) ^ 3) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 665454160801) ^ 15 = 89382384336 := by
        calc
          (7 : ZMod 665454160801) ^ 15 = (7 : ZMod 665454160801) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 7 * (7 : ZMod 665454160801) ^ 7) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 89382384336 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 665454160801) ^ 30 = 244766967168 := by
        calc
          (7 : ZMod 665454160801) ^ 30 = (7 : ZMod 665454160801) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 15 * (7 : ZMod 665454160801) ^ 15 := by rw [pow_add]
          _ = 244766967168 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 665454160801) ^ 61 = 109190518335 := by
        calc
          (7 : ZMod 665454160801) ^ 61 = (7 : ZMod 665454160801) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 30 * (7 : ZMod 665454160801) ^ 30) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 109190518335 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 665454160801) ^ 123 = 143232836210 := by
        calc
          (7 : ZMod 665454160801) ^ 123 = (7 : ZMod 665454160801) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 61 * (7 : ZMod 665454160801) ^ 61) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 143232836210 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 665454160801) ^ 247 = 101202535054 := by
        calc
          (7 : ZMod 665454160801) ^ 247 = (7 : ZMod 665454160801) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 123 * (7 : ZMod 665454160801) ^ 123) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 101202535054 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 665454160801) ^ 495 = 141769595824 := by
        calc
          (7 : ZMod 665454160801) ^ 495 = (7 : ZMod 665454160801) ^ (247 + 247 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 247 * (7 : ZMod 665454160801) ^ 247) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 141769595824 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 665454160801) ^ 991 = 658436569871 := by
        calc
          (7 : ZMod 665454160801) ^ 991 = (7 : ZMod 665454160801) ^ (495 + 495 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 495 * (7 : ZMod 665454160801) ^ 495) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 658436569871 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 665454160801) ^ 1983 = 535572551811 := by
        calc
          (7 : ZMod 665454160801) ^ 1983 = (7 : ZMod 665454160801) ^ (991 + 991 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 991 * (7 : ZMod 665454160801) ^ 991) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 535572551811 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 665454160801) ^ 3966 = 395470560518 := by
        calc
          (7 : ZMod 665454160801) ^ 3966 = (7 : ZMod 665454160801) ^ (1983 + 1983) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1983 * (7 : ZMod 665454160801) ^ 1983 := by rw [pow_add]
          _ = 395470560518 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 665454160801) ^ 7932 = 102340080009 := by
        calc
          (7 : ZMod 665454160801) ^ 7932 = (7 : ZMod 665454160801) ^ (3966 + 3966) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3966 * (7 : ZMod 665454160801) ^ 3966 := by rw [pow_add]
          _ = 102340080009 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 665454160801) ^ 15865 = 377170981646 := by
        calc
          (7 : ZMod 665454160801) ^ 15865 = (7 : ZMod 665454160801) ^ (7932 + 7932 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 7932 * (7 : ZMod 665454160801) ^ 7932) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 377170981646 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 665454160801) ^ 31731 = 214337977520 := by
        calc
          (7 : ZMod 665454160801) ^ 31731 = (7 : ZMod 665454160801) ^ (15865 + 15865 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 15865 * (7 : ZMod 665454160801) ^ 15865) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 214337977520 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 665454160801) ^ 63462 = 86302682758 := by
        calc
          (7 : ZMod 665454160801) ^ 63462 = (7 : ZMod 665454160801) ^ (31731 + 31731) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 31731 * (7 : ZMod 665454160801) ^ 31731 := by rw [pow_add]
          _ = 86302682758 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 665454160801) ^ 126925 = 126208230608 := by
        calc
          (7 : ZMod 665454160801) ^ 126925 = (7 : ZMod 665454160801) ^ (63462 + 63462 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 63462 * (7 : ZMod 665454160801) ^ 63462) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 126208230608 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 665454160801) ^ 253850 = 188839671079 := by
        calc
          (7 : ZMod 665454160801) ^ 253850 = (7 : ZMod 665454160801) ^ (126925 + 126925) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 126925 * (7 : ZMod 665454160801) ^ 126925 := by rw [pow_add]
          _ = 188839671079 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 665454160801) ^ 507701 = 4613166522 := by
        calc
          (7 : ZMod 665454160801) ^ 507701 = (7 : ZMod 665454160801) ^ (253850 + 253850 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 253850 * (7 : ZMod 665454160801) ^ 253850) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 4613166522 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 665454160801) ^ 1015402 = 111877978762 := by
        calc
          (7 : ZMod 665454160801) ^ 1015402 = (7 : ZMod 665454160801) ^ (507701 + 507701) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 507701 * (7 : ZMod 665454160801) ^ 507701 := by rw [pow_add]
          _ = 111877978762 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 665454160801) ^ 2030804 = 126732895989 := by
        calc
          (7 : ZMod 665454160801) ^ 2030804 = (7 : ZMod 665454160801) ^ (1015402 + 1015402) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1015402 * (7 : ZMod 665454160801) ^ 1015402 := by rw [pow_add]
          _ = 126732895989 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 665454160801) ^ 4061609 = 455239763333 := by
        calc
          (7 : ZMod 665454160801) ^ 4061609 = (7 : ZMod 665454160801) ^ (2030804 + 2030804 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 2030804 * (7 : ZMod 665454160801) ^ 2030804) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 455239763333 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 665454160801) ^ 8123219 = 594561080885 := by
        calc
          (7 : ZMod 665454160801) ^ 8123219 = (7 : ZMod 665454160801) ^ (4061609 + 4061609 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 4061609 * (7 : ZMod 665454160801) ^ 4061609) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 594561080885 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 665454160801) ^ 16246439 = 64683368635 := by
        calc
          (7 : ZMod 665454160801) ^ 16246439 = (7 : ZMod 665454160801) ^ (8123219 + 8123219 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 8123219 * (7 : ZMod 665454160801) ^ 8123219) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 64683368635 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 665454160801) ^ 32492878 = 208948319999 := by
        calc
          (7 : ZMod 665454160801) ^ 32492878 = (7 : ZMod 665454160801) ^ (16246439 + 16246439) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 16246439 * (7 : ZMod 665454160801) ^ 16246439 := by rw [pow_add]
          _ = 208948319999 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 665454160801) ^ 64985757 = 355981462167 := by
        calc
          (7 : ZMod 665454160801) ^ 64985757 = (7 : ZMod 665454160801) ^ (32492878 + 32492878 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 32492878 * (7 : ZMod 665454160801) ^ 32492878) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 355981462167 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 665454160801) ^ 129971515 = 483095683395 := by
        calc
          (7 : ZMod 665454160801) ^ 129971515 = (7 : ZMod 665454160801) ^ (64985757 + 64985757 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 64985757 * (7 : ZMod 665454160801) ^ 64985757) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 483095683395 := by rw [factor_2_25]; decide
      have factor_2_27 : (7 : ZMod 665454160801) ^ 259943031 = 157300574079 := by
        calc
          (7 : ZMod 665454160801) ^ 259943031 = (7 : ZMod 665454160801) ^ (129971515 + 129971515 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 129971515 * (7 : ZMod 665454160801) ^ 129971515) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 157300574079 := by rw [factor_2_26]; decide
      have factor_2_28 : (7 : ZMod 665454160801) ^ 519886063 = 75621392102 := by
        calc
          (7 : ZMod 665454160801) ^ 519886063 = (7 : ZMod 665454160801) ^ (259943031 + 259943031 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 259943031 * (7 : ZMod 665454160801) ^ 259943031) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 75621392102 := by rw [factor_2_27]; decide
      have factor_2_29 : (7 : ZMod 665454160801) ^ 1039772126 = 558571610046 := by
        calc
          (7 : ZMod 665454160801) ^ 1039772126 = (7 : ZMod 665454160801) ^ (519886063 + 519886063) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 519886063 * (7 : ZMod 665454160801) ^ 519886063 := by rw [pow_add]
          _ = 558571610046 := by rw [factor_2_28]; decide
      have factor_2_30 : (7 : ZMod 665454160801) ^ 2079544252 = 582431554233 := by
        calc
          (7 : ZMod 665454160801) ^ 2079544252 = (7 : ZMod 665454160801) ^ (1039772126 + 1039772126) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1039772126 * (7 : ZMod 665454160801) ^ 1039772126 := by rw [pow_add]
          _ = 582431554233 := by rw [factor_2_29]; decide
      have factor_2_31 : (7 : ZMod 665454160801) ^ 4159088505 = 579428161631 := by
        calc
          (7 : ZMod 665454160801) ^ 4159088505 = (7 : ZMod 665454160801) ^ (2079544252 + 2079544252 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 2079544252 * (7 : ZMod 665454160801) ^ 2079544252) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 579428161631 := by rw [factor_2_30]; decide
      have factor_2_32 : (7 : ZMod 665454160801) ^ 8318177010 = 234863995402 := by
        calc
          (7 : ZMod 665454160801) ^ 8318177010 = (7 : ZMod 665454160801) ^ (4159088505 + 4159088505) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4159088505 * (7 : ZMod 665454160801) ^ 4159088505 := by rw [pow_add]
          _ = 234863995402 := by rw [factor_2_31]; decide
      have factor_2_33 : (7 : ZMod 665454160801) ^ 16636354020 = 437548739008 := by
        calc
          (7 : ZMod 665454160801) ^ 16636354020 = (7 : ZMod 665454160801) ^ (8318177010 + 8318177010) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 8318177010 * (7 : ZMod 665454160801) ^ 8318177010 := by rw [pow_add]
          _ = 437548739008 := by rw [factor_2_32]; decide
      have factor_2_34 : (7 : ZMod 665454160801) ^ 33272708040 = 258719719232 := by
        calc
          (7 : ZMod 665454160801) ^ 33272708040 = (7 : ZMod 665454160801) ^ (16636354020 + 16636354020) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 16636354020 * (7 : ZMod 665454160801) ^ 16636354020 := by rw [pow_add]
          _ = 258719719232 := by rw [factor_2_33]; decide
      have factor_2_35 : (7 : ZMod 665454160801) ^ 66545416080 = 274803667049 := by
        calc
          (7 : ZMod 665454160801) ^ 66545416080 = (7 : ZMod 665454160801) ^ (33272708040 + 33272708040) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 33272708040 * (7 : ZMod 665454160801) ^ 33272708040 := by rw [pow_add]
          _ = 274803667049 := by rw [factor_2_34]; decide
      have factor_2_36 : (7 : ZMod 665454160801) ^ 133090832160 = 16129361717 := by
        calc
          (7 : ZMod 665454160801) ^ 133090832160 = (7 : ZMod 665454160801) ^ (66545416080 + 66545416080) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 66545416080 * (7 : ZMod 665454160801) ^ 66545416080 := by rw [pow_add]
          _ = 16129361717 := by rw [factor_2_35]; decide
      change (7 : ZMod 665454160801) ^ 133090832160 ≠ 1
      rw [factor_2_36]
      decide
    ·
      have factor_3_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 665454160801) ^ 3 = 343 := by
        calc
          (7 : ZMod 665454160801) ^ 3 = (7 : ZMod 665454160801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 665454160801) ^ 7 = 823543 := by
        calc
          (7 : ZMod 665454160801) ^ 7 = (7 : ZMod 665454160801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 3 * (7 : ZMod 665454160801) ^ 3) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 665454160801) ^ 14 = 12768912048 := by
        calc
          (7 : ZMod 665454160801) ^ 14 = (7 : ZMod 665454160801) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 7 * (7 : ZMod 665454160801) ^ 7 := by rw [pow_add]
          _ = 12768912048 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 665454160801) ^ 28 = 276609187412 := by
        calc
          (7 : ZMod 665454160801) ^ 28 = (7 : ZMod 665454160801) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 14 * (7 : ZMod 665454160801) ^ 14 := by rw [pow_add]
          _ = 276609187412 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 665454160801) ^ 56 = 649900266907 := by
        calc
          (7 : ZMod 665454160801) ^ 56 = (7 : ZMod 665454160801) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 28 * (7 : ZMod 665454160801) ^ 28 := by rw [pow_add]
          _ = 649900266907 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 665454160801) ^ 112 = 348945475810 := by
        calc
          (7 : ZMod 665454160801) ^ 112 = (7 : ZMod 665454160801) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 56 * (7 : ZMod 665454160801) ^ 56 := by rw [pow_add]
          _ = 348945475810 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 665454160801) ^ 225 = 590976919012 := by
        calc
          (7 : ZMod 665454160801) ^ 225 = (7 : ZMod 665454160801) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 112 * (7 : ZMod 665454160801) ^ 112) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 590976919012 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 665454160801) ^ 450 = 561002800633 := by
        calc
          (7 : ZMod 665454160801) ^ 450 = (7 : ZMod 665454160801) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 225 * (7 : ZMod 665454160801) ^ 225 := by rw [pow_add]
          _ = 561002800633 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 665454160801) ^ 901 = 485690977842 := by
        calc
          (7 : ZMod 665454160801) ^ 901 = (7 : ZMod 665454160801) ^ (450 + 450 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 450 * (7 : ZMod 665454160801) ^ 450) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 485690977842 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 665454160801) ^ 1802 = 284535393682 := by
        calc
          (7 : ZMod 665454160801) ^ 1802 = (7 : ZMod 665454160801) ^ (901 + 901) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 901 * (7 : ZMod 665454160801) ^ 901 := by rw [pow_add]
          _ = 284535393682 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 665454160801) ^ 3605 = 405582854327 := by
        calc
          (7 : ZMod 665454160801) ^ 3605 = (7 : ZMod 665454160801) ^ (1802 + 1802 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1802 * (7 : ZMod 665454160801) ^ 1802) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 405582854327 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 665454160801) ^ 7211 = 305798682267 := by
        calc
          (7 : ZMod 665454160801) ^ 7211 = (7 : ZMod 665454160801) ^ (3605 + 3605 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 3605 * (7 : ZMod 665454160801) ^ 3605) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 305798682267 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 665454160801) ^ 14423 = 193560055002 := by
        calc
          (7 : ZMod 665454160801) ^ 14423 = (7 : ZMod 665454160801) ^ (7211 + 7211 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 7211 * (7 : ZMod 665454160801) ^ 7211) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 193560055002 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 665454160801) ^ 28846 = 159725362782 := by
        calc
          (7 : ZMod 665454160801) ^ 28846 = (7 : ZMod 665454160801) ^ (14423 + 14423) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 14423 * (7 : ZMod 665454160801) ^ 14423 := by rw [pow_add]
          _ = 159725362782 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 665454160801) ^ 57693 = 293099409339 := by
        calc
          (7 : ZMod 665454160801) ^ 57693 = (7 : ZMod 665454160801) ^ (28846 + 28846 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 28846 * (7 : ZMod 665454160801) ^ 28846) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 293099409339 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 665454160801) ^ 115386 = 352642604968 := by
        calc
          (7 : ZMod 665454160801) ^ 115386 = (7 : ZMod 665454160801) ^ (57693 + 57693) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 57693 * (7 : ZMod 665454160801) ^ 57693 := by rw [pow_add]
          _ = 352642604968 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 665454160801) ^ 230773 = 653298317552 := by
        calc
          (7 : ZMod 665454160801) ^ 230773 = (7 : ZMod 665454160801) ^ (115386 + 115386 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 115386 * (7 : ZMod 665454160801) ^ 115386) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 653298317552 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 665454160801) ^ 461546 = 135917270157 := by
        calc
          (7 : ZMod 665454160801) ^ 461546 = (7 : ZMod 665454160801) ^ (230773 + 230773) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 230773 * (7 : ZMod 665454160801) ^ 230773 := by rw [pow_add]
          _ = 135917270157 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 665454160801) ^ 923093 = 400031968796 := by
        calc
          (7 : ZMod 665454160801) ^ 923093 = (7 : ZMod 665454160801) ^ (461546 + 461546 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 461546 * (7 : ZMod 665454160801) ^ 461546) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 400031968796 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 665454160801) ^ 1846186 = 392066406176 := by
        calc
          (7 : ZMod 665454160801) ^ 1846186 = (7 : ZMod 665454160801) ^ (923093 + 923093) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 923093 * (7 : ZMod 665454160801) ^ 923093 := by rw [pow_add]
          _ = 392066406176 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 665454160801) ^ 3692372 = 151087797523 := by
        calc
          (7 : ZMod 665454160801) ^ 3692372 = (7 : ZMod 665454160801) ^ (1846186 + 1846186) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1846186 * (7 : ZMod 665454160801) ^ 1846186 := by rw [pow_add]
          _ = 151087797523 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 665454160801) ^ 7384745 = 265961515058 := by
        calc
          (7 : ZMod 665454160801) ^ 7384745 = (7 : ZMod 665454160801) ^ (3692372 + 3692372 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 3692372 * (7 : ZMod 665454160801) ^ 3692372) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 265961515058 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 665454160801) ^ 14769490 = 165458965015 := by
        calc
          (7 : ZMod 665454160801) ^ 14769490 = (7 : ZMod 665454160801) ^ (7384745 + 7384745) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 7384745 * (7 : ZMod 665454160801) ^ 7384745 := by rw [pow_add]
          _ = 165458965015 := by rw [factor_3_22]; decide
      have factor_3_24 : (7 : ZMod 665454160801) ^ 29538980 = 146247980747 := by
        calc
          (7 : ZMod 665454160801) ^ 29538980 = (7 : ZMod 665454160801) ^ (14769490 + 14769490) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 14769490 * (7 : ZMod 665454160801) ^ 14769490 := by rw [pow_add]
          _ = 146247980747 := by rw [factor_3_23]; decide
      have factor_3_25 : (7 : ZMod 665454160801) ^ 59077961 = 267968155417 := by
        calc
          (7 : ZMod 665454160801) ^ 59077961 = (7 : ZMod 665454160801) ^ (29538980 + 29538980 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 29538980 * (7 : ZMod 665454160801) ^ 29538980) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 267968155417 := by rw [factor_3_24]; decide
      have factor_3_26 : (7 : ZMod 665454160801) ^ 118155923 = 445482143046 := by
        calc
          (7 : ZMod 665454160801) ^ 118155923 = (7 : ZMod 665454160801) ^ (59077961 + 59077961 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 59077961 * (7 : ZMod 665454160801) ^ 59077961) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 445482143046 := by rw [factor_3_25]; decide
      have factor_3_27 : (7 : ZMod 665454160801) ^ 236311846 = 59978399902 := by
        calc
          (7 : ZMod 665454160801) ^ 236311846 = (7 : ZMod 665454160801) ^ (118155923 + 118155923) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 118155923 * (7 : ZMod 665454160801) ^ 118155923 := by rw [pow_add]
          _ = 59978399902 := by rw [factor_3_26]; decide
      have factor_3_28 : (7 : ZMod 665454160801) ^ 472623693 = 16813939285 := by
        calc
          (7 : ZMod 665454160801) ^ 472623693 = (7 : ZMod 665454160801) ^ (236311846 + 236311846 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 236311846 * (7 : ZMod 665454160801) ^ 236311846) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 16813939285 := by rw [factor_3_27]; decide
      have factor_3_29 : (7 : ZMod 665454160801) ^ 945247387 = 80864223642 := by
        calc
          (7 : ZMod 665454160801) ^ 945247387 = (7 : ZMod 665454160801) ^ (472623693 + 472623693 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 472623693 * (7 : ZMod 665454160801) ^ 472623693) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 80864223642 := by rw [factor_3_28]; decide
      have factor_3_30 : (7 : ZMod 665454160801) ^ 1890494775 = 434895512929 := by
        calc
          (7 : ZMod 665454160801) ^ 1890494775 = (7 : ZMod 665454160801) ^ (945247387 + 945247387 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 945247387 * (7 : ZMod 665454160801) ^ 945247387) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 434895512929 := by rw [factor_3_29]; decide
      have factor_3_31 : (7 : ZMod 665454160801) ^ 3780989550 = 170223601350 := by
        calc
          (7 : ZMod 665454160801) ^ 3780989550 = (7 : ZMod 665454160801) ^ (1890494775 + 1890494775) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1890494775 * (7 : ZMod 665454160801) ^ 1890494775 := by rw [pow_add]
          _ = 170223601350 := by rw [factor_3_30]; decide
      have factor_3_32 : (7 : ZMod 665454160801) ^ 7561979100 = 385476391244 := by
        calc
          (7 : ZMod 665454160801) ^ 7561979100 = (7 : ZMod 665454160801) ^ (3780989550 + 3780989550) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3780989550 * (7 : ZMod 665454160801) ^ 3780989550 := by rw [pow_add]
          _ = 385476391244 := by rw [factor_3_31]; decide
      have factor_3_33 : (7 : ZMod 665454160801) ^ 15123958200 = 348537930553 := by
        calc
          (7 : ZMod 665454160801) ^ 15123958200 = (7 : ZMod 665454160801) ^ (7561979100 + 7561979100) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 7561979100 * (7 : ZMod 665454160801) ^ 7561979100 := by rw [pow_add]
          _ = 348537930553 := by rw [factor_3_32]; decide
      have factor_3_34 : (7 : ZMod 665454160801) ^ 30247916400 = 214695272152 := by
        calc
          (7 : ZMod 665454160801) ^ 30247916400 = (7 : ZMod 665454160801) ^ (15123958200 + 15123958200) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 15123958200 * (7 : ZMod 665454160801) ^ 15123958200 := by rw [pow_add]
          _ = 214695272152 := by rw [factor_3_33]; decide
      have factor_3_35 : (7 : ZMod 665454160801) ^ 60495832800 = 329010665985 := by
        calc
          (7 : ZMod 665454160801) ^ 60495832800 = (7 : ZMod 665454160801) ^ (30247916400 + 30247916400) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 30247916400 * (7 : ZMod 665454160801) ^ 30247916400 := by rw [pow_add]
          _ = 329010665985 := by rw [factor_3_34]; decide
      change (7 : ZMod 665454160801) ^ 60495832800 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 665454160801) ^ 2 = 49 := by
        calc
          (7 : ZMod 665454160801) ^ 2 = (7 : ZMod 665454160801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 665454160801) ^ 5 = 16807 := by
        calc
          (7 : ZMod 665454160801) ^ 5 = (7 : ZMod 665454160801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 2 * (7 : ZMod 665454160801) ^ 2) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 665454160801) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 665454160801) ^ 11 = (7 : ZMod 665454160801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 5 * (7 : ZMod 665454160801) ^ 5) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 665454160801) ^ 23 = 520081930821 := by
        calc
          (7 : ZMod 665454160801) ^ 23 = (7 : ZMod 665454160801) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 11 * (7 : ZMod 665454160801) ^ 11) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 520081930821 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 665454160801) ^ 47 = 108154289694 := by
        calc
          (7 : ZMod 665454160801) ^ 47 = (7 : ZMod 665454160801) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 23 * (7 : ZMod 665454160801) ^ 23) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 108154289694 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 665454160801) ^ 95 = 106124867930 := by
        calc
          (7 : ZMod 665454160801) ^ 95 = (7 : ZMod 665454160801) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 47 * (7 : ZMod 665454160801) ^ 47) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 106124867930 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 665454160801) ^ 190 = 441144215104 := by
        calc
          (7 : ZMod 665454160801) ^ 190 = (7 : ZMod 665454160801) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 95 * (7 : ZMod 665454160801) ^ 95 := by rw [pow_add]
          _ = 441144215104 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 665454160801) ^ 381 = 488459056454 := by
        calc
          (7 : ZMod 665454160801) ^ 381 = (7 : ZMod 665454160801) ^ (190 + 190 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 190 * (7 : ZMod 665454160801) ^ 190) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 488459056454 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 665454160801) ^ 762 = 327145790328 := by
        calc
          (7 : ZMod 665454160801) ^ 762 = (7 : ZMod 665454160801) ^ (381 + 381) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 381 * (7 : ZMod 665454160801) ^ 381 := by rw [pow_add]
          _ = 327145790328 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 665454160801) ^ 1525 = 90372481236 := by
        calc
          (7 : ZMod 665454160801) ^ 1525 = (7 : ZMod 665454160801) ^ (762 + 762 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 762 * (7 : ZMod 665454160801) ^ 762) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 90372481236 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 665454160801) ^ 3051 = 210543644484 := by
        calc
          (7 : ZMod 665454160801) ^ 3051 = (7 : ZMod 665454160801) ^ (1525 + 1525 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1525 * (7 : ZMod 665454160801) ^ 1525) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 210543644484 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 665454160801) ^ 6102 = 36177036737 := by
        calc
          (7 : ZMod 665454160801) ^ 6102 = (7 : ZMod 665454160801) ^ (3051 + 3051) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3051 * (7 : ZMod 665454160801) ^ 3051 := by rw [pow_add]
          _ = 36177036737 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 665454160801) ^ 12204 = 388941572756 := by
        calc
          (7 : ZMod 665454160801) ^ 12204 = (7 : ZMod 665454160801) ^ (6102 + 6102) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 6102 * (7 : ZMod 665454160801) ^ 6102 := by rw [pow_add]
          _ = 388941572756 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 665454160801) ^ 24408 = 378270986441 := by
        calc
          (7 : ZMod 665454160801) ^ 24408 = (7 : ZMod 665454160801) ^ (12204 + 12204) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 12204 * (7 : ZMod 665454160801) ^ 12204 := by rw [pow_add]
          _ = 378270986441 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 665454160801) ^ 48817 = 251588113809 := by
        calc
          (7 : ZMod 665454160801) ^ 48817 = (7 : ZMod 665454160801) ^ (24408 + 24408 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 24408 * (7 : ZMod 665454160801) ^ 24408) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 251588113809 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 665454160801) ^ 97634 = 507059769113 := by
        calc
          (7 : ZMod 665454160801) ^ 97634 = (7 : ZMod 665454160801) ^ (48817 + 48817) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 48817 * (7 : ZMod 665454160801) ^ 48817 := by rw [pow_add]
          _ = 507059769113 := by rw [factor_4_15]; decide
      have factor_4_17 : (7 : ZMod 665454160801) ^ 195269 = 563824921500 := by
        calc
          (7 : ZMod 665454160801) ^ 195269 = (7 : ZMod 665454160801) ^ (97634 + 97634 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 97634 * (7 : ZMod 665454160801) ^ 97634) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 563824921500 := by rw [factor_4_16]; decide
      have factor_4_18 : (7 : ZMod 665454160801) ^ 390539 = 567493014996 := by
        calc
          (7 : ZMod 665454160801) ^ 390539 = (7 : ZMod 665454160801) ^ (195269 + 195269 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 195269 * (7 : ZMod 665454160801) ^ 195269) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 567493014996 := by rw [factor_4_17]; decide
      have factor_4_19 : (7 : ZMod 665454160801) ^ 781078 = 624866610925 := by
        calc
          (7 : ZMod 665454160801) ^ 781078 = (7 : ZMod 665454160801) ^ (390539 + 390539) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 390539 * (7 : ZMod 665454160801) ^ 390539 := by rw [pow_add]
          _ = 624866610925 := by rw [factor_4_18]; decide
      have factor_4_20 : (7 : ZMod 665454160801) ^ 1562157 = 93364426685 := by
        calc
          (7 : ZMod 665454160801) ^ 1562157 = (7 : ZMod 665454160801) ^ (781078 + 781078 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 781078 * (7 : ZMod 665454160801) ^ 781078) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 93364426685 := by rw [factor_4_19]; decide
      have factor_4_21 : (7 : ZMod 665454160801) ^ 3124315 = 303302022810 := by
        calc
          (7 : ZMod 665454160801) ^ 3124315 = (7 : ZMod 665454160801) ^ (1562157 + 1562157 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1562157 * (7 : ZMod 665454160801) ^ 1562157) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 303302022810 := by rw [factor_4_20]; decide
      have factor_4_22 : (7 : ZMod 665454160801) ^ 6248630 = 564586816851 := by
        calc
          (7 : ZMod 665454160801) ^ 6248630 = (7 : ZMod 665454160801) ^ (3124315 + 3124315) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3124315 * (7 : ZMod 665454160801) ^ 3124315 := by rw [pow_add]
          _ = 564586816851 := by rw [factor_4_21]; decide
      have factor_4_23 : (7 : ZMod 665454160801) ^ 12497261 = 610794299017 := by
        calc
          (7 : ZMod 665454160801) ^ 12497261 = (7 : ZMod 665454160801) ^ (6248630 + 6248630 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 6248630 * (7 : ZMod 665454160801) ^ 6248630) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 610794299017 := by rw [factor_4_22]; decide
      have factor_4_24 : (7 : ZMod 665454160801) ^ 24994522 = 438605429410 := by
        calc
          (7 : ZMod 665454160801) ^ 24994522 = (7 : ZMod 665454160801) ^ (12497261 + 12497261) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 12497261 * (7 : ZMod 665454160801) ^ 12497261 := by rw [pow_add]
          _ = 438605429410 := by rw [factor_4_23]; decide
      have factor_4_25 : (7 : ZMod 665454160801) ^ 49989044 = 130047354940 := by
        calc
          (7 : ZMod 665454160801) ^ 49989044 = (7 : ZMod 665454160801) ^ (24994522 + 24994522) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 24994522 * (7 : ZMod 665454160801) ^ 24994522 := by rw [pow_add]
          _ = 130047354940 := by rw [factor_4_24]; decide
      have factor_4_26 : (7 : ZMod 665454160801) ^ 99978089 = 149230733867 := by
        calc
          (7 : ZMod 665454160801) ^ 99978089 = (7 : ZMod 665454160801) ^ (49989044 + 49989044 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 49989044 * (7 : ZMod 665454160801) ^ 49989044) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 149230733867 := by rw [factor_4_25]; decide
      have factor_4_27 : (7 : ZMod 665454160801) ^ 199956178 = 375173013969 := by
        calc
          (7 : ZMod 665454160801) ^ 199956178 = (7 : ZMod 665454160801) ^ (99978089 + 99978089) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 99978089 * (7 : ZMod 665454160801) ^ 99978089 := by rw [pow_add]
          _ = 375173013969 := by rw [factor_4_26]; decide
      have factor_4_28 : (7 : ZMod 665454160801) ^ 399912356 = 222749761952 := by
        calc
          (7 : ZMod 665454160801) ^ 399912356 = (7 : ZMod 665454160801) ^ (199956178 + 199956178) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 199956178 * (7 : ZMod 665454160801) ^ 199956178 := by rw [pow_add]
          _ = 222749761952 := by rw [factor_4_27]; decide
      have factor_4_29 : (7 : ZMod 665454160801) ^ 799824712 = 305858340510 := by
        calc
          (7 : ZMod 665454160801) ^ 799824712 = (7 : ZMod 665454160801) ^ (399912356 + 399912356) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 399912356 * (7 : ZMod 665454160801) ^ 399912356 := by rw [pow_add]
          _ = 305858340510 := by rw [factor_4_28]; decide
      have factor_4_30 : (7 : ZMod 665454160801) ^ 1599649425 = 196862093529 := by
        calc
          (7 : ZMod 665454160801) ^ 1599649425 = (7 : ZMod 665454160801) ^ (799824712 + 799824712 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 799824712 * (7 : ZMod 665454160801) ^ 799824712) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 196862093529 := by rw [factor_4_29]; decide
      have factor_4_31 : (7 : ZMod 665454160801) ^ 3199298850 = 453375663261 := by
        calc
          (7 : ZMod 665454160801) ^ 3199298850 = (7 : ZMod 665454160801) ^ (1599649425 + 1599649425) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1599649425 * (7 : ZMod 665454160801) ^ 1599649425 := by rw [pow_add]
          _ = 453375663261 := by rw [factor_4_30]; decide
      have factor_4_32 : (7 : ZMod 665454160801) ^ 6398597700 = 529909738886 := by
        calc
          (7 : ZMod 665454160801) ^ 6398597700 = (7 : ZMod 665454160801) ^ (3199298850 + 3199298850) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3199298850 * (7 : ZMod 665454160801) ^ 3199298850 := by rw [pow_add]
          _ = 529909738886 := by rw [factor_4_31]; decide
      have factor_4_33 : (7 : ZMod 665454160801) ^ 12797195400 = 388959905484 := by
        calc
          (7 : ZMod 665454160801) ^ 12797195400 = (7 : ZMod 665454160801) ^ (6398597700 + 6398597700) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 6398597700 * (7 : ZMod 665454160801) ^ 6398597700 := by rw [pow_add]
          _ = 388959905484 := by rw [factor_4_32]; decide
      have factor_4_34 : (7 : ZMod 665454160801) ^ 25594390800 = 603893185800 := by
        calc
          (7 : ZMod 665454160801) ^ 25594390800 = (7 : ZMod 665454160801) ^ (12797195400 + 12797195400) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 12797195400 * (7 : ZMod 665454160801) ^ 12797195400 := by rw [pow_add]
          _ = 603893185800 := by rw [factor_4_33]; decide
      have factor_4_35 : (7 : ZMod 665454160801) ^ 51188781600 = 427541502527 := by
        calc
          (7 : ZMod 665454160801) ^ 51188781600 = (7 : ZMod 665454160801) ^ (25594390800 + 25594390800) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 25594390800 * (7 : ZMod 665454160801) ^ 25594390800 := by rw [pow_add]
          _ = 427541502527 := by rw [factor_4_34]; decide
      change (7 : ZMod 665454160801) ^ 51188781600 ≠ 1
      rw [factor_4_35]
      decide
    ·
      have factor_5_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_5_1 : (7 : ZMod 665454160801) ^ 2 = 49 := by
        calc
          (7 : ZMod 665454160801) ^ 2 = (7 : ZMod 665454160801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_5_0]; decide
      have factor_5_2 : (7 : ZMod 665454160801) ^ 4 = 2401 := by
        calc
          (7 : ZMod 665454160801) ^ 4 = (7 : ZMod 665454160801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2 * (7 : ZMod 665454160801) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_5_1]; decide
      have factor_5_3 : (7 : ZMod 665454160801) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 665454160801) ^ 9 = (7 : ZMod 665454160801) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 4 * (7 : ZMod 665454160801) ^ 4) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_5_2]; decide
      have factor_5_4 : (7 : ZMod 665454160801) ^ 18 = 47266430402 := by
        calc
          (7 : ZMod 665454160801) ^ 18 = (7 : ZMod 665454160801) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 9 * (7 : ZMod 665454160801) ^ 9 := by rw [pow_add]
          _ = 47266430402 := by rw [factor_5_3]; decide
      have factor_5_5 : (7 : ZMod 665454160801) ^ 36 = 391020006359 := by
        calc
          (7 : ZMod 665454160801) ^ 36 = (7 : ZMod 665454160801) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 18 * (7 : ZMod 665454160801) ^ 18 := by rw [pow_add]
          _ = 391020006359 := by rw [factor_5_4]; decide
      have factor_5_6 : (7 : ZMod 665454160801) ^ 72 = 531390012815 := by
        calc
          (7 : ZMod 665454160801) ^ 72 = (7 : ZMod 665454160801) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 36 * (7 : ZMod 665454160801) ^ 36 := by rw [pow_add]
          _ = 531390012815 := by rw [factor_5_5]; decide
      have factor_5_7 : (7 : ZMod 665454160801) ^ 145 = 460103883603 := by
        calc
          (7 : ZMod 665454160801) ^ 145 = (7 : ZMod 665454160801) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 72 * (7 : ZMod 665454160801) ^ 72) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 460103883603 := by rw [factor_5_6]; decide
      have factor_5_8 : (7 : ZMod 665454160801) ^ 291 = 155715253314 := by
        calc
          (7 : ZMod 665454160801) ^ 291 = (7 : ZMod 665454160801) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 145 * (7 : ZMod 665454160801) ^ 145) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 155715253314 := by rw [factor_5_7]; decide
      have factor_5_9 : (7 : ZMod 665454160801) ^ 583 = 584228632507 := by
        calc
          (7 : ZMod 665454160801) ^ 583 = (7 : ZMod 665454160801) ^ (291 + 291 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 291 * (7 : ZMod 665454160801) ^ 291) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 584228632507 := by rw [factor_5_8]; decide
      have factor_5_10 : (7 : ZMod 665454160801) ^ 1166 = 183873984443 := by
        calc
          (7 : ZMod 665454160801) ^ 1166 = (7 : ZMod 665454160801) ^ (583 + 583) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 583 * (7 : ZMod 665454160801) ^ 583 := by rw [pow_add]
          _ = 183873984443 := by rw [factor_5_9]; decide
      have factor_5_11 : (7 : ZMod 665454160801) ^ 2333 = 576509179441 := by
        calc
          (7 : ZMod 665454160801) ^ 2333 = (7 : ZMod 665454160801) ^ (1166 + 1166 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1166 * (7 : ZMod 665454160801) ^ 1166) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 576509179441 := by rw [factor_5_10]; decide
      have factor_5_12 : (7 : ZMod 665454160801) ^ 4666 = 438279683238 := by
        calc
          (7 : ZMod 665454160801) ^ 4666 = (7 : ZMod 665454160801) ^ (2333 + 2333) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2333 * (7 : ZMod 665454160801) ^ 2333 := by rw [pow_add]
          _ = 438279683238 := by rw [factor_5_11]; decide
      have factor_5_13 : (7 : ZMod 665454160801) ^ 9332 = 298355770328 := by
        calc
          (7 : ZMod 665454160801) ^ 9332 = (7 : ZMod 665454160801) ^ (4666 + 4666) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4666 * (7 : ZMod 665454160801) ^ 4666 := by rw [pow_add]
          _ = 298355770328 := by rw [factor_5_12]; decide
      have factor_5_14 : (7 : ZMod 665454160801) ^ 18665 = 55405217939 := by
        calc
          (7 : ZMod 665454160801) ^ 18665 = (7 : ZMod 665454160801) ^ (9332 + 9332 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 9332 * (7 : ZMod 665454160801) ^ 9332) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 55405217939 := by rw [factor_5_13]; decide
      have factor_5_15 : (7 : ZMod 665454160801) ^ 37330 = 353812097730 := by
        calc
          (7 : ZMod 665454160801) ^ 37330 = (7 : ZMod 665454160801) ^ (18665 + 18665) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 18665 * (7 : ZMod 665454160801) ^ 18665 := by rw [pow_add]
          _ = 353812097730 := by rw [factor_5_14]; decide
      have factor_5_16 : (7 : ZMod 665454160801) ^ 74661 = 186195510296 := by
        calc
          (7 : ZMod 665454160801) ^ 74661 = (7 : ZMod 665454160801) ^ (37330 + 37330 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 37330 * (7 : ZMod 665454160801) ^ 37330) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 186195510296 := by rw [factor_5_15]; decide
      have factor_5_17 : (7 : ZMod 665454160801) ^ 149323 = 332698922072 := by
        calc
          (7 : ZMod 665454160801) ^ 149323 = (7 : ZMod 665454160801) ^ (74661 + 74661 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 74661 * (7 : ZMod 665454160801) ^ 74661) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 332698922072 := by rw [factor_5_16]; decide
      have factor_5_18 : (7 : ZMod 665454160801) ^ 298647 = 518909857246 := by
        calc
          (7 : ZMod 665454160801) ^ 298647 = (7 : ZMod 665454160801) ^ (149323 + 149323 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 149323 * (7 : ZMod 665454160801) ^ 149323) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 518909857246 := by rw [factor_5_17]; decide
      have factor_5_19 : (7 : ZMod 665454160801) ^ 597295 = 208935484003 := by
        calc
          (7 : ZMod 665454160801) ^ 597295 = (7 : ZMod 665454160801) ^ (298647 + 298647 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 298647 * (7 : ZMod 665454160801) ^ 298647) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 208935484003 := by rw [factor_5_18]; decide
      have factor_5_20 : (7 : ZMod 665454160801) ^ 1194591 = 555791692771 := by
        calc
          (7 : ZMod 665454160801) ^ 1194591 = (7 : ZMod 665454160801) ^ (597295 + 597295 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 597295 * (7 : ZMod 665454160801) ^ 597295) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 555791692771 := by rw [factor_5_19]; decide
      have factor_5_21 : (7 : ZMod 665454160801) ^ 2389182 = 83566571580 := by
        calc
          (7 : ZMod 665454160801) ^ 2389182 = (7 : ZMod 665454160801) ^ (1194591 + 1194591) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1194591 * (7 : ZMod 665454160801) ^ 1194591 := by rw [pow_add]
          _ = 83566571580 := by rw [factor_5_20]; decide
      have factor_5_22 : (7 : ZMod 665454160801) ^ 4778364 = 299561036255 := by
        calc
          (7 : ZMod 665454160801) ^ 4778364 = (7 : ZMod 665454160801) ^ (2389182 + 2389182) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2389182 * (7 : ZMod 665454160801) ^ 2389182 := by rw [pow_add]
          _ = 299561036255 := by rw [factor_5_21]; decide
      have factor_5_23 : (7 : ZMod 665454160801) ^ 9556729 = 136647640826 := by
        calc
          (7 : ZMod 665454160801) ^ 9556729 = (7 : ZMod 665454160801) ^ (4778364 + 4778364 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 4778364 * (7 : ZMod 665454160801) ^ 4778364) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 136647640826 := by rw [factor_5_22]; decide
      have factor_5_24 : (7 : ZMod 665454160801) ^ 19113458 = 295468456670 := by
        calc
          (7 : ZMod 665454160801) ^ 19113458 = (7 : ZMod 665454160801) ^ (9556729 + 9556729) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 9556729 * (7 : ZMod 665454160801) ^ 9556729 := by rw [pow_add]
          _ = 295468456670 := by rw [factor_5_23]; decide
      have factor_5_25 : (7 : ZMod 665454160801) ^ 38226916 = 645566272352 := by
        calc
          (7 : ZMod 665454160801) ^ 38226916 = (7 : ZMod 665454160801) ^ (19113458 + 19113458) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 19113458 * (7 : ZMod 665454160801) ^ 19113458 := by rw [pow_add]
          _ = 645566272352 := by rw [factor_5_24]; decide
      have factor_5_26 : (7 : ZMod 665454160801) ^ 76453832 = 594891747620 := by
        calc
          (7 : ZMod 665454160801) ^ 76453832 = (7 : ZMod 665454160801) ^ (38226916 + 38226916) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 38226916 * (7 : ZMod 665454160801) ^ 38226916 := by rw [pow_add]
          _ = 594891747620 := by rw [factor_5_25]; decide
      have factor_5_27 : (7 : ZMod 665454160801) ^ 152907665 = 325520763025 := by
        calc
          (7 : ZMod 665454160801) ^ 152907665 = (7 : ZMod 665454160801) ^ (76453832 + 76453832 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 76453832 * (7 : ZMod 665454160801) ^ 76453832) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 325520763025 := by rw [factor_5_26]; decide
      have factor_5_28 : (7 : ZMod 665454160801) ^ 305815331 = 182120336664 := by
        calc
          (7 : ZMod 665454160801) ^ 305815331 = (7 : ZMod 665454160801) ^ (152907665 + 152907665 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 152907665 * (7 : ZMod 665454160801) ^ 152907665) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 182120336664 := by rw [factor_5_27]; decide
      have factor_5_29 : (7 : ZMod 665454160801) ^ 611630662 = 172016671295 := by
        calc
          (7 : ZMod 665454160801) ^ 611630662 = (7 : ZMod 665454160801) ^ (305815331 + 305815331) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 305815331 * (7 : ZMod 665454160801) ^ 305815331 := by rw [pow_add]
          _ = 172016671295 := by rw [factor_5_28]; decide
      have factor_5_30 : (7 : ZMod 665454160801) ^ 1223261325 = 138569755725 := by
        calc
          (7 : ZMod 665454160801) ^ 1223261325 = (7 : ZMod 665454160801) ^ (611630662 + 611630662 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 611630662 * (7 : ZMod 665454160801) ^ 611630662) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 138569755725 := by rw [factor_5_29]; decide
      have factor_5_31 : (7 : ZMod 665454160801) ^ 2446522650 = 146731664218 := by
        calc
          (7 : ZMod 665454160801) ^ 2446522650 = (7 : ZMod 665454160801) ^ (1223261325 + 1223261325) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1223261325 * (7 : ZMod 665454160801) ^ 1223261325 := by rw [pow_add]
          _ = 146731664218 := by rw [factor_5_30]; decide
      have factor_5_32 : (7 : ZMod 665454160801) ^ 4893045300 = 593066988065 := by
        calc
          (7 : ZMod 665454160801) ^ 4893045300 = (7 : ZMod 665454160801) ^ (2446522650 + 2446522650) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2446522650 * (7 : ZMod 665454160801) ^ 2446522650 := by rw [pow_add]
          _ = 593066988065 := by rw [factor_5_31]; decide
      have factor_5_33 : (7 : ZMod 665454160801) ^ 9786090600 = 559164838306 := by
        calc
          (7 : ZMod 665454160801) ^ 9786090600 = (7 : ZMod 665454160801) ^ (4893045300 + 4893045300) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4893045300 * (7 : ZMod 665454160801) ^ 4893045300 := by rw [pow_add]
          _ = 559164838306 := by rw [factor_5_32]; decide
      have factor_5_34 : (7 : ZMod 665454160801) ^ 19572181200 = 584849061830 := by
        calc
          (7 : ZMod 665454160801) ^ 19572181200 = (7 : ZMod 665454160801) ^ (9786090600 + 9786090600) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 9786090600 * (7 : ZMod 665454160801) ^ 9786090600 := by rw [pow_add]
          _ = 584849061830 := by rw [factor_5_33]; decide
      have factor_5_35 : (7 : ZMod 665454160801) ^ 39144362400 = 97683026764 := by
        calc
          (7 : ZMod 665454160801) ^ 39144362400 = (7 : ZMod 665454160801) ^ (19572181200 + 19572181200) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 19572181200 * (7 : ZMod 665454160801) ^ 19572181200 := by rw [pow_add]
          _ = 97683026764 := by rw [factor_5_34]; decide
      change (7 : ZMod 665454160801) ^ 39144362400 ≠ 1
      rw [factor_5_35]
      decide
    ·
      have factor_6_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_6_1 : (7 : ZMod 665454160801) ^ 2 = 49 := by
        calc
          (7 : ZMod 665454160801) ^ 2 = (7 : ZMod 665454160801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_6_0]; decide
      have factor_6_2 : (7 : ZMod 665454160801) ^ 4 = 2401 := by
        calc
          (7 : ZMod 665454160801) ^ 4 = (7 : ZMod 665454160801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2 * (7 : ZMod 665454160801) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_6_1]; decide
      have factor_6_3 : (7 : ZMod 665454160801) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 665454160801) ^ 8 = (7 : ZMod 665454160801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4 * (7 : ZMod 665454160801) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_6_2]; decide
      have factor_6_4 : (7 : ZMod 665454160801) ^ 16 = 625676690352 := by
        calc
          (7 : ZMod 665454160801) ^ 16 = (7 : ZMod 665454160801) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 8 * (7 : ZMod 665454160801) ^ 8 := by rw [pow_add]
          _ = 625676690352 := by rw [factor_6_3]; decide
      have factor_6_5 : (7 : ZMod 665454160801) ^ 32 = 15406496814 := by
        calc
          (7 : ZMod 665454160801) ^ 32 = (7 : ZMod 665454160801) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 16 * (7 : ZMod 665454160801) ^ 16 := by rw [pow_add]
          _ = 15406496814 := by rw [factor_6_4]; decide
      have factor_6_6 : (7 : ZMod 665454160801) ^ 65 = 642949327542 := by
        calc
          (7 : ZMod 665454160801) ^ 65 = (7 : ZMod 665454160801) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 32 * (7 : ZMod 665454160801) ^ 32) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 642949327542 := by rw [factor_6_5]; decide
      have factor_6_7 : (7 : ZMod 665454160801) ^ 130 = 660541467571 := by
        calc
          (7 : ZMod 665454160801) ^ 130 = (7 : ZMod 665454160801) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 65 * (7 : ZMod 665454160801) ^ 65 := by rw [pow_add]
          _ = 660541467571 := by rw [factor_6_6]; decide
      have factor_6_8 : (7 : ZMod 665454160801) ^ 260 = 351714289906 := by
        calc
          (7 : ZMod 665454160801) ^ 260 = (7 : ZMod 665454160801) ^ (130 + 130) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 130 * (7 : ZMod 665454160801) ^ 130 := by rw [pow_add]
          _ = 351714289906 := by rw [factor_6_7]; decide
      have factor_6_9 : (7 : ZMod 665454160801) ^ 521 = 442914701531 := by
        calc
          (7 : ZMod 665454160801) ^ 521 = (7 : ZMod 665454160801) ^ (260 + 260 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 260 * (7 : ZMod 665454160801) ^ 260) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 442914701531 := by rw [factor_6_8]; decide
      have factor_6_10 : (7 : ZMod 665454160801) ^ 1043 = 464319259277 := by
        calc
          (7 : ZMod 665454160801) ^ 1043 = (7 : ZMod 665454160801) ^ (521 + 521 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 521 * (7 : ZMod 665454160801) ^ 521) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 464319259277 := by rw [factor_6_9]; decide
      have factor_6_11 : (7 : ZMod 665454160801) ^ 2087 = 570362117770 := by
        calc
          (7 : ZMod 665454160801) ^ 2087 = (7 : ZMod 665454160801) ^ (1043 + 1043 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1043 * (7 : ZMod 665454160801) ^ 1043) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 570362117770 := by rw [factor_6_10]; decide
      have factor_6_12 : (7 : ZMod 665454160801) ^ 4175 = 558774208619 := by
        calc
          (7 : ZMod 665454160801) ^ 4175 = (7 : ZMod 665454160801) ^ (2087 + 2087 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 2087 * (7 : ZMod 665454160801) ^ 2087) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 558774208619 := by rw [factor_6_11]; decide
      have factor_6_13 : (7 : ZMod 665454160801) ^ 8350 = 452946338374 := by
        calc
          (7 : ZMod 665454160801) ^ 8350 = (7 : ZMod 665454160801) ^ (4175 + 4175) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4175 * (7 : ZMod 665454160801) ^ 4175 := by rw [pow_add]
          _ = 452946338374 := by rw [factor_6_12]; decide
      have factor_6_14 : (7 : ZMod 665454160801) ^ 16700 = 425528077598 := by
        calc
          (7 : ZMod 665454160801) ^ 16700 = (7 : ZMod 665454160801) ^ (8350 + 8350) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 8350 * (7 : ZMod 665454160801) ^ 8350 := by rw [pow_add]
          _ = 425528077598 := by rw [factor_6_13]; decide
      have factor_6_15 : (7 : ZMod 665454160801) ^ 33401 = 551469231669 := by
        calc
          (7 : ZMod 665454160801) ^ 33401 = (7 : ZMod 665454160801) ^ (16700 + 16700 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 16700 * (7 : ZMod 665454160801) ^ 16700) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 551469231669 := by rw [factor_6_14]; decide
      have factor_6_16 : (7 : ZMod 665454160801) ^ 66802 = 307169278826 := by
        calc
          (7 : ZMod 665454160801) ^ 66802 = (7 : ZMod 665454160801) ^ (33401 + 33401) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 33401 * (7 : ZMod 665454160801) ^ 33401 := by rw [pow_add]
          _ = 307169278826 := by rw [factor_6_15]; decide
      have factor_6_17 : (7 : ZMod 665454160801) ^ 133605 = 250043011837 := by
        calc
          (7 : ZMod 665454160801) ^ 133605 = (7 : ZMod 665454160801) ^ (66802 + 66802 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 66802 * (7 : ZMod 665454160801) ^ 66802) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 250043011837 := by rw [factor_6_16]; decide
      have factor_6_18 : (7 : ZMod 665454160801) ^ 267211 = 292313650917 := by
        calc
          (7 : ZMod 665454160801) ^ 267211 = (7 : ZMod 665454160801) ^ (133605 + 133605 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 133605 * (7 : ZMod 665454160801) ^ 133605) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 292313650917 := by rw [factor_6_17]; decide
      have factor_6_19 : (7 : ZMod 665454160801) ^ 534422 = 107968036011 := by
        calc
          (7 : ZMod 665454160801) ^ 534422 = (7 : ZMod 665454160801) ^ (267211 + 267211) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 267211 * (7 : ZMod 665454160801) ^ 267211 := by rw [pow_add]
          _ = 107968036011 := by rw [factor_6_18]; decide
      have factor_6_20 : (7 : ZMod 665454160801) ^ 1068844 = 21302313204 := by
        calc
          (7 : ZMod 665454160801) ^ 1068844 = (7 : ZMod 665454160801) ^ (534422 + 534422) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 534422 * (7 : ZMod 665454160801) ^ 534422 := by rw [pow_add]
          _ = 21302313204 := by rw [factor_6_19]; decide
      have factor_6_21 : (7 : ZMod 665454160801) ^ 2137689 = 323544216185 := by
        calc
          (7 : ZMod 665454160801) ^ 2137689 = (7 : ZMod 665454160801) ^ (1068844 + 1068844 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1068844 * (7 : ZMod 665454160801) ^ 1068844) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 323544216185 := by rw [factor_6_20]; decide
      have factor_6_22 : (7 : ZMod 665454160801) ^ 4275378 = 638278043479 := by
        calc
          (7 : ZMod 665454160801) ^ 4275378 = (7 : ZMod 665454160801) ^ (2137689 + 2137689) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2137689 * (7 : ZMod 665454160801) ^ 2137689 := by rw [pow_add]
          _ = 638278043479 := by rw [factor_6_21]; decide
      have factor_6_23 : (7 : ZMod 665454160801) ^ 8550757 = 530077147187 := by
        calc
          (7 : ZMod 665454160801) ^ 8550757 = (7 : ZMod 665454160801) ^ (4275378 + 4275378 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 4275378 * (7 : ZMod 665454160801) ^ 4275378) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 530077147187 := by rw [factor_6_22]; decide
      have factor_6_24 : (7 : ZMod 665454160801) ^ 17101515 = 467286527914 := by
        calc
          (7 : ZMod 665454160801) ^ 17101515 = (7 : ZMod 665454160801) ^ (8550757 + 8550757 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 8550757 * (7 : ZMod 665454160801) ^ 8550757) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 467286527914 := by rw [factor_6_23]; decide
      have factor_6_25 : (7 : ZMod 665454160801) ^ 34203030 = 364955727568 := by
        calc
          (7 : ZMod 665454160801) ^ 34203030 = (7 : ZMod 665454160801) ^ (17101515 + 17101515) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 17101515 * (7 : ZMod 665454160801) ^ 17101515 := by rw [pow_add]
          _ = 364955727568 := by rw [factor_6_24]; decide
      have factor_6_26 : (7 : ZMod 665454160801) ^ 68406060 = 277653375068 := by
        calc
          (7 : ZMod 665454160801) ^ 68406060 = (7 : ZMod 665454160801) ^ (34203030 + 34203030) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 34203030 * (7 : ZMod 665454160801) ^ 34203030 := by rw [pow_add]
          _ = 277653375068 := by rw [factor_6_25]; decide
      have factor_6_27 : (7 : ZMod 665454160801) ^ 136812121 = 50223812793 := by
        calc
          (7 : ZMod 665454160801) ^ 136812121 = (7 : ZMod 665454160801) ^ (68406060 + 68406060 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 68406060 * (7 : ZMod 665454160801) ^ 68406060) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 50223812793 := by rw [factor_6_26]; decide
      have factor_6_28 : (7 : ZMod 665454160801) ^ 273624243 = 470695469983 := by
        calc
          (7 : ZMod 665454160801) ^ 273624243 = (7 : ZMod 665454160801) ^ (136812121 + 136812121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 136812121 * (7 : ZMod 665454160801) ^ 136812121) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 470695469983 := by rw [factor_6_27]; decide
      have factor_6_29 : (7 : ZMod 665454160801) ^ 547248487 = 493133661235 := by
        calc
          (7 : ZMod 665454160801) ^ 547248487 = (7 : ZMod 665454160801) ^ (273624243 + 273624243 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 273624243 * (7 : ZMod 665454160801) ^ 273624243) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 493133661235 := by rw [factor_6_28]; decide
      have factor_6_30 : (7 : ZMod 665454160801) ^ 1094496975 = 308698362933 := by
        calc
          (7 : ZMod 665454160801) ^ 1094496975 = (7 : ZMod 665454160801) ^ (547248487 + 547248487 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 547248487 * (7 : ZMod 665454160801) ^ 547248487) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 308698362933 := by rw [factor_6_29]; decide
      have factor_6_31 : (7 : ZMod 665454160801) ^ 2188993950 = 630045439222 := by
        calc
          (7 : ZMod 665454160801) ^ 2188993950 = (7 : ZMod 665454160801) ^ (1094496975 + 1094496975) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1094496975 * (7 : ZMod 665454160801) ^ 1094496975 := by rw [pow_add]
          _ = 630045439222 := by rw [factor_6_30]; decide
      have factor_6_32 : (7 : ZMod 665454160801) ^ 4377987900 = 407668755385 := by
        calc
          (7 : ZMod 665454160801) ^ 4377987900 = (7 : ZMod 665454160801) ^ (2188993950 + 2188993950) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2188993950 * (7 : ZMod 665454160801) ^ 2188993950 := by rw [pow_add]
          _ = 407668755385 := by rw [factor_6_31]; decide
      have factor_6_33 : (7 : ZMod 665454160801) ^ 8755975800 = 307014755230 := by
        calc
          (7 : ZMod 665454160801) ^ 8755975800 = (7 : ZMod 665454160801) ^ (4377987900 + 4377987900) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 4377987900 * (7 : ZMod 665454160801) ^ 4377987900 := by rw [pow_add]
          _ = 307014755230 := by rw [factor_6_32]; decide
      have factor_6_34 : (7 : ZMod 665454160801) ^ 17511951600 = 228455524649 := by
        calc
          (7 : ZMod 665454160801) ^ 17511951600 = (7 : ZMod 665454160801) ^ (8755975800 + 8755975800) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 8755975800 * (7 : ZMod 665454160801) ^ 8755975800 := by rw [pow_add]
          _ = 228455524649 := by rw [factor_6_33]; decide
      have factor_6_35 : (7 : ZMod 665454160801) ^ 35023903200 = 11904243259 := by
        calc
          (7 : ZMod 665454160801) ^ 35023903200 = (7 : ZMod 665454160801) ^ (17511951600 + 17511951600) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 17511951600 * (7 : ZMod 665454160801) ^ 17511951600 := by rw [pow_add]
          _ = 11904243259 := by rw [factor_6_34]; decide
      change (7 : ZMod 665454160801) ^ 35023903200 ≠ 1
      rw [factor_6_35]
      decide
    ·
      have factor_7_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_7_1 : (7 : ZMod 665454160801) ^ 3 = 343 := by
        calc
          (7 : ZMod 665454160801) ^ 3 = (7 : ZMod 665454160801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_7_0]; decide
      have factor_7_2 : (7 : ZMod 665454160801) ^ 6 = 117649 := by
        calc
          (7 : ZMod 665454160801) ^ 6 = (7 : ZMod 665454160801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3 * (7 : ZMod 665454160801) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_7_1]; decide
      have factor_7_3 : (7 : ZMod 665454160801) ^ 13 = 96889010407 := by
        calc
          (7 : ZMod 665454160801) ^ 13 = (7 : ZMod 665454160801) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 6 * (7 : ZMod 665454160801) ^ 6) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 96889010407 := by rw [factor_7_2]; decide
      have factor_7_4 : (7 : ZMod 665454160801) ^ 26 = 46387176935 := by
        calc
          (7 : ZMod 665454160801) ^ 26 = (7 : ZMod 665454160801) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 13 * (7 : ZMod 665454160801) ^ 13 := by rw [pow_add]
          _ = 46387176935 := by rw [factor_7_3]; decide
      have factor_7_5 : (7 : ZMod 665454160801) ^ 53 = 95019533485 := by
        calc
          (7 : ZMod 665454160801) ^ 53 = (7 : ZMod 665454160801) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 26 * (7 : ZMod 665454160801) ^ 26) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 95019533485 := by rw [factor_7_4]; decide
      have factor_7_6 : (7 : ZMod 665454160801) ^ 107 = 158910959289 := by
        calc
          (7 : ZMod 665454160801) ^ 107 = (7 : ZMod 665454160801) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 53 * (7 : ZMod 665454160801) ^ 53) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 158910959289 := by rw [factor_7_5]; decide
      have factor_7_7 : (7 : ZMod 665454160801) ^ 215 = 80075644986 := by
        calc
          (7 : ZMod 665454160801) ^ 215 = (7 : ZMod 665454160801) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 107 * (7 : ZMod 665454160801) ^ 107) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 80075644986 := by rw [factor_7_6]; decide
      have factor_7_8 : (7 : ZMod 665454160801) ^ 431 = 170126274762 := by
        calc
          (7 : ZMod 665454160801) ^ 431 = (7 : ZMod 665454160801) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 215 * (7 : ZMod 665454160801) ^ 215) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 170126274762 := by rw [factor_7_7]; decide
      have factor_7_9 : (7 : ZMod 665454160801) ^ 862 = 557194721961 := by
        calc
          (7 : ZMod 665454160801) ^ 862 = (7 : ZMod 665454160801) ^ (431 + 431) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 431 * (7 : ZMod 665454160801) ^ 431 := by rw [pow_add]
          _ = 557194721961 := by rw [factor_7_8]; decide
      have factor_7_10 : (7 : ZMod 665454160801) ^ 1724 = 89049174125 := by
        calc
          (7 : ZMod 665454160801) ^ 1724 = (7 : ZMod 665454160801) ^ (862 + 862) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 862 * (7 : ZMod 665454160801) ^ 862 := by rw [pow_add]
          _ = 89049174125 := by rw [factor_7_9]; decide
      have factor_7_11 : (7 : ZMod 665454160801) ^ 3449 = 241097400141 := by
        calc
          (7 : ZMod 665454160801) ^ 3449 = (7 : ZMod 665454160801) ^ (1724 + 1724 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1724 * (7 : ZMod 665454160801) ^ 1724) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 241097400141 := by rw [factor_7_10]; decide
      have factor_7_12 : (7 : ZMod 665454160801) ^ 6898 = 335236194505 := by
        calc
          (7 : ZMod 665454160801) ^ 6898 = (7 : ZMod 665454160801) ^ (3449 + 3449) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3449 * (7 : ZMod 665454160801) ^ 3449 := by rw [pow_add]
          _ = 335236194505 := by rw [factor_7_11]; decide
      have factor_7_13 : (7 : ZMod 665454160801) ^ 13796 = 560305527234 := by
        calc
          (7 : ZMod 665454160801) ^ 13796 = (7 : ZMod 665454160801) ^ (6898 + 6898) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 6898 * (7 : ZMod 665454160801) ^ 6898 := by rw [pow_add]
          _ = 560305527234 := by rw [factor_7_12]; decide
      have factor_7_14 : (7 : ZMod 665454160801) ^ 27592 = 657092967282 := by
        calc
          (7 : ZMod 665454160801) ^ 27592 = (7 : ZMod 665454160801) ^ (13796 + 13796) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 13796 * (7 : ZMod 665454160801) ^ 13796 := by rw [pow_add]
          _ = 657092967282 := by rw [factor_7_13]; decide
      have factor_7_15 : (7 : ZMod 665454160801) ^ 55184 = 24829263155 := by
        calc
          (7 : ZMod 665454160801) ^ 55184 = (7 : ZMod 665454160801) ^ (27592 + 27592) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 27592 * (7 : ZMod 665454160801) ^ 27592 := by rw [pow_add]
          _ = 24829263155 := by rw [factor_7_14]; decide
      have factor_7_16 : (7 : ZMod 665454160801) ^ 110369 = 420557532748 := by
        calc
          (7 : ZMod 665454160801) ^ 110369 = (7 : ZMod 665454160801) ^ (55184 + 55184 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 55184 * (7 : ZMod 665454160801) ^ 55184) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 420557532748 := by rw [factor_7_15]; decide
      have factor_7_17 : (7 : ZMod 665454160801) ^ 220739 = 386927440092 := by
        calc
          (7 : ZMod 665454160801) ^ 220739 = (7 : ZMod 665454160801) ^ (110369 + 110369 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 110369 * (7 : ZMod 665454160801) ^ 110369) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 386927440092 := by rw [factor_7_16]; decide
      have factor_7_18 : (7 : ZMod 665454160801) ^ 441479 = 5232508424 := by
        calc
          (7 : ZMod 665454160801) ^ 441479 = (7 : ZMod 665454160801) ^ (220739 + 220739 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 220739 * (7 : ZMod 665454160801) ^ 220739) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 5232508424 := by rw [factor_7_17]; decide
      have factor_7_19 : (7 : ZMod 665454160801) ^ 882958 = 531423623430 := by
        calc
          (7 : ZMod 665454160801) ^ 882958 = (7 : ZMod 665454160801) ^ (441479 + 441479) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 441479 * (7 : ZMod 665454160801) ^ 441479 := by rw [pow_add]
          _ = 531423623430 := by rw [factor_7_18]; decide
      have factor_7_20 : (7 : ZMod 665454160801) ^ 1765917 = 345104320997 := by
        calc
          (7 : ZMod 665454160801) ^ 1765917 = (7 : ZMod 665454160801) ^ (882958 + 882958 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 882958 * (7 : ZMod 665454160801) ^ 882958) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 345104320997 := by rw [factor_7_19]; decide
      have factor_7_21 : (7 : ZMod 665454160801) ^ 3531834 = 354919180384 := by
        calc
          (7 : ZMod 665454160801) ^ 3531834 = (7 : ZMod 665454160801) ^ (1765917 + 1765917) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1765917 * (7 : ZMod 665454160801) ^ 1765917 := by rw [pow_add]
          _ = 354919180384 := by rw [factor_7_20]; decide
      have factor_7_22 : (7 : ZMod 665454160801) ^ 7063669 = 456159037450 := by
        calc
          (7 : ZMod 665454160801) ^ 7063669 = (7 : ZMod 665454160801) ^ (3531834 + 3531834 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 3531834 * (7 : ZMod 665454160801) ^ 3531834) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 456159037450 := by rw [factor_7_21]; decide
      have factor_7_23 : (7 : ZMod 665454160801) ^ 14127338 = 288469135478 := by
        calc
          (7 : ZMod 665454160801) ^ 14127338 = (7 : ZMod 665454160801) ^ (7063669 + 7063669) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 7063669 * (7 : ZMod 665454160801) ^ 7063669 := by rw [pow_add]
          _ = 288469135478 := by rw [factor_7_22]; decide
      have factor_7_24 : (7 : ZMod 665454160801) ^ 28254677 = 45356403670 := by
        calc
          (7 : ZMod 665454160801) ^ 28254677 = (7 : ZMod 665454160801) ^ (14127338 + 14127338 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 14127338 * (7 : ZMod 665454160801) ^ 14127338) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 45356403670 := by rw [factor_7_23]; decide
      have factor_7_25 : (7 : ZMod 665454160801) ^ 56509354 = 630027408509 := by
        calc
          (7 : ZMod 665454160801) ^ 56509354 = (7 : ZMod 665454160801) ^ (28254677 + 28254677) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 28254677 * (7 : ZMod 665454160801) ^ 28254677 := by rw [pow_add]
          _ = 630027408509 := by rw [factor_7_24]; decide
      have factor_7_26 : (7 : ZMod 665454160801) ^ 113018709 = 460500783069 := by
        calc
          (7 : ZMod 665454160801) ^ 113018709 = (7 : ZMod 665454160801) ^ (56509354 + 56509354 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 56509354 * (7 : ZMod 665454160801) ^ 56509354) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 460500783069 := by rw [factor_7_25]; decide
      have factor_7_27 : (7 : ZMod 665454160801) ^ 226037418 = 166738277788 := by
        calc
          (7 : ZMod 665454160801) ^ 226037418 = (7 : ZMod 665454160801) ^ (113018709 + 113018709) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 113018709 * (7 : ZMod 665454160801) ^ 113018709 := by rw [pow_add]
          _ = 166738277788 := by rw [factor_7_26]; decide
      have factor_7_28 : (7 : ZMod 665454160801) ^ 452074837 = 618412284518 := by
        calc
          (7 : ZMod 665454160801) ^ 452074837 = (7 : ZMod 665454160801) ^ (226037418 + 226037418 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 226037418 * (7 : ZMod 665454160801) ^ 226037418) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 618412284518 := by rw [factor_7_27]; decide
      have factor_7_29 : (7 : ZMod 665454160801) ^ 904149675 = 52980834510 := by
        calc
          (7 : ZMod 665454160801) ^ 904149675 = (7 : ZMod 665454160801) ^ (452074837 + 452074837 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 452074837 * (7 : ZMod 665454160801) ^ 452074837) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 52980834510 := by rw [factor_7_28]; decide
      have factor_7_30 : (7 : ZMod 665454160801) ^ 1808299350 = 1830423110 := by
        calc
          (7 : ZMod 665454160801) ^ 1808299350 = (7 : ZMod 665454160801) ^ (904149675 + 904149675) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 904149675 * (7 : ZMod 665454160801) ^ 904149675 := by rw [pow_add]
          _ = 1830423110 := by rw [factor_7_29]; decide
      have factor_7_31 : (7 : ZMod 665454160801) ^ 3616598700 = 189196373270 := by
        calc
          (7 : ZMod 665454160801) ^ 3616598700 = (7 : ZMod 665454160801) ^ (1808299350 + 1808299350) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1808299350 * (7 : ZMod 665454160801) ^ 1808299350 := by rw [pow_add]
          _ = 189196373270 := by rw [factor_7_30]; decide
      have factor_7_32 : (7 : ZMod 665454160801) ^ 7233197400 = 175843392642 := by
        calc
          (7 : ZMod 665454160801) ^ 7233197400 = (7 : ZMod 665454160801) ^ (3616598700 + 3616598700) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 3616598700 * (7 : ZMod 665454160801) ^ 3616598700 := by rw [pow_add]
          _ = 175843392642 := by rw [factor_7_31]; decide
      have factor_7_33 : (7 : ZMod 665454160801) ^ 14466394800 = 247532528272 := by
        calc
          (7 : ZMod 665454160801) ^ 14466394800 = (7 : ZMod 665454160801) ^ (7233197400 + 7233197400) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 7233197400 * (7 : ZMod 665454160801) ^ 7233197400 := by rw [pow_add]
          _ = 247532528272 := by rw [factor_7_32]; decide
      have factor_7_34 : (7 : ZMod 665454160801) ^ 28932789600 = 147398872333 := by
        calc
          (7 : ZMod 665454160801) ^ 28932789600 = (7 : ZMod 665454160801) ^ (14466394800 + 14466394800) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 14466394800 * (7 : ZMod 665454160801) ^ 14466394800 := by rw [pow_add]
          _ = 147398872333 := by rw [factor_7_33]; decide
      change (7 : ZMod 665454160801) ^ 28932789600 ≠ 1
      rw [factor_7_34]
      decide
    ·
      have factor_8_0 : (7 : ZMod 665454160801) ^ 1 = 7 := by norm_num
      have factor_8_1 : (7 : ZMod 665454160801) ^ 2 = 49 := by
        calc
          (7 : ZMod 665454160801) ^ 2 = (7 : ZMod 665454160801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1 * (7 : ZMod 665454160801) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_8_0]; decide
      have factor_8_2 : (7 : ZMod 665454160801) ^ 5 = 16807 := by
        calc
          (7 : ZMod 665454160801) ^ 5 = (7 : ZMod 665454160801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 2 * (7 : ZMod 665454160801) ^ 2) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_8_1]; decide
      have factor_8_3 : (7 : ZMod 665454160801) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 665454160801) ^ 10 = (7 : ZMod 665454160801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 5 * (7 : ZMod 665454160801) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_8_2]; decide
      have factor_8_4 : (7 : ZMod 665454160801) ^ 21 = 241485768662 := by
        calc
          (7 : ZMod 665454160801) ^ 21 = (7 : ZMod 665454160801) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 10 * (7 : ZMod 665454160801) ^ 10) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 241485768662 := by rw [factor_8_3]; decide
      have factor_8_5 : (7 : ZMod 665454160801) ^ 42 = 266591956861 := by
        calc
          (7 : ZMod 665454160801) ^ 42 = (7 : ZMod 665454160801) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 21 * (7 : ZMod 665454160801) ^ 21 := by rw [pow_add]
          _ = 266591956861 := by rw [factor_8_4]; decide
      have factor_8_6 : (7 : ZMod 665454160801) ^ 85 = 528117212933 := by
        calc
          (7 : ZMod 665454160801) ^ 85 = (7 : ZMod 665454160801) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 42 * (7 : ZMod 665454160801) ^ 42) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 528117212933 := by rw [factor_8_5]; decide
      have factor_8_7 : (7 : ZMod 665454160801) ^ 170 = 433936807985 := by
        calc
          (7 : ZMod 665454160801) ^ 170 = (7 : ZMod 665454160801) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 85 * (7 : ZMod 665454160801) ^ 85 := by rw [pow_add]
          _ = 433936807985 := by rw [factor_8_6]; decide
      have factor_8_8 : (7 : ZMod 665454160801) ^ 341 = 316151097749 := by
        calc
          (7 : ZMod 665454160801) ^ 341 = (7 : ZMod 665454160801) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 170 * (7 : ZMod 665454160801) ^ 170) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 316151097749 := by rw [factor_8_7]; decide
      have factor_8_9 : (7 : ZMod 665454160801) ^ 683 = 580707732653 := by
        calc
          (7 : ZMod 665454160801) ^ 683 = (7 : ZMod 665454160801) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 341 * (7 : ZMod 665454160801) ^ 341) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 580707732653 := by rw [factor_8_8]; decide
      have factor_8_10 : (7 : ZMod 665454160801) ^ 1367 = 253179269244 := by
        calc
          (7 : ZMod 665454160801) ^ 1367 = (7 : ZMod 665454160801) ^ (683 + 683 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 683 * (7 : ZMod 665454160801) ^ 683) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 253179269244 := by rw [factor_8_9]; decide
      have factor_8_11 : (7 : ZMod 665454160801) ^ 2735 = 581984809508 := by
        calc
          (7 : ZMod 665454160801) ^ 2735 = (7 : ZMod 665454160801) ^ (1367 + 1367 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 1367 * (7 : ZMod 665454160801) ^ 1367) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 581984809508 := by rw [factor_8_10]; decide
      have factor_8_12 : (7 : ZMod 665454160801) ^ 5470 = 122629798208 := by
        calc
          (7 : ZMod 665454160801) ^ 5470 = (7 : ZMod 665454160801) ^ (2735 + 2735) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2735 * (7 : ZMod 665454160801) ^ 2735 := by rw [pow_add]
          _ = 122629798208 := by rw [factor_8_11]; decide
      have factor_8_13 : (7 : ZMod 665454160801) ^ 10941 = 652678716711 := by
        calc
          (7 : ZMod 665454160801) ^ 10941 = (7 : ZMod 665454160801) ^ (5470 + 5470 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 5470 * (7 : ZMod 665454160801) ^ 5470) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 652678716711 := by rw [factor_8_12]; decide
      have factor_8_14 : (7 : ZMod 665454160801) ^ 21883 = 432408460465 := by
        calc
          (7 : ZMod 665454160801) ^ 21883 = (7 : ZMod 665454160801) ^ (10941 + 10941 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 10941 * (7 : ZMod 665454160801) ^ 10941) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 432408460465 := by rw [factor_8_13]; decide
      have factor_8_15 : (7 : ZMod 665454160801) ^ 43767 = 81231080016 := by
        calc
          (7 : ZMod 665454160801) ^ 43767 = (7 : ZMod 665454160801) ^ (21883 + 21883 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 21883 * (7 : ZMod 665454160801) ^ 21883) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 81231080016 := by rw [factor_8_14]; decide
      have factor_8_16 : (7 : ZMod 665454160801) ^ 87534 = 129790610127 := by
        calc
          (7 : ZMod 665454160801) ^ 87534 = (7 : ZMod 665454160801) ^ (43767 + 43767) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 43767 * (7 : ZMod 665454160801) ^ 43767 := by rw [pow_add]
          _ = 129790610127 := by rw [factor_8_15]; decide
      have factor_8_17 : (7 : ZMod 665454160801) ^ 175069 = 452065348012 := by
        calc
          (7 : ZMod 665454160801) ^ 175069 = (7 : ZMod 665454160801) ^ (87534 + 87534 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 87534 * (7 : ZMod 665454160801) ^ 87534) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 452065348012 := by rw [factor_8_16]; decide
      have factor_8_18 : (7 : ZMod 665454160801) ^ 350138 = 8232392851 := by
        calc
          (7 : ZMod 665454160801) ^ 350138 = (7 : ZMod 665454160801) ^ (175069 + 175069) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 175069 * (7 : ZMod 665454160801) ^ 175069 := by rw [pow_add]
          _ = 8232392851 := by rw [factor_8_17]; decide
      have factor_8_19 : (7 : ZMod 665454160801) ^ 700277 = 12246715737 := by
        calc
          (7 : ZMod 665454160801) ^ 700277 = (7 : ZMod 665454160801) ^ (350138 + 350138 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 350138 * (7 : ZMod 665454160801) ^ 350138) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 12246715737 := by rw [factor_8_18]; decide
      have factor_8_20 : (7 : ZMod 665454160801) ^ 1400555 = 420738645676 := by
        calc
          (7 : ZMod 665454160801) ^ 1400555 = (7 : ZMod 665454160801) ^ (700277 + 700277 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 700277 * (7 : ZMod 665454160801) ^ 700277) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 420738645676 := by rw [factor_8_19]; decide
      have factor_8_21 : (7 : ZMod 665454160801) ^ 2801110 = 188921392107 := by
        calc
          (7 : ZMod 665454160801) ^ 2801110 = (7 : ZMod 665454160801) ^ (1400555 + 1400555) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1400555 * (7 : ZMod 665454160801) ^ 1400555 := by rw [pow_add]
          _ = 188921392107 := by rw [factor_8_20]; decide
      have factor_8_22 : (7 : ZMod 665454160801) ^ 5602220 = 145979902261 := by
        calc
          (7 : ZMod 665454160801) ^ 5602220 = (7 : ZMod 665454160801) ^ (2801110 + 2801110) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2801110 * (7 : ZMod 665454160801) ^ 2801110 := by rw [pow_add]
          _ = 145979902261 := by rw [factor_8_21]; decide
      have factor_8_23 : (7 : ZMod 665454160801) ^ 11204441 = 155112319872 := by
        calc
          (7 : ZMod 665454160801) ^ 11204441 = (7 : ZMod 665454160801) ^ (5602220 + 5602220 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 5602220 * (7 : ZMod 665454160801) ^ 5602220) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 155112319872 := by rw [factor_8_22]; decide
      have factor_8_24 : (7 : ZMod 665454160801) ^ 22408882 = 275324664176 := by
        calc
          (7 : ZMod 665454160801) ^ 22408882 = (7 : ZMod 665454160801) ^ (11204441 + 11204441) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 11204441 * (7 : ZMod 665454160801) ^ 11204441 := by rw [pow_add]
          _ = 275324664176 := by rw [factor_8_23]; decide
      have factor_8_25 : (7 : ZMod 665454160801) ^ 44817764 = 611079830022 := by
        calc
          (7 : ZMod 665454160801) ^ 44817764 = (7 : ZMod 665454160801) ^ (22408882 + 22408882) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 22408882 * (7 : ZMod 665454160801) ^ 22408882 := by rw [pow_add]
          _ = 611079830022 := by rw [factor_8_24]; decide
      have factor_8_26 : (7 : ZMod 665454160801) ^ 89635528 = 584713020048 := by
        calc
          (7 : ZMod 665454160801) ^ 89635528 = (7 : ZMod 665454160801) ^ (44817764 + 44817764) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 44817764 * (7 : ZMod 665454160801) ^ 44817764 := by rw [pow_add]
          _ = 584713020048 := by rw [factor_8_25]; decide
      have factor_8_27 : (7 : ZMod 665454160801) ^ 179271056 = 254612641396 := by
        calc
          (7 : ZMod 665454160801) ^ 179271056 = (7 : ZMod 665454160801) ^ (89635528 + 89635528) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 89635528 * (7 : ZMod 665454160801) ^ 89635528 := by rw [pow_add]
          _ = 254612641396 := by rw [factor_8_26]; decide
      have factor_8_28 : (7 : ZMod 665454160801) ^ 358542112 = 238077987385 := by
        calc
          (7 : ZMod 665454160801) ^ 358542112 = (7 : ZMod 665454160801) ^ (179271056 + 179271056) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 179271056 * (7 : ZMod 665454160801) ^ 179271056 := by rw [pow_add]
          _ = 238077987385 := by rw [factor_8_27]; decide
      have factor_8_29 : (7 : ZMod 665454160801) ^ 717084225 = 580304716830 := by
        calc
          (7 : ZMod 665454160801) ^ 717084225 = (7 : ZMod 665454160801) ^ (358542112 + 358542112 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = ((7 : ZMod 665454160801) ^ 358542112 * (7 : ZMod 665454160801) ^ 358542112) * (7 : ZMod 665454160801) := by rw [pow_succ, pow_add]
          _ = 580304716830 := by rw [factor_8_28]; decide
      have factor_8_30 : (7 : ZMod 665454160801) ^ 1434168450 = 543350933319 := by
        calc
          (7 : ZMod 665454160801) ^ 1434168450 = (7 : ZMod 665454160801) ^ (717084225 + 717084225) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 717084225 * (7 : ZMod 665454160801) ^ 717084225 := by rw [pow_add]
          _ = 543350933319 := by rw [factor_8_29]; decide
      have factor_8_31 : (7 : ZMod 665454160801) ^ 2868336900 = 607161989818 := by
        calc
          (7 : ZMod 665454160801) ^ 2868336900 = (7 : ZMod 665454160801) ^ (1434168450 + 1434168450) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 1434168450 * (7 : ZMod 665454160801) ^ 1434168450 := by rw [pow_add]
          _ = 607161989818 := by rw [factor_8_30]; decide
      have factor_8_32 : (7 : ZMod 665454160801) ^ 5736673800 = 96838422250 := by
        calc
          (7 : ZMod 665454160801) ^ 5736673800 = (7 : ZMod 665454160801) ^ (2868336900 + 2868336900) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 2868336900 * (7 : ZMod 665454160801) ^ 2868336900 := by rw [pow_add]
          _ = 96838422250 := by rw [factor_8_31]; decide
      have factor_8_33 : (7 : ZMod 665454160801) ^ 11473347600 = 50309425842 := by
        calc
          (7 : ZMod 665454160801) ^ 11473347600 = (7 : ZMod 665454160801) ^ (5736673800 + 5736673800) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 5736673800 * (7 : ZMod 665454160801) ^ 5736673800 := by rw [pow_add]
          _ = 50309425842 := by rw [factor_8_32]; decide
      have factor_8_34 : (7 : ZMod 665454160801) ^ 22946695200 = 415514497068 := by
        calc
          (7 : ZMod 665454160801) ^ 22946695200 = (7 : ZMod 665454160801) ^ (11473347600 + 11473347600) :=
            congrArg (fun n : ℕ => (7 : ZMod 665454160801) ^ n) (by norm_num)
          _ = (7 : ZMod 665454160801) ^ 11473347600 * (7 : ZMod 665454160801) ^ 11473347600 := by rw [pow_add]
          _ = 415514497068 := by rw [factor_8_33]; decide
      change (7 : ZMod 665454160801) ^ 22946695200 ≠ 1
      rw [factor_8_34]
      decide

#print axioms prime_lucas_665454160801

end TotientTailPeriodKiller
end Erdos249257
