import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_448521808841 : Nat.Prime 448521808841 := by
  apply lucas_primality 448521808841 (3 : ZMod 448521808841)
  ·
      have fermat_0 : (3 : ZMod 448521808841) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 448521808841) ^ 3 = 27 := by
        calc
          (3 : ZMod 448521808841) ^ 3 = (3 : ZMod 448521808841) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1 * (3 : ZMod 448521808841) ^ 1) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 448521808841) ^ 6 = 729 := by
        calc
          (3 : ZMod 448521808841) ^ 6 = (3 : ZMod 448521808841) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 3 * (3 : ZMod 448521808841) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 448521808841) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 448521808841) ^ 13 = (3 : ZMod 448521808841) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 6 * (3 : ZMod 448521808841) ^ 6) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 448521808841) ^ 26 = 299256784124 := by
        calc
          (3 : ZMod 448521808841) ^ 26 = (3 : ZMod 448521808841) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 13 * (3 : ZMod 448521808841) ^ 13 := by rw [pow_add]
          _ = 299256784124 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 448521808841) ^ 52 = 288937088314 := by
        calc
          (3 : ZMod 448521808841) ^ 52 = (3 : ZMod 448521808841) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 26 * (3 : ZMod 448521808841) ^ 26 := by rw [pow_add]
          _ = 288937088314 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 448521808841) ^ 104 = 188734132322 := by
        calc
          (3 : ZMod 448521808841) ^ 104 = (3 : ZMod 448521808841) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 52 * (3 : ZMod 448521808841) ^ 52 := by rw [pow_add]
          _ = 188734132322 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 448521808841) ^ 208 = 46144353638 := by
        calc
          (3 : ZMod 448521808841) ^ 208 = (3 : ZMod 448521808841) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 104 * (3 : ZMod 448521808841) ^ 104 := by rw [pow_add]
          _ = 46144353638 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 448521808841) ^ 417 = 53844686086 := by
        calc
          (3 : ZMod 448521808841) ^ 417 = (3 : ZMod 448521808841) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 208 * (3 : ZMod 448521808841) ^ 208) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 53844686086 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 448521808841) ^ 835 = 285049105611 := by
        calc
          (3 : ZMod 448521808841) ^ 835 = (3 : ZMod 448521808841) ^ (417 + 417 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 417 * (3 : ZMod 448521808841) ^ 417) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 285049105611 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 448521808841) ^ 1670 = 314907313613 := by
        calc
          (3 : ZMod 448521808841) ^ 1670 = (3 : ZMod 448521808841) ^ (835 + 835) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 835 * (3 : ZMod 448521808841) ^ 835 := by rw [pow_add]
          _ = 314907313613 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 448521808841) ^ 3341 = 223806904395 := by
        calc
          (3 : ZMod 448521808841) ^ 3341 = (3 : ZMod 448521808841) ^ (1670 + 1670 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1670 * (3 : ZMod 448521808841) ^ 1670) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 223806904395 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 448521808841) ^ 6683 = 317660942126 := by
        calc
          (3 : ZMod 448521808841) ^ 6683 = (3 : ZMod 448521808841) ^ (3341 + 3341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3341 * (3 : ZMod 448521808841) ^ 3341) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 317660942126 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 448521808841) ^ 13366 = 195028067687 := by
        calc
          (3 : ZMod 448521808841) ^ 13366 = (3 : ZMod 448521808841) ^ (6683 + 6683) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 6683 * (3 : ZMod 448521808841) ^ 6683 := by rw [pow_add]
          _ = 195028067687 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 448521808841) ^ 26733 = 293899804340 := by
        calc
          (3 : ZMod 448521808841) ^ 26733 = (3 : ZMod 448521808841) ^ (13366 + 13366 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 13366 * (3 : ZMod 448521808841) ^ 13366) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 293899804340 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 448521808841) ^ 53467 = 280879181495 := by
        calc
          (3 : ZMod 448521808841) ^ 53467 = (3 : ZMod 448521808841) ^ (26733 + 26733 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 26733 * (3 : ZMod 448521808841) ^ 26733) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 280879181495 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 448521808841) ^ 106935 = 207018257262 := by
        calc
          (3 : ZMod 448521808841) ^ 106935 = (3 : ZMod 448521808841) ^ (53467 + 53467 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 53467 * (3 : ZMod 448521808841) ^ 53467) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 207018257262 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 448521808841) ^ 213871 = 39531638307 := by
        calc
          (3 : ZMod 448521808841) ^ 213871 = (3 : ZMod 448521808841) ^ (106935 + 106935 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 106935 * (3 : ZMod 448521808841) ^ 106935) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 39531638307 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 448521808841) ^ 427743 = 359703932466 := by
        calc
          (3 : ZMod 448521808841) ^ 427743 = (3 : ZMod 448521808841) ^ (213871 + 213871 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 213871 * (3 : ZMod 448521808841) ^ 213871) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 359703932466 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 448521808841) ^ 855487 = 320967201498 := by
        calc
          (3 : ZMod 448521808841) ^ 855487 = (3 : ZMod 448521808841) ^ (427743 + 427743 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 427743 * (3 : ZMod 448521808841) ^ 427743) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 320967201498 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 448521808841) ^ 1710974 = 443981763510 := by
        calc
          (3 : ZMod 448521808841) ^ 1710974 = (3 : ZMod 448521808841) ^ (855487 + 855487) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 855487 * (3 : ZMod 448521808841) ^ 855487 := by rw [pow_add]
          _ = 443981763510 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 448521808841) ^ 3421949 = 193259490680 := by
        calc
          (3 : ZMod 448521808841) ^ 3421949 = (3 : ZMod 448521808841) ^ (1710974 + 1710974 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1710974 * (3 : ZMod 448521808841) ^ 1710974) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 193259490680 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 448521808841) ^ 6843899 = 257211520379 := by
        calc
          (3 : ZMod 448521808841) ^ 6843899 = (3 : ZMod 448521808841) ^ (3421949 + 3421949 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3421949 * (3 : ZMod 448521808841) ^ 3421949) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 257211520379 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 448521808841) ^ 13687799 = 437391113789 := by
        calc
          (3 : ZMod 448521808841) ^ 13687799 = (3 : ZMod 448521808841) ^ (6843899 + 6843899 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 6843899 * (3 : ZMod 448521808841) ^ 6843899) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 437391113789 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 448521808841) ^ 27375598 = 382469388523 := by
        calc
          (3 : ZMod 448521808841) ^ 27375598 = (3 : ZMod 448521808841) ^ (13687799 + 13687799) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 13687799 * (3 : ZMod 448521808841) ^ 13687799 := by rw [pow_add]
          _ = 382469388523 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 448521808841) ^ 54751197 = 105952727415 := by
        calc
          (3 : ZMod 448521808841) ^ 54751197 = (3 : ZMod 448521808841) ^ (27375598 + 27375598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 27375598 * (3 : ZMod 448521808841) ^ 27375598) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 105952727415 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 448521808841) ^ 109502394 = 212296971345 := by
        calc
          (3 : ZMod 448521808841) ^ 109502394 = (3 : ZMod 448521808841) ^ (54751197 + 54751197) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 54751197 * (3 : ZMod 448521808841) ^ 54751197 := by rw [pow_add]
          _ = 212296971345 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 448521808841) ^ 219004789 = 418603621030 := by
        calc
          (3 : ZMod 448521808841) ^ 219004789 = (3 : ZMod 448521808841) ^ (109502394 + 109502394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 109502394 * (3 : ZMod 448521808841) ^ 109502394) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 418603621030 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 448521808841) ^ 438009578 = 422494610851 := by
        calc
          (3 : ZMod 448521808841) ^ 438009578 = (3 : ZMod 448521808841) ^ (219004789 + 219004789) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 219004789 * (3 : ZMod 448521808841) ^ 219004789 := by rw [pow_add]
          _ = 422494610851 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 448521808841) ^ 876019157 = 210008048216 := by
        calc
          (3 : ZMod 448521808841) ^ 876019157 = (3 : ZMod 448521808841) ^ (438009578 + 438009578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 438009578 * (3 : ZMod 448521808841) ^ 438009578) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 210008048216 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 448521808841) ^ 1752038315 = 229026283642 := by
        calc
          (3 : ZMod 448521808841) ^ 1752038315 = (3 : ZMod 448521808841) ^ (876019157 + 876019157 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 876019157 * (3 : ZMod 448521808841) ^ 876019157) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 229026283642 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 448521808841) ^ 3504076631 = 369646764674 := by
        calc
          (3 : ZMod 448521808841) ^ 3504076631 = (3 : ZMod 448521808841) ^ (1752038315 + 1752038315 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1752038315 * (3 : ZMod 448521808841) ^ 1752038315) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 369646764674 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 448521808841) ^ 7008153263 = 88319921638 := by
        calc
          (3 : ZMod 448521808841) ^ 7008153263 = (3 : ZMod 448521808841) ^ (3504076631 + 3504076631 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3504076631 * (3 : ZMod 448521808841) ^ 3504076631) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 88319921638 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 448521808841) ^ 14016306526 = 200254836829 := by
        calc
          (3 : ZMod 448521808841) ^ 14016306526 = (3 : ZMod 448521808841) ^ (7008153263 + 7008153263) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 7008153263 * (3 : ZMod 448521808841) ^ 7008153263 := by rw [pow_add]
          _ = 200254836829 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 448521808841) ^ 28032613052 = 186493730988 := by
        calc
          (3 : ZMod 448521808841) ^ 28032613052 = (3 : ZMod 448521808841) ^ (14016306526 + 14016306526) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 14016306526 * (3 : ZMod 448521808841) ^ 14016306526 := by rw [pow_add]
          _ = 186493730988 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 448521808841) ^ 56065226105 = 350424712214 := by
        calc
          (3 : ZMod 448521808841) ^ 56065226105 = (3 : ZMod 448521808841) ^ (28032613052 + 28032613052 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 28032613052 * (3 : ZMod 448521808841) ^ 28032613052) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 350424712214 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 448521808841) ^ 112130452210 = 3244848715 := by
        calc
          (3 : ZMod 448521808841) ^ 112130452210 = (3 : ZMod 448521808841) ^ (56065226105 + 56065226105) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 56065226105 * (3 : ZMod 448521808841) ^ 56065226105 := by rw [pow_add]
          _ = 3244848715 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 448521808841) ^ 224260904420 = 448521808840 := by
        calc
          (3 : ZMod 448521808841) ^ 224260904420 = (3 : ZMod 448521808841) ^ (112130452210 + 112130452210) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 112130452210 * (3 : ZMod 448521808841) ^ 112130452210 := by rw [pow_add]
          _ = 448521808840 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 448521808841) ^ 448521808840 = 1 := by
        calc
          (3 : ZMod 448521808841) ^ 448521808840 = (3 : ZMod 448521808841) ^ (224260904420 + 224260904420) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 224260904420 * (3 : ZMod 448521808841) ^ 224260904420 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (22907, 1), (69929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (22907, 1), (69929, 1)] : List FactorBlock).map factorBlockValue).prod = 448521808841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 448521808841) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 448521808841) ^ 3 = 27 := by
        calc
          (3 : ZMod 448521808841) ^ 3 = (3 : ZMod 448521808841) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1 * (3 : ZMod 448521808841) ^ 1) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 448521808841) ^ 6 = 729 := by
        calc
          (3 : ZMod 448521808841) ^ 6 = (3 : ZMod 448521808841) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 3 * (3 : ZMod 448521808841) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 448521808841) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 448521808841) ^ 13 = (3 : ZMod 448521808841) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 6 * (3 : ZMod 448521808841) ^ 6) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 448521808841) ^ 26 = 299256784124 := by
        calc
          (3 : ZMod 448521808841) ^ 26 = (3 : ZMod 448521808841) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 13 * (3 : ZMod 448521808841) ^ 13 := by rw [pow_add]
          _ = 299256784124 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 448521808841) ^ 52 = 288937088314 := by
        calc
          (3 : ZMod 448521808841) ^ 52 = (3 : ZMod 448521808841) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 26 * (3 : ZMod 448521808841) ^ 26 := by rw [pow_add]
          _ = 288937088314 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 448521808841) ^ 104 = 188734132322 := by
        calc
          (3 : ZMod 448521808841) ^ 104 = (3 : ZMod 448521808841) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 52 * (3 : ZMod 448521808841) ^ 52 := by rw [pow_add]
          _ = 188734132322 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 448521808841) ^ 208 = 46144353638 := by
        calc
          (3 : ZMod 448521808841) ^ 208 = (3 : ZMod 448521808841) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 104 * (3 : ZMod 448521808841) ^ 104 := by rw [pow_add]
          _ = 46144353638 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 448521808841) ^ 417 = 53844686086 := by
        calc
          (3 : ZMod 448521808841) ^ 417 = (3 : ZMod 448521808841) ^ (208 + 208 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 208 * (3 : ZMod 448521808841) ^ 208) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 53844686086 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 448521808841) ^ 835 = 285049105611 := by
        calc
          (3 : ZMod 448521808841) ^ 835 = (3 : ZMod 448521808841) ^ (417 + 417 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 417 * (3 : ZMod 448521808841) ^ 417) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 285049105611 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 448521808841) ^ 1670 = 314907313613 := by
        calc
          (3 : ZMod 448521808841) ^ 1670 = (3 : ZMod 448521808841) ^ (835 + 835) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 835 * (3 : ZMod 448521808841) ^ 835 := by rw [pow_add]
          _ = 314907313613 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 448521808841) ^ 3341 = 223806904395 := by
        calc
          (3 : ZMod 448521808841) ^ 3341 = (3 : ZMod 448521808841) ^ (1670 + 1670 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1670 * (3 : ZMod 448521808841) ^ 1670) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 223806904395 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 448521808841) ^ 6683 = 317660942126 := by
        calc
          (3 : ZMod 448521808841) ^ 6683 = (3 : ZMod 448521808841) ^ (3341 + 3341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3341 * (3 : ZMod 448521808841) ^ 3341) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 317660942126 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 448521808841) ^ 13366 = 195028067687 := by
        calc
          (3 : ZMod 448521808841) ^ 13366 = (3 : ZMod 448521808841) ^ (6683 + 6683) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 6683 * (3 : ZMod 448521808841) ^ 6683 := by rw [pow_add]
          _ = 195028067687 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 448521808841) ^ 26733 = 293899804340 := by
        calc
          (3 : ZMod 448521808841) ^ 26733 = (3 : ZMod 448521808841) ^ (13366 + 13366 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 13366 * (3 : ZMod 448521808841) ^ 13366) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 293899804340 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 448521808841) ^ 53467 = 280879181495 := by
        calc
          (3 : ZMod 448521808841) ^ 53467 = (3 : ZMod 448521808841) ^ (26733 + 26733 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 26733 * (3 : ZMod 448521808841) ^ 26733) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 280879181495 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 448521808841) ^ 106935 = 207018257262 := by
        calc
          (3 : ZMod 448521808841) ^ 106935 = (3 : ZMod 448521808841) ^ (53467 + 53467 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 53467 * (3 : ZMod 448521808841) ^ 53467) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 207018257262 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 448521808841) ^ 213871 = 39531638307 := by
        calc
          (3 : ZMod 448521808841) ^ 213871 = (3 : ZMod 448521808841) ^ (106935 + 106935 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 106935 * (3 : ZMod 448521808841) ^ 106935) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 39531638307 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 448521808841) ^ 427743 = 359703932466 := by
        calc
          (3 : ZMod 448521808841) ^ 427743 = (3 : ZMod 448521808841) ^ (213871 + 213871 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 213871 * (3 : ZMod 448521808841) ^ 213871) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 359703932466 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 448521808841) ^ 855487 = 320967201498 := by
        calc
          (3 : ZMod 448521808841) ^ 855487 = (3 : ZMod 448521808841) ^ (427743 + 427743 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 427743 * (3 : ZMod 448521808841) ^ 427743) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 320967201498 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 448521808841) ^ 1710974 = 443981763510 := by
        calc
          (3 : ZMod 448521808841) ^ 1710974 = (3 : ZMod 448521808841) ^ (855487 + 855487) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 855487 * (3 : ZMod 448521808841) ^ 855487 := by rw [pow_add]
          _ = 443981763510 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 448521808841) ^ 3421949 = 193259490680 := by
        calc
          (3 : ZMod 448521808841) ^ 3421949 = (3 : ZMod 448521808841) ^ (1710974 + 1710974 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1710974 * (3 : ZMod 448521808841) ^ 1710974) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 193259490680 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 448521808841) ^ 6843899 = 257211520379 := by
        calc
          (3 : ZMod 448521808841) ^ 6843899 = (3 : ZMod 448521808841) ^ (3421949 + 3421949 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3421949 * (3 : ZMod 448521808841) ^ 3421949) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 257211520379 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 448521808841) ^ 13687799 = 437391113789 := by
        calc
          (3 : ZMod 448521808841) ^ 13687799 = (3 : ZMod 448521808841) ^ (6843899 + 6843899 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 6843899 * (3 : ZMod 448521808841) ^ 6843899) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 437391113789 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 448521808841) ^ 27375598 = 382469388523 := by
        calc
          (3 : ZMod 448521808841) ^ 27375598 = (3 : ZMod 448521808841) ^ (13687799 + 13687799) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 13687799 * (3 : ZMod 448521808841) ^ 13687799 := by rw [pow_add]
          _ = 382469388523 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 448521808841) ^ 54751197 = 105952727415 := by
        calc
          (3 : ZMod 448521808841) ^ 54751197 = (3 : ZMod 448521808841) ^ (27375598 + 27375598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 27375598 * (3 : ZMod 448521808841) ^ 27375598) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 105952727415 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 448521808841) ^ 109502394 = 212296971345 := by
        calc
          (3 : ZMod 448521808841) ^ 109502394 = (3 : ZMod 448521808841) ^ (54751197 + 54751197) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 54751197 * (3 : ZMod 448521808841) ^ 54751197 := by rw [pow_add]
          _ = 212296971345 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 448521808841) ^ 219004789 = 418603621030 := by
        calc
          (3 : ZMod 448521808841) ^ 219004789 = (3 : ZMod 448521808841) ^ (109502394 + 109502394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 109502394 * (3 : ZMod 448521808841) ^ 109502394) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 418603621030 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 448521808841) ^ 438009578 = 422494610851 := by
        calc
          (3 : ZMod 448521808841) ^ 438009578 = (3 : ZMod 448521808841) ^ (219004789 + 219004789) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 219004789 * (3 : ZMod 448521808841) ^ 219004789 := by rw [pow_add]
          _ = 422494610851 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 448521808841) ^ 876019157 = 210008048216 := by
        calc
          (3 : ZMod 448521808841) ^ 876019157 = (3 : ZMod 448521808841) ^ (438009578 + 438009578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 438009578 * (3 : ZMod 448521808841) ^ 438009578) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 210008048216 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 448521808841) ^ 1752038315 = 229026283642 := by
        calc
          (3 : ZMod 448521808841) ^ 1752038315 = (3 : ZMod 448521808841) ^ (876019157 + 876019157 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 876019157 * (3 : ZMod 448521808841) ^ 876019157) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 229026283642 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 448521808841) ^ 3504076631 = 369646764674 := by
        calc
          (3 : ZMod 448521808841) ^ 3504076631 = (3 : ZMod 448521808841) ^ (1752038315 + 1752038315 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1752038315 * (3 : ZMod 448521808841) ^ 1752038315) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 369646764674 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 448521808841) ^ 7008153263 = 88319921638 := by
        calc
          (3 : ZMod 448521808841) ^ 7008153263 = (3 : ZMod 448521808841) ^ (3504076631 + 3504076631 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3504076631 * (3 : ZMod 448521808841) ^ 3504076631) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 88319921638 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 448521808841) ^ 14016306526 = 200254836829 := by
        calc
          (3 : ZMod 448521808841) ^ 14016306526 = (3 : ZMod 448521808841) ^ (7008153263 + 7008153263) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 7008153263 * (3 : ZMod 448521808841) ^ 7008153263 := by rw [pow_add]
          _ = 200254836829 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 448521808841) ^ 28032613052 = 186493730988 := by
        calc
          (3 : ZMod 448521808841) ^ 28032613052 = (3 : ZMod 448521808841) ^ (14016306526 + 14016306526) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 14016306526 * (3 : ZMod 448521808841) ^ 14016306526 := by rw [pow_add]
          _ = 186493730988 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 448521808841) ^ 56065226105 = 350424712214 := by
        calc
          (3 : ZMod 448521808841) ^ 56065226105 = (3 : ZMod 448521808841) ^ (28032613052 + 28032613052 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 28032613052 * (3 : ZMod 448521808841) ^ 28032613052) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 350424712214 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 448521808841) ^ 112130452210 = 3244848715 := by
        calc
          (3 : ZMod 448521808841) ^ 112130452210 = (3 : ZMod 448521808841) ^ (56065226105 + 56065226105) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 56065226105 * (3 : ZMod 448521808841) ^ 56065226105 := by rw [pow_add]
          _ = 3244848715 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 448521808841) ^ 224260904420 = 448521808840 := by
        calc
          (3 : ZMod 448521808841) ^ 224260904420 = (3 : ZMod 448521808841) ^ (112130452210 + 112130452210) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 112130452210 * (3 : ZMod 448521808841) ^ 112130452210 := by rw [pow_add]
          _ = 448521808840 := by rw [factor_0_36]; decide
      change (3 : ZMod 448521808841) ^ 224260904420 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (3 : ZMod 448521808841) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 448521808841) ^ 2 = 9 := by
        calc
          (3 : ZMod 448521808841) ^ 2 = (3 : ZMod 448521808841) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 1 * (3 : ZMod 448521808841) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 448521808841) ^ 5 = 243 := by
        calc
          (3 : ZMod 448521808841) ^ 5 = (3 : ZMod 448521808841) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 2 * (3 : ZMod 448521808841) ^ 2) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 448521808841) ^ 10 = 59049 := by
        calc
          (3 : ZMod 448521808841) ^ 10 = (3 : ZMod 448521808841) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 5 * (3 : ZMod 448521808841) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 448521808841) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 448521808841) ^ 20 = (3 : ZMod 448521808841) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 10 * (3 : ZMod 448521808841) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 448521808841) ^ 41 = 353996785701 := by
        calc
          (3 : ZMod 448521808841) ^ 41 = (3 : ZMod 448521808841) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 20 * (3 : ZMod 448521808841) ^ 20) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 353996785701 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 448521808841) ^ 83 = 435321972894 := by
        calc
          (3 : ZMod 448521808841) ^ 83 = (3 : ZMod 448521808841) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 41 * (3 : ZMod 448521808841) ^ 41) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 435321972894 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 448521808841) ^ 167 = 91365051876 := by
        calc
          (3 : ZMod 448521808841) ^ 167 = (3 : ZMod 448521808841) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 83 * (3 : ZMod 448521808841) ^ 83) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 91365051876 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 448521808841) ^ 334 = 444816602854 := by
        calc
          (3 : ZMod 448521808841) ^ 334 = (3 : ZMod 448521808841) ^ (167 + 167) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 167 * (3 : ZMod 448521808841) ^ 167 := by rw [pow_add]
          _ = 444816602854 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 448521808841) ^ 668 = 325586661493 := by
        calc
          (3 : ZMod 448521808841) ^ 668 = (3 : ZMod 448521808841) ^ (334 + 334) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 334 * (3 : ZMod 448521808841) ^ 334 := by rw [pow_add]
          _ = 325586661493 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 448521808841) ^ 1336 = 56522339920 := by
        calc
          (3 : ZMod 448521808841) ^ 1336 = (3 : ZMod 448521808841) ^ (668 + 668) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 668 * (3 : ZMod 448521808841) ^ 668 := by rw [pow_add]
          _ = 56522339920 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 448521808841) ^ 2673 = 364774319199 := by
        calc
          (3 : ZMod 448521808841) ^ 2673 = (3 : ZMod 448521808841) ^ (1336 + 1336 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1336 * (3 : ZMod 448521808841) ^ 1336) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 364774319199 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 448521808841) ^ 5346 = 368932698806 := by
        calc
          (3 : ZMod 448521808841) ^ 5346 = (3 : ZMod 448521808841) ^ (2673 + 2673) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 2673 * (3 : ZMod 448521808841) ^ 2673 := by rw [pow_add]
          _ = 368932698806 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 448521808841) ^ 10693 = 69370559910 := by
        calc
          (3 : ZMod 448521808841) ^ 10693 = (3 : ZMod 448521808841) ^ (5346 + 5346 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 5346 * (3 : ZMod 448521808841) ^ 5346) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 69370559910 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 448521808841) ^ 21387 = 71350120938 := by
        calc
          (3 : ZMod 448521808841) ^ 21387 = (3 : ZMod 448521808841) ^ (10693 + 10693 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 10693 * (3 : ZMod 448521808841) ^ 10693) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 71350120938 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 448521808841) ^ 42774 = 67830080720 := by
        calc
          (3 : ZMod 448521808841) ^ 42774 = (3 : ZMod 448521808841) ^ (21387 + 21387) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 21387 * (3 : ZMod 448521808841) ^ 21387 := by rw [pow_add]
          _ = 67830080720 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 448521808841) ^ 85548 = 259271948841 := by
        calc
          (3 : ZMod 448521808841) ^ 85548 = (3 : ZMod 448521808841) ^ (42774 + 42774) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 42774 * (3 : ZMod 448521808841) ^ 42774 := by rw [pow_add]
          _ = 259271948841 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 448521808841) ^ 171097 = 358549406296 := by
        calc
          (3 : ZMod 448521808841) ^ 171097 = (3 : ZMod 448521808841) ^ (85548 + 85548 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 85548 * (3 : ZMod 448521808841) ^ 85548) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 358549406296 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 448521808841) ^ 342194 = 2068011857 := by
        calc
          (3 : ZMod 448521808841) ^ 342194 = (3 : ZMod 448521808841) ^ (171097 + 171097) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 171097 * (3 : ZMod 448521808841) ^ 171097 := by rw [pow_add]
          _ = 2068011857 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 448521808841) ^ 684389 = 303129325950 := by
        calc
          (3 : ZMod 448521808841) ^ 684389 = (3 : ZMod 448521808841) ^ (342194 + 342194 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 342194 * (3 : ZMod 448521808841) ^ 342194) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 303129325950 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 448521808841) ^ 1368779 = 407211400244 := by
        calc
          (3 : ZMod 448521808841) ^ 1368779 = (3 : ZMod 448521808841) ^ (684389 + 684389 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 684389 * (3 : ZMod 448521808841) ^ 684389) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 407211400244 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 448521808841) ^ 2737559 = 80172906370 := by
        calc
          (3 : ZMod 448521808841) ^ 2737559 = (3 : ZMod 448521808841) ^ (1368779 + 1368779 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1368779 * (3 : ZMod 448521808841) ^ 1368779) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 80172906370 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 448521808841) ^ 5475119 = 151106556881 := by
        calc
          (3 : ZMod 448521808841) ^ 5475119 = (3 : ZMod 448521808841) ^ (2737559 + 2737559 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 2737559 * (3 : ZMod 448521808841) ^ 2737559) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 151106556881 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 448521808841) ^ 10950239 = 383112201114 := by
        calc
          (3 : ZMod 448521808841) ^ 10950239 = (3 : ZMod 448521808841) ^ (5475119 + 5475119 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 5475119 * (3 : ZMod 448521808841) ^ 5475119) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 383112201114 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 448521808841) ^ 21900478 = 425244294031 := by
        calc
          (3 : ZMod 448521808841) ^ 21900478 = (3 : ZMod 448521808841) ^ (10950239 + 10950239) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 10950239 * (3 : ZMod 448521808841) ^ 10950239 := by rw [pow_add]
          _ = 425244294031 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 448521808841) ^ 43800957 = 104478915993 := by
        calc
          (3 : ZMod 448521808841) ^ 43800957 = (3 : ZMod 448521808841) ^ (21900478 + 21900478 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 21900478 * (3 : ZMod 448521808841) ^ 21900478) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 104478915993 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 448521808841) ^ 87601915 = 288699602954 := by
        calc
          (3 : ZMod 448521808841) ^ 87601915 = (3 : ZMod 448521808841) ^ (43800957 + 43800957 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 43800957 * (3 : ZMod 448521808841) ^ 43800957) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 288699602954 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 448521808841) ^ 175203831 = 6184686124 := by
        calc
          (3 : ZMod 448521808841) ^ 175203831 = (3 : ZMod 448521808841) ^ (87601915 + 87601915 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 87601915 * (3 : ZMod 448521808841) ^ 87601915) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 6184686124 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 448521808841) ^ 350407663 = 362603590156 := by
        calc
          (3 : ZMod 448521808841) ^ 350407663 = (3 : ZMod 448521808841) ^ (175203831 + 175203831 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 175203831 * (3 : ZMod 448521808841) ^ 175203831) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 362603590156 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 448521808841) ^ 700815326 = 150918879712 := by
        calc
          (3 : ZMod 448521808841) ^ 700815326 = (3 : ZMod 448521808841) ^ (350407663 + 350407663) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 350407663 * (3 : ZMod 448521808841) ^ 350407663 := by rw [pow_add]
          _ = 150918879712 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 448521808841) ^ 1401630652 = 63647116478 := by
        calc
          (3 : ZMod 448521808841) ^ 1401630652 = (3 : ZMod 448521808841) ^ (700815326 + 700815326) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 700815326 * (3 : ZMod 448521808841) ^ 700815326 := by rw [pow_add]
          _ = 63647116478 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 448521808841) ^ 2803261305 = 382611686558 := by
        calc
          (3 : ZMod 448521808841) ^ 2803261305 = (3 : ZMod 448521808841) ^ (1401630652 + 1401630652 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1401630652 * (3 : ZMod 448521808841) ^ 1401630652) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 382611686558 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 448521808841) ^ 5606522610 = 31081065128 := by
        calc
          (3 : ZMod 448521808841) ^ 5606522610 = (3 : ZMod 448521808841) ^ (2803261305 + 2803261305) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 2803261305 * (3 : ZMod 448521808841) ^ 2803261305 := by rw [pow_add]
          _ = 31081065128 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 448521808841) ^ 11213045221 = 436740608003 := by
        calc
          (3 : ZMod 448521808841) ^ 11213045221 = (3 : ZMod 448521808841) ^ (5606522610 + 5606522610 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 5606522610 * (3 : ZMod 448521808841) ^ 5606522610) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 436740608003 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 448521808841) ^ 22426090442 = 275714536234 := by
        calc
          (3 : ZMod 448521808841) ^ 22426090442 = (3 : ZMod 448521808841) ^ (11213045221 + 11213045221) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 11213045221 * (3 : ZMod 448521808841) ^ 11213045221 := by rw [pow_add]
          _ = 275714536234 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 448521808841) ^ 44852180884 = 398539758890 := by
        calc
          (3 : ZMod 448521808841) ^ 44852180884 = (3 : ZMod 448521808841) ^ (22426090442 + 22426090442) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 22426090442 * (3 : ZMod 448521808841) ^ 22426090442 := by rw [pow_add]
          _ = 398539758890 := by rw [factor_1_34]; decide
      have factor_1_36 : (3 : ZMod 448521808841) ^ 89704361768 = 251133616956 := by
        calc
          (3 : ZMod 448521808841) ^ 89704361768 = (3 : ZMod 448521808841) ^ (44852180884 + 44852180884) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 44852180884 * (3 : ZMod 448521808841) ^ 44852180884 := by rw [pow_add]
          _ = 251133616956 := by rw [factor_1_35]; decide
      change (3 : ZMod 448521808841) ^ 89704361768 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (3 : ZMod 448521808841) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 448521808841) ^ 3 = 27 := by
        calc
          (3 : ZMod 448521808841) ^ 3 = (3 : ZMod 448521808841) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1 * (3 : ZMod 448521808841) ^ 1) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 448521808841) ^ 7 = 2187 := by
        calc
          (3 : ZMod 448521808841) ^ 7 = (3 : ZMod 448521808841) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3 * (3 : ZMod 448521808841) ^ 3) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 448521808841) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 448521808841) ^ 14 = (3 : ZMod 448521808841) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 7 * (3 : ZMod 448521808841) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 448521808841) ^ 29 = 6540612210 := by
        calc
          (3 : ZMod 448521808841) ^ 29 = (3 : ZMod 448521808841) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 14 * (3 : ZMod 448521808841) ^ 14) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 6540612210 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 448521808841) ^ 59 = 386705294590 := by
        calc
          (3 : ZMod 448521808841) ^ 59 = (3 : ZMod 448521808841) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 29 * (3 : ZMod 448521808841) ^ 29) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 386705294590 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 448521808841) ^ 119 = 28378424677 := by
        calc
          (3 : ZMod 448521808841) ^ 119 = (3 : ZMod 448521808841) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 59 * (3 : ZMod 448521808841) ^ 59) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 28378424677 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 448521808841) ^ 238 = 274567535339 := by
        calc
          (3 : ZMod 448521808841) ^ 238 = (3 : ZMod 448521808841) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 119 * (3 : ZMod 448521808841) ^ 119 := by rw [pow_add]
          _ = 274567535339 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 448521808841) ^ 477 = 316191796535 := by
        calc
          (3 : ZMod 448521808841) ^ 477 = (3 : ZMod 448521808841) ^ (238 + 238 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 238 * (3 : ZMod 448521808841) ^ 238) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 316191796535 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 448521808841) ^ 954 = 244128529734 := by
        calc
          (3 : ZMod 448521808841) ^ 954 = (3 : ZMod 448521808841) ^ (477 + 477) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 477 * (3 : ZMod 448521808841) ^ 477 := by rw [pow_add]
          _ = 244128529734 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 448521808841) ^ 1909 = 266579555999 := by
        calc
          (3 : ZMod 448521808841) ^ 1909 = (3 : ZMod 448521808841) ^ (954 + 954 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 954 * (3 : ZMod 448521808841) ^ 954) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 266579555999 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 448521808841) ^ 3819 = 364996095082 := by
        calc
          (3 : ZMod 448521808841) ^ 3819 = (3 : ZMod 448521808841) ^ (1909 + 1909 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1909 * (3 : ZMod 448521808841) ^ 1909) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 364996095082 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 448521808841) ^ 7638 = 94447118912 := by
        calc
          (3 : ZMod 448521808841) ^ 7638 = (3 : ZMod 448521808841) ^ (3819 + 3819) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 3819 * (3 : ZMod 448521808841) ^ 3819 := by rw [pow_add]
          _ = 94447118912 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 448521808841) ^ 15276 = 373655655694 := by
        calc
          (3 : ZMod 448521808841) ^ 15276 = (3 : ZMod 448521808841) ^ (7638 + 7638) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 7638 * (3 : ZMod 448521808841) ^ 7638 := by rw [pow_add]
          _ = 373655655694 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 448521808841) ^ 30553 = 116964842243 := by
        calc
          (3 : ZMod 448521808841) ^ 30553 = (3 : ZMod 448521808841) ^ (15276 + 15276 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 15276 * (3 : ZMod 448521808841) ^ 15276) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 116964842243 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 448521808841) ^ 61106 = 129671585252 := by
        calc
          (3 : ZMod 448521808841) ^ 61106 = (3 : ZMod 448521808841) ^ (30553 + 30553) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 30553 * (3 : ZMod 448521808841) ^ 30553 := by rw [pow_add]
          _ = 129671585252 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 448521808841) ^ 122212 = 75708100519 := by
        calc
          (3 : ZMod 448521808841) ^ 122212 = (3 : ZMod 448521808841) ^ (61106 + 61106) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 61106 * (3 : ZMod 448521808841) ^ 61106 := by rw [pow_add]
          _ = 75708100519 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 448521808841) ^ 244424 = 425903141543 := by
        calc
          (3 : ZMod 448521808841) ^ 244424 = (3 : ZMod 448521808841) ^ (122212 + 122212) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 122212 * (3 : ZMod 448521808841) ^ 122212 := by rw [pow_add]
          _ = 425903141543 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 448521808841) ^ 488849 = 397582591896 := by
        calc
          (3 : ZMod 448521808841) ^ 488849 = (3 : ZMod 448521808841) ^ (244424 + 244424 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 244424 * (3 : ZMod 448521808841) ^ 244424) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 397582591896 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 448521808841) ^ 977699 = 137607713746 := by
        calc
          (3 : ZMod 448521808841) ^ 977699 = (3 : ZMod 448521808841) ^ (488849 + 488849 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 488849 * (3 : ZMod 448521808841) ^ 488849) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 137607713746 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 448521808841) ^ 1955399 = 14150615507 := by
        calc
          (3 : ZMod 448521808841) ^ 1955399 = (3 : ZMod 448521808841) ^ (977699 + 977699 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 977699 * (3 : ZMod 448521808841) ^ 977699) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 14150615507 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 448521808841) ^ 3910799 = 184102706981 := by
        calc
          (3 : ZMod 448521808841) ^ 3910799 = (3 : ZMod 448521808841) ^ (1955399 + 1955399 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1955399 * (3 : ZMod 448521808841) ^ 1955399) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 184102706981 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 448521808841) ^ 7821599 = 214384033198 := by
        calc
          (3 : ZMod 448521808841) ^ 7821599 = (3 : ZMod 448521808841) ^ (3910799 + 3910799 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3910799 * (3 : ZMod 448521808841) ^ 3910799) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 214384033198 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 448521808841) ^ 15643199 = 50912594804 := by
        calc
          (3 : ZMod 448521808841) ^ 15643199 = (3 : ZMod 448521808841) ^ (7821599 + 7821599 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 7821599 * (3 : ZMod 448521808841) ^ 7821599) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 50912594804 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 448521808841) ^ 31286398 = 380016143324 := by
        calc
          (3 : ZMod 448521808841) ^ 31286398 = (3 : ZMod 448521808841) ^ (15643199 + 15643199) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 15643199 * (3 : ZMod 448521808841) ^ 15643199 := by rw [pow_add]
          _ = 380016143324 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 448521808841) ^ 62572796 = 182244369970 := by
        calc
          (3 : ZMod 448521808841) ^ 62572796 = (3 : ZMod 448521808841) ^ (31286398 + 31286398) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 31286398 * (3 : ZMod 448521808841) ^ 31286398 := by rw [pow_add]
          _ = 182244369970 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 448521808841) ^ 125145593 = 56867547969 := by
        calc
          (3 : ZMod 448521808841) ^ 125145593 = (3 : ZMod 448521808841) ^ (62572796 + 62572796 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 62572796 * (3 : ZMod 448521808841) ^ 62572796) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 56867547969 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 448521808841) ^ 250291187 = 384519264924 := by
        calc
          (3 : ZMod 448521808841) ^ 250291187 = (3 : ZMod 448521808841) ^ (125145593 + 125145593 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 125145593 * (3 : ZMod 448521808841) ^ 125145593) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 384519264924 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 448521808841) ^ 500582375 = 399544831065 := by
        calc
          (3 : ZMod 448521808841) ^ 500582375 = (3 : ZMod 448521808841) ^ (250291187 + 250291187 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 250291187 * (3 : ZMod 448521808841) ^ 250291187) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 399544831065 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 448521808841) ^ 1001164751 = 136903261660 := by
        calc
          (3 : ZMod 448521808841) ^ 1001164751 = (3 : ZMod 448521808841) ^ (500582375 + 500582375 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 500582375 * (3 : ZMod 448521808841) ^ 500582375) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 136903261660 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 448521808841) ^ 2002329503 = 391251466388 := by
        calc
          (3 : ZMod 448521808841) ^ 2002329503 = (3 : ZMod 448521808841) ^ (1001164751 + 1001164751 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1001164751 * (3 : ZMod 448521808841) ^ 1001164751) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 391251466388 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 448521808841) ^ 4004659007 = 200535964832 := by
        calc
          (3 : ZMod 448521808841) ^ 4004659007 = (3 : ZMod 448521808841) ^ (2002329503 + 2002329503 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 2002329503 * (3 : ZMod 448521808841) ^ 2002329503) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 200535964832 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 448521808841) ^ 8009318015 = 289651257584 := by
        calc
          (3 : ZMod 448521808841) ^ 8009318015 = (3 : ZMod 448521808841) ^ (4004659007 + 4004659007 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 4004659007 * (3 : ZMod 448521808841) ^ 4004659007) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 289651257584 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 448521808841) ^ 16018636030 = 314738718647 := by
        calc
          (3 : ZMod 448521808841) ^ 16018636030 = (3 : ZMod 448521808841) ^ (8009318015 + 8009318015) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 8009318015 * (3 : ZMod 448521808841) ^ 8009318015 := by rw [pow_add]
          _ = 314738718647 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 448521808841) ^ 32037272060 = 54026657377 := by
        calc
          (3 : ZMod 448521808841) ^ 32037272060 = (3 : ZMod 448521808841) ^ (16018636030 + 16018636030) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 16018636030 * (3 : ZMod 448521808841) ^ 16018636030 := by rw [pow_add]
          _ = 54026657377 := by rw [factor_2_33]; decide
      have factor_2_35 : (3 : ZMod 448521808841) ^ 64074544120 = 283836894625 := by
        calc
          (3 : ZMod 448521808841) ^ 64074544120 = (3 : ZMod 448521808841) ^ (32037272060 + 32037272060) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 32037272060 * (3 : ZMod 448521808841) ^ 32037272060 := by rw [pow_add]
          _ = 283836894625 := by rw [factor_2_34]; decide
      change (3 : ZMod 448521808841) ^ 64074544120 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (3 : ZMod 448521808841) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 448521808841) ^ 2 = 9 := by
        calc
          (3 : ZMod 448521808841) ^ 2 = (3 : ZMod 448521808841) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 1 * (3 : ZMod 448521808841) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 448521808841) ^ 4 = 81 := by
        calc
          (3 : ZMod 448521808841) ^ 4 = (3 : ZMod 448521808841) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 2 * (3 : ZMod 448521808841) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 448521808841) ^ 9 = 19683 := by
        calc
          (3 : ZMod 448521808841) ^ 9 = (3 : ZMod 448521808841) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 4 * (3 : ZMod 448521808841) ^ 4) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 448521808841) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 448521808841) ^ 18 = (3 : ZMod 448521808841) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 9 * (3 : ZMod 448521808841) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 448521808841) ^ 37 = 303384869915 := by
        calc
          (3 : ZMod 448521808841) ^ 37 = (3 : ZMod 448521808841) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 18 * (3 : ZMod 448521808841) ^ 18) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 303384869915 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 448521808841) ^ 74 = 6243040989 := by
        calc
          (3 : ZMod 448521808841) ^ 74 = (3 : ZMod 448521808841) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 37 * (3 : ZMod 448521808841) ^ 37 := by rw [pow_add]
          _ = 6243040989 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 448521808841) ^ 149 = 322264812348 := by
        calc
          (3 : ZMod 448521808841) ^ 149 = (3 : ZMod 448521808841) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 74 * (3 : ZMod 448521808841) ^ 74) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 322264812348 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 448521808841) ^ 298 = 410471029483 := by
        calc
          (3 : ZMod 448521808841) ^ 298 = (3 : ZMod 448521808841) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 149 * (3 : ZMod 448521808841) ^ 149 := by rw [pow_add]
          _ = 410471029483 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 448521808841) ^ 597 = 371687360540 := by
        calc
          (3 : ZMod 448521808841) ^ 597 = (3 : ZMod 448521808841) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 298 * (3 : ZMod 448521808841) ^ 298) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 371687360540 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 448521808841) ^ 1195 = 256704030143 := by
        calc
          (3 : ZMod 448521808841) ^ 1195 = (3 : ZMod 448521808841) ^ (597 + 597 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 597 * (3 : ZMod 448521808841) ^ 597) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 256704030143 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 448521808841) ^ 2390 = 297908212122 := by
        calc
          (3 : ZMod 448521808841) ^ 2390 = (3 : ZMod 448521808841) ^ (1195 + 1195) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 1195 * (3 : ZMod 448521808841) ^ 1195 := by rw [pow_add]
          _ = 297908212122 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 448521808841) ^ 4780 = 360759083546 := by
        calc
          (3 : ZMod 448521808841) ^ 4780 = (3 : ZMod 448521808841) ^ (2390 + 2390) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 2390 * (3 : ZMod 448521808841) ^ 2390 := by rw [pow_add]
          _ = 360759083546 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 448521808841) ^ 9560 = 69069687339 := by
        calc
          (3 : ZMod 448521808841) ^ 9560 = (3 : ZMod 448521808841) ^ (4780 + 4780) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 4780 * (3 : ZMod 448521808841) ^ 4780 := by rw [pow_add]
          _ = 69069687339 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 448521808841) ^ 19121 = 243474743150 := by
        calc
          (3 : ZMod 448521808841) ^ 19121 = (3 : ZMod 448521808841) ^ (9560 + 9560 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 9560 * (3 : ZMod 448521808841) ^ 9560) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 243474743150 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 448521808841) ^ 38242 = 15466133023 := by
        calc
          (3 : ZMod 448521808841) ^ 38242 = (3 : ZMod 448521808841) ^ (19121 + 19121) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 19121 * (3 : ZMod 448521808841) ^ 19121 := by rw [pow_add]
          _ = 15466133023 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 448521808841) ^ 76484 = 306555948576 := by
        calc
          (3 : ZMod 448521808841) ^ 76484 = (3 : ZMod 448521808841) ^ (38242 + 38242) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 38242 * (3 : ZMod 448521808841) ^ 38242 := by rw [pow_add]
          _ = 306555948576 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 448521808841) ^ 152969 = 172118137302 := by
        calc
          (3 : ZMod 448521808841) ^ 152969 = (3 : ZMod 448521808841) ^ (76484 + 76484 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 76484 * (3 : ZMod 448521808841) ^ 76484) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 172118137302 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 448521808841) ^ 305939 = 99638471194 := by
        calc
          (3 : ZMod 448521808841) ^ 305939 = (3 : ZMod 448521808841) ^ (152969 + 152969 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 152969 * (3 : ZMod 448521808841) ^ 152969) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 99638471194 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 448521808841) ^ 611878 = 135853679315 := by
        calc
          (3 : ZMod 448521808841) ^ 611878 = (3 : ZMod 448521808841) ^ (305939 + 305939) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 305939 * (3 : ZMod 448521808841) ^ 305939 := by rw [pow_add]
          _ = 135853679315 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 448521808841) ^ 1223757 = 82803427317 := by
        calc
          (3 : ZMod 448521808841) ^ 1223757 = (3 : ZMod 448521808841) ^ (611878 + 611878 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 611878 * (3 : ZMod 448521808841) ^ 611878) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 82803427317 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 448521808841) ^ 2447515 = 362021833396 := by
        calc
          (3 : ZMod 448521808841) ^ 2447515 = (3 : ZMod 448521808841) ^ (1223757 + 1223757 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1223757 * (3 : ZMod 448521808841) ^ 1223757) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 362021833396 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 448521808841) ^ 4895030 = 20491035138 := by
        calc
          (3 : ZMod 448521808841) ^ 4895030 = (3 : ZMod 448521808841) ^ (2447515 + 2447515) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 2447515 * (3 : ZMod 448521808841) ^ 2447515 := by rw [pow_add]
          _ = 20491035138 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 448521808841) ^ 9790060 = 322169604054 := by
        calc
          (3 : ZMod 448521808841) ^ 9790060 = (3 : ZMod 448521808841) ^ (4895030 + 4895030) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 4895030 * (3 : ZMod 448521808841) ^ 4895030 := by rw [pow_add]
          _ = 322169604054 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 448521808841) ^ 19580120 = 400436408287 := by
        calc
          (3 : ZMod 448521808841) ^ 19580120 = (3 : ZMod 448521808841) ^ (9790060 + 9790060) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 9790060 * (3 : ZMod 448521808841) ^ 9790060 := by rw [pow_add]
          _ = 400436408287 := by rw [factor_3_23]; decide
      change (3 : ZMod 448521808841) ^ 19580120 ≠ 1
      rw [factor_3_24]
      decide
    ·
      have factor_4_0 : (3 : ZMod 448521808841) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 448521808841) ^ 3 = 27 := by
        calc
          (3 : ZMod 448521808841) ^ 3 = (3 : ZMod 448521808841) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1 * (3 : ZMod 448521808841) ^ 1) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 448521808841) ^ 6 = 729 := by
        calc
          (3 : ZMod 448521808841) ^ 6 = (3 : ZMod 448521808841) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 3 * (3 : ZMod 448521808841) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 448521808841) ^ 12 = 531441 := by
        calc
          (3 : ZMod 448521808841) ^ 12 = (3 : ZMod 448521808841) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 6 * (3 : ZMod 448521808841) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 448521808841) ^ 24 = 282429536481 := by
        calc
          (3 : ZMod 448521808841) ^ 24 = (3 : ZMod 448521808841) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 12 * (3 : ZMod 448521808841) ^ 12 := by rw [pow_add]
          _ = 282429536481 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 448521808841) ^ 48 = 42328268521 := by
        calc
          (3 : ZMod 448521808841) ^ 48 = (3 : ZMod 448521808841) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 24 * (3 : ZMod 448521808841) ^ 24 := by rw [pow_add]
          _ = 42328268521 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 448521808841) ^ 97 = 420716490199 := by
        calc
          (3 : ZMod 448521808841) ^ 97 = (3 : ZMod 448521808841) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 48 * (3 : ZMod 448521808841) ^ 48) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 420716490199 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 448521808841) ^ 195 = 367564298756 := by
        calc
          (3 : ZMod 448521808841) ^ 195 = (3 : ZMod 448521808841) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 97 * (3 : ZMod 448521808841) ^ 97) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 367564298756 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 448521808841) ^ 391 = 286736533158 := by
        calc
          (3 : ZMod 448521808841) ^ 391 = (3 : ZMod 448521808841) ^ (195 + 195 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 195 * (3 : ZMod 448521808841) ^ 195) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 286736533158 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 448521808841) ^ 782 = 116535194538 := by
        calc
          (3 : ZMod 448521808841) ^ 782 = (3 : ZMod 448521808841) ^ (391 + 391) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 391 * (3 : ZMod 448521808841) ^ 391 := by rw [pow_add]
          _ = 116535194538 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 448521808841) ^ 1565 = 122305334608 := by
        calc
          (3 : ZMod 448521808841) ^ 1565 = (3 : ZMod 448521808841) ^ (782 + 782 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 782 * (3 : ZMod 448521808841) ^ 782) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 122305334608 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 448521808841) ^ 3131 = 144835669936 := by
        calc
          (3 : ZMod 448521808841) ^ 3131 = (3 : ZMod 448521808841) ^ (1565 + 1565 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 1565 * (3 : ZMod 448521808841) ^ 1565) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 144835669936 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 448521808841) ^ 6263 = 401118203602 := by
        calc
          (3 : ZMod 448521808841) ^ 6263 = (3 : ZMod 448521808841) ^ (3131 + 3131 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 3131 * (3 : ZMod 448521808841) ^ 3131) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 401118203602 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 448521808841) ^ 12527 = 357105023536 := by
        calc
          (3 : ZMod 448521808841) ^ 12527 = (3 : ZMod 448521808841) ^ (6263 + 6263 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 6263 * (3 : ZMod 448521808841) ^ 6263) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 357105023536 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 448521808841) ^ 25054 = 208658427509 := by
        calc
          (3 : ZMod 448521808841) ^ 25054 = (3 : ZMod 448521808841) ^ (12527 + 12527) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 12527 * (3 : ZMod 448521808841) ^ 12527 := by rw [pow_add]
          _ = 208658427509 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 448521808841) ^ 50109 = 293911696355 := by
        calc
          (3 : ZMod 448521808841) ^ 50109 = (3 : ZMod 448521808841) ^ (25054 + 25054 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 25054 * (3 : ZMod 448521808841) ^ 25054) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 293911696355 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 448521808841) ^ 100218 = 53805190610 := by
        calc
          (3 : ZMod 448521808841) ^ 100218 = (3 : ZMod 448521808841) ^ (50109 + 50109) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 50109 * (3 : ZMod 448521808841) ^ 50109 := by rw [pow_add]
          _ = 53805190610 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 448521808841) ^ 200436 = 72114635884 := by
        calc
          (3 : ZMod 448521808841) ^ 200436 = (3 : ZMod 448521808841) ^ (100218 + 100218) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 100218 * (3 : ZMod 448521808841) ^ 100218 := by rw [pow_add]
          _ = 72114635884 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 448521808841) ^ 400872 = 62354483448 := by
        calc
          (3 : ZMod 448521808841) ^ 400872 = (3 : ZMod 448521808841) ^ (200436 + 200436) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 200436 * (3 : ZMod 448521808841) ^ 200436 := by rw [pow_add]
          _ = 62354483448 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 448521808841) ^ 801745 = 108441308180 := by
        calc
          (3 : ZMod 448521808841) ^ 801745 = (3 : ZMod 448521808841) ^ (400872 + 400872 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = ((3 : ZMod 448521808841) ^ 400872 * (3 : ZMod 448521808841) ^ 400872) * (3 : ZMod 448521808841) := by rw [pow_succ, pow_add]
          _ = 108441308180 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 448521808841) ^ 1603490 = 21059191884 := by
        calc
          (3 : ZMod 448521808841) ^ 1603490 = (3 : ZMod 448521808841) ^ (801745 + 801745) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 801745 * (3 : ZMod 448521808841) ^ 801745 := by rw [pow_add]
          _ = 21059191884 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 448521808841) ^ 3206980 = 17127365240 := by
        calc
          (3 : ZMod 448521808841) ^ 3206980 = (3 : ZMod 448521808841) ^ (1603490 + 1603490) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 1603490 * (3 : ZMod 448521808841) ^ 1603490 := by rw [pow_add]
          _ = 17127365240 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 448521808841) ^ 6413960 = 367919383616 := by
        calc
          (3 : ZMod 448521808841) ^ 6413960 = (3 : ZMod 448521808841) ^ (3206980 + 3206980) :=
            congrArg (fun n : ℕ => (3 : ZMod 448521808841) ^ n) (by norm_num)
          _ = (3 : ZMod 448521808841) ^ 3206980 * (3 : ZMod 448521808841) ^ 3206980 := by rw [pow_add]
          _ = 367919383616 := by rw [factor_4_21]; decide
      change (3 : ZMod 448521808841) ^ 6413960 ≠ 1
      rw [factor_4_22]
      decide

#print axioms prime_lucas_448521808841

end TotientTailPeriodKiller
end Erdos249257
