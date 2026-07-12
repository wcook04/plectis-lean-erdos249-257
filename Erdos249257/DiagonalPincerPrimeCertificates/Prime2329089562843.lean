import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime255550753

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2329089562843 : Nat.Prime 2329089562843 := by
  apply lucas_primality 2329089562843 (2 : ZMod 2329089562843)
  ·
      have fermat_0 : (2 : ZMod 2329089562843) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 2329089562843) ^ 2 = 4 := by
        calc
          (2 : ZMod 2329089562843) ^ 2 = (2 : ZMod 2329089562843) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1 * (2 : ZMod 2329089562843) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 2329089562843) ^ 4 = 16 := by
        calc
          (2 : ZMod 2329089562843) ^ 4 = (2 : ZMod 2329089562843) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2 * (2 : ZMod 2329089562843) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 2329089562843) ^ 8 = 256 := by
        calc
          (2 : ZMod 2329089562843) ^ 8 = (2 : ZMod 2329089562843) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4 * (2 : ZMod 2329089562843) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 2329089562843) ^ 16 = 65536 := by
        calc
          (2 : ZMod 2329089562843) ^ 16 = (2 : ZMod 2329089562843) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 8 * (2 : ZMod 2329089562843) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 2329089562843) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 2329089562843) ^ 33 = (2 : ZMod 2329089562843) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 16 * (2 : ZMod 2329089562843) ^ 16) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 2329089562843) ^ 67 = 1056856390154 := by
        calc
          (2 : ZMod 2329089562843) ^ 67 = (2 : ZMod 2329089562843) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 33 * (2 : ZMod 2329089562843) ^ 33) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1056856390154 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 2329089562843) ^ 135 = 743124746080 := by
        calc
          (2 : ZMod 2329089562843) ^ 135 = (2 : ZMod 2329089562843) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 67 * (2 : ZMod 2329089562843) ^ 67) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 743124746080 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 2329089562843) ^ 271 = 350172561459 := by
        calc
          (2 : ZMod 2329089562843) ^ 271 = (2 : ZMod 2329089562843) ^ (135 + 135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 135 * (2 : ZMod 2329089562843) ^ 135) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 350172561459 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 2329089562843) ^ 542 = 2146552171829 := by
        calc
          (2 : ZMod 2329089562843) ^ 542 = (2 : ZMod 2329089562843) ^ (271 + 271) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 271 * (2 : ZMod 2329089562843) ^ 271 := by rw [pow_add]
          _ = 2146552171829 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 2329089562843) ^ 1084 = 489867469984 := by
        calc
          (2 : ZMod 2329089562843) ^ 1084 = (2 : ZMod 2329089562843) ^ (542 + 542) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 542 * (2 : ZMod 2329089562843) ^ 542 := by rw [pow_add]
          _ = 489867469984 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 2329089562843) ^ 2169 = 1081715727514 := by
        calc
          (2 : ZMod 2329089562843) ^ 2169 = (2 : ZMod 2329089562843) ^ (1084 + 1084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 1084 * (2 : ZMod 2329089562843) ^ 1084) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1081715727514 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 2329089562843) ^ 4338 = 433155888352 := by
        calc
          (2 : ZMod 2329089562843) ^ 4338 = (2 : ZMod 2329089562843) ^ (2169 + 2169) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2169 * (2 : ZMod 2329089562843) ^ 2169 := by rw [pow_add]
          _ = 433155888352 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 2329089562843) ^ 8676 = 1849925332270 := by
        calc
          (2 : ZMod 2329089562843) ^ 8676 = (2 : ZMod 2329089562843) ^ (4338 + 4338) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4338 * (2 : ZMod 2329089562843) ^ 4338 := by rw [pow_add]
          _ = 1849925332270 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 2329089562843) ^ 17353 = 1283690241728 := by
        calc
          (2 : ZMod 2329089562843) ^ 17353 = (2 : ZMod 2329089562843) ^ (8676 + 8676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 8676 * (2 : ZMod 2329089562843) ^ 8676) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1283690241728 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 2329089562843) ^ 34706 = 520280740606 := by
        calc
          (2 : ZMod 2329089562843) ^ 34706 = (2 : ZMod 2329089562843) ^ (17353 + 17353) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 17353 * (2 : ZMod 2329089562843) ^ 17353 := by rw [pow_add]
          _ = 520280740606 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 2329089562843) ^ 69412 = 1109329173391 := by
        calc
          (2 : ZMod 2329089562843) ^ 69412 = (2 : ZMod 2329089562843) ^ (34706 + 34706) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 34706 * (2 : ZMod 2329089562843) ^ 34706 := by rw [pow_add]
          _ = 1109329173391 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 2329089562843) ^ 138824 = 1906370669353 := by
        calc
          (2 : ZMod 2329089562843) ^ 138824 = (2 : ZMod 2329089562843) ^ (69412 + 69412) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 69412 * (2 : ZMod 2329089562843) ^ 69412 := by rw [pow_add]
          _ = 1906370669353 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 2329089562843) ^ 277649 = 2156853016147 := by
        calc
          (2 : ZMod 2329089562843) ^ 277649 = (2 : ZMod 2329089562843) ^ (138824 + 138824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 138824 * (2 : ZMod 2329089562843) ^ 138824) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2156853016147 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 2329089562843) ^ 555298 = 724734245666 := by
        calc
          (2 : ZMod 2329089562843) ^ 555298 = (2 : ZMod 2329089562843) ^ (277649 + 277649) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 277649 * (2 : ZMod 2329089562843) ^ 277649 := by rw [pow_add]
          _ = 724734245666 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 2329089562843) ^ 1110596 = 909380393466 := by
        calc
          (2 : ZMod 2329089562843) ^ 1110596 = (2 : ZMod 2329089562843) ^ (555298 + 555298) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 555298 * (2 : ZMod 2329089562843) ^ 555298 := by rw [pow_add]
          _ = 909380393466 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 2329089562843) ^ 2221192 = 1010962097336 := by
        calc
          (2 : ZMod 2329089562843) ^ 2221192 = (2 : ZMod 2329089562843) ^ (1110596 + 1110596) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1110596 * (2 : ZMod 2329089562843) ^ 1110596 := by rw [pow_add]
          _ = 1010962097336 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 2329089562843) ^ 4442385 = 185530540228 := by
        calc
          (2 : ZMod 2329089562843) ^ 4442385 = (2 : ZMod 2329089562843) ^ (2221192 + 2221192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 2221192 * (2 : ZMod 2329089562843) ^ 2221192) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 185530540228 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 2329089562843) ^ 8884771 = 86081139652 := by
        calc
          (2 : ZMod 2329089562843) ^ 8884771 = (2 : ZMod 2329089562843) ^ (4442385 + 4442385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 4442385 * (2 : ZMod 2329089562843) ^ 4442385) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 86081139652 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 2329089562843) ^ 17769543 = 1593719981219 := by
        calc
          (2 : ZMod 2329089562843) ^ 17769543 = (2 : ZMod 2329089562843) ^ (8884771 + 8884771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 8884771 * (2 : ZMod 2329089562843) ^ 8884771) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1593719981219 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 2329089562843) ^ 35539086 = 1326056745177 := by
        calc
          (2 : ZMod 2329089562843) ^ 35539086 = (2 : ZMod 2329089562843) ^ (17769543 + 17769543) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 17769543 * (2 : ZMod 2329089562843) ^ 17769543 := by rw [pow_add]
          _ = 1326056745177 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 2329089562843) ^ 71078172 = 1167663267838 := by
        calc
          (2 : ZMod 2329089562843) ^ 71078172 = (2 : ZMod 2329089562843) ^ (35539086 + 35539086) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 35539086 * (2 : ZMod 2329089562843) ^ 35539086 := by rw [pow_add]
          _ = 1167663267838 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 2329089562843) ^ 142156345 = 1383034332328 := by
        calc
          (2 : ZMod 2329089562843) ^ 142156345 = (2 : ZMod 2329089562843) ^ (71078172 + 71078172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 71078172 * (2 : ZMod 2329089562843) ^ 71078172) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1383034332328 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 2329089562843) ^ 284312690 = 1051011238358 := by
        calc
          (2 : ZMod 2329089562843) ^ 284312690 = (2 : ZMod 2329089562843) ^ (142156345 + 142156345) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 142156345 * (2 : ZMod 2329089562843) ^ 142156345 := by rw [pow_add]
          _ = 1051011238358 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 2329089562843) ^ 568625381 = 442794569722 := by
        calc
          (2 : ZMod 2329089562843) ^ 568625381 = (2 : ZMod 2329089562843) ^ (284312690 + 284312690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 284312690 * (2 : ZMod 2329089562843) ^ 284312690) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 442794569722 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 2329089562843) ^ 1137250763 = 907369370865 := by
        calc
          (2 : ZMod 2329089562843) ^ 1137250763 = (2 : ZMod 2329089562843) ^ (568625381 + 568625381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 568625381 * (2 : ZMod 2329089562843) ^ 568625381) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 907369370865 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 2329089562843) ^ 2274501526 = 412622242984 := by
        calc
          (2 : ZMod 2329089562843) ^ 2274501526 = (2 : ZMod 2329089562843) ^ (1137250763 + 1137250763) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1137250763 * (2 : ZMod 2329089562843) ^ 1137250763 := by rw [pow_add]
          _ = 412622242984 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 2329089562843) ^ 4549003052 = 1124704671290 := by
        calc
          (2 : ZMod 2329089562843) ^ 4549003052 = (2 : ZMod 2329089562843) ^ (2274501526 + 2274501526) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2274501526 * (2 : ZMod 2329089562843) ^ 2274501526 := by rw [pow_add]
          _ = 1124704671290 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 2329089562843) ^ 9098006104 = 1615238502695 := by
        calc
          (2 : ZMod 2329089562843) ^ 9098006104 = (2 : ZMod 2329089562843) ^ (4549003052 + 4549003052) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4549003052 * (2 : ZMod 2329089562843) ^ 4549003052 := by rw [pow_add]
          _ = 1615238502695 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 2329089562843) ^ 18196012209 = 2048791318685 := by
        calc
          (2 : ZMod 2329089562843) ^ 18196012209 = (2 : ZMod 2329089562843) ^ (9098006104 + 9098006104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 9098006104 * (2 : ZMod 2329089562843) ^ 9098006104) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2048791318685 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 2329089562843) ^ 36392024419 = 2313131125456 := by
        calc
          (2 : ZMod 2329089562843) ^ 36392024419 = (2 : ZMod 2329089562843) ^ (18196012209 + 18196012209 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 18196012209 * (2 : ZMod 2329089562843) ^ 18196012209) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2313131125456 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 2329089562843) ^ 72784048838 = 1558788057127 := by
        calc
          (2 : ZMod 2329089562843) ^ 72784048838 = (2 : ZMod 2329089562843) ^ (36392024419 + 36392024419) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 36392024419 * (2 : ZMod 2329089562843) ^ 36392024419 := by rw [pow_add]
          _ = 1558788057127 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 2329089562843) ^ 145568097677 = 1672714008582 := by
        calc
          (2 : ZMod 2329089562843) ^ 145568097677 = (2 : ZMod 2329089562843) ^ (72784048838 + 72784048838 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 72784048838 * (2 : ZMod 2329089562843) ^ 72784048838) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1672714008582 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 2329089562843) ^ 291136195355 = 1568857744271 := by
        calc
          (2 : ZMod 2329089562843) ^ 291136195355 = (2 : ZMod 2329089562843) ^ (145568097677 + 145568097677 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 145568097677 * (2 : ZMod 2329089562843) ^ 145568097677) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1568857744271 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 2329089562843) ^ 582272390710 = 1507298319142 := by
        calc
          (2 : ZMod 2329089562843) ^ 582272390710 = (2 : ZMod 2329089562843) ^ (291136195355 + 291136195355) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 291136195355 * (2 : ZMod 2329089562843) ^ 291136195355 := by rw [pow_add]
          _ = 1507298319142 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 2329089562843) ^ 1164544781421 = 2329089562842 := by
        calc
          (2 : ZMod 2329089562843) ^ 1164544781421 = (2 : ZMod 2329089562843) ^ (582272390710 + 582272390710 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 582272390710 * (2 : ZMod 2329089562843) ^ 582272390710) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2329089562842 := by rw [fermat_39]; decide
      have fermat_41 : (2 : ZMod 2329089562843) ^ 2329089562842 = 1 := by
        calc
          (2 : ZMod 2329089562843) ^ 2329089562842 = (2 : ZMod 2329089562843) ^ (1164544781421 + 1164544781421) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1164544781421 * (2 : ZMod 2329089562843) ^ 1164544781421 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (31, 1), (255550753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (31, 1), (255550753, 1)] : List FactorBlock).map factorBlockValue).prod = 2329089562843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_255550753) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 2329089562843) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 2329089562843) ^ 2 = 4 := by
        calc
          (2 : ZMod 2329089562843) ^ 2 = (2 : ZMod 2329089562843) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1 * (2 : ZMod 2329089562843) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 2329089562843) ^ 4 = 16 := by
        calc
          (2 : ZMod 2329089562843) ^ 4 = (2 : ZMod 2329089562843) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2 * (2 : ZMod 2329089562843) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 2329089562843) ^ 8 = 256 := by
        calc
          (2 : ZMod 2329089562843) ^ 8 = (2 : ZMod 2329089562843) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4 * (2 : ZMod 2329089562843) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 2329089562843) ^ 16 = 65536 := by
        calc
          (2 : ZMod 2329089562843) ^ 16 = (2 : ZMod 2329089562843) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 8 * (2 : ZMod 2329089562843) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 2329089562843) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 2329089562843) ^ 33 = (2 : ZMod 2329089562843) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 16 * (2 : ZMod 2329089562843) ^ 16) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 2329089562843) ^ 67 = 1056856390154 := by
        calc
          (2 : ZMod 2329089562843) ^ 67 = (2 : ZMod 2329089562843) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 33 * (2 : ZMod 2329089562843) ^ 33) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1056856390154 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 2329089562843) ^ 135 = 743124746080 := by
        calc
          (2 : ZMod 2329089562843) ^ 135 = (2 : ZMod 2329089562843) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 67 * (2 : ZMod 2329089562843) ^ 67) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 743124746080 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 2329089562843) ^ 271 = 350172561459 := by
        calc
          (2 : ZMod 2329089562843) ^ 271 = (2 : ZMod 2329089562843) ^ (135 + 135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 135 * (2 : ZMod 2329089562843) ^ 135) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 350172561459 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 2329089562843) ^ 542 = 2146552171829 := by
        calc
          (2 : ZMod 2329089562843) ^ 542 = (2 : ZMod 2329089562843) ^ (271 + 271) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 271 * (2 : ZMod 2329089562843) ^ 271 := by rw [pow_add]
          _ = 2146552171829 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 2329089562843) ^ 1084 = 489867469984 := by
        calc
          (2 : ZMod 2329089562843) ^ 1084 = (2 : ZMod 2329089562843) ^ (542 + 542) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 542 * (2 : ZMod 2329089562843) ^ 542 := by rw [pow_add]
          _ = 489867469984 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 2329089562843) ^ 2169 = 1081715727514 := by
        calc
          (2 : ZMod 2329089562843) ^ 2169 = (2 : ZMod 2329089562843) ^ (1084 + 1084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 1084 * (2 : ZMod 2329089562843) ^ 1084) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1081715727514 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 2329089562843) ^ 4338 = 433155888352 := by
        calc
          (2 : ZMod 2329089562843) ^ 4338 = (2 : ZMod 2329089562843) ^ (2169 + 2169) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2169 * (2 : ZMod 2329089562843) ^ 2169 := by rw [pow_add]
          _ = 433155888352 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 2329089562843) ^ 8676 = 1849925332270 := by
        calc
          (2 : ZMod 2329089562843) ^ 8676 = (2 : ZMod 2329089562843) ^ (4338 + 4338) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4338 * (2 : ZMod 2329089562843) ^ 4338 := by rw [pow_add]
          _ = 1849925332270 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 2329089562843) ^ 17353 = 1283690241728 := by
        calc
          (2 : ZMod 2329089562843) ^ 17353 = (2 : ZMod 2329089562843) ^ (8676 + 8676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 8676 * (2 : ZMod 2329089562843) ^ 8676) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1283690241728 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 2329089562843) ^ 34706 = 520280740606 := by
        calc
          (2 : ZMod 2329089562843) ^ 34706 = (2 : ZMod 2329089562843) ^ (17353 + 17353) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 17353 * (2 : ZMod 2329089562843) ^ 17353 := by rw [pow_add]
          _ = 520280740606 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 2329089562843) ^ 69412 = 1109329173391 := by
        calc
          (2 : ZMod 2329089562843) ^ 69412 = (2 : ZMod 2329089562843) ^ (34706 + 34706) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 34706 * (2 : ZMod 2329089562843) ^ 34706 := by rw [pow_add]
          _ = 1109329173391 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 2329089562843) ^ 138824 = 1906370669353 := by
        calc
          (2 : ZMod 2329089562843) ^ 138824 = (2 : ZMod 2329089562843) ^ (69412 + 69412) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 69412 * (2 : ZMod 2329089562843) ^ 69412 := by rw [pow_add]
          _ = 1906370669353 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 2329089562843) ^ 277649 = 2156853016147 := by
        calc
          (2 : ZMod 2329089562843) ^ 277649 = (2 : ZMod 2329089562843) ^ (138824 + 138824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 138824 * (2 : ZMod 2329089562843) ^ 138824) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2156853016147 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 2329089562843) ^ 555298 = 724734245666 := by
        calc
          (2 : ZMod 2329089562843) ^ 555298 = (2 : ZMod 2329089562843) ^ (277649 + 277649) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 277649 * (2 : ZMod 2329089562843) ^ 277649 := by rw [pow_add]
          _ = 724734245666 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 2329089562843) ^ 1110596 = 909380393466 := by
        calc
          (2 : ZMod 2329089562843) ^ 1110596 = (2 : ZMod 2329089562843) ^ (555298 + 555298) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 555298 * (2 : ZMod 2329089562843) ^ 555298 := by rw [pow_add]
          _ = 909380393466 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 2329089562843) ^ 2221192 = 1010962097336 := by
        calc
          (2 : ZMod 2329089562843) ^ 2221192 = (2 : ZMod 2329089562843) ^ (1110596 + 1110596) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1110596 * (2 : ZMod 2329089562843) ^ 1110596 := by rw [pow_add]
          _ = 1010962097336 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 2329089562843) ^ 4442385 = 185530540228 := by
        calc
          (2 : ZMod 2329089562843) ^ 4442385 = (2 : ZMod 2329089562843) ^ (2221192 + 2221192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 2221192 * (2 : ZMod 2329089562843) ^ 2221192) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 185530540228 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 2329089562843) ^ 8884771 = 86081139652 := by
        calc
          (2 : ZMod 2329089562843) ^ 8884771 = (2 : ZMod 2329089562843) ^ (4442385 + 4442385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 4442385 * (2 : ZMod 2329089562843) ^ 4442385) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 86081139652 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 2329089562843) ^ 17769543 = 1593719981219 := by
        calc
          (2 : ZMod 2329089562843) ^ 17769543 = (2 : ZMod 2329089562843) ^ (8884771 + 8884771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 8884771 * (2 : ZMod 2329089562843) ^ 8884771) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1593719981219 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 2329089562843) ^ 35539086 = 1326056745177 := by
        calc
          (2 : ZMod 2329089562843) ^ 35539086 = (2 : ZMod 2329089562843) ^ (17769543 + 17769543) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 17769543 * (2 : ZMod 2329089562843) ^ 17769543 := by rw [pow_add]
          _ = 1326056745177 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 2329089562843) ^ 71078172 = 1167663267838 := by
        calc
          (2 : ZMod 2329089562843) ^ 71078172 = (2 : ZMod 2329089562843) ^ (35539086 + 35539086) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 35539086 * (2 : ZMod 2329089562843) ^ 35539086 := by rw [pow_add]
          _ = 1167663267838 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 2329089562843) ^ 142156345 = 1383034332328 := by
        calc
          (2 : ZMod 2329089562843) ^ 142156345 = (2 : ZMod 2329089562843) ^ (71078172 + 71078172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 71078172 * (2 : ZMod 2329089562843) ^ 71078172) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1383034332328 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 2329089562843) ^ 284312690 = 1051011238358 := by
        calc
          (2 : ZMod 2329089562843) ^ 284312690 = (2 : ZMod 2329089562843) ^ (142156345 + 142156345) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 142156345 * (2 : ZMod 2329089562843) ^ 142156345 := by rw [pow_add]
          _ = 1051011238358 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 2329089562843) ^ 568625381 = 442794569722 := by
        calc
          (2 : ZMod 2329089562843) ^ 568625381 = (2 : ZMod 2329089562843) ^ (284312690 + 284312690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 284312690 * (2 : ZMod 2329089562843) ^ 284312690) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 442794569722 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 2329089562843) ^ 1137250763 = 907369370865 := by
        calc
          (2 : ZMod 2329089562843) ^ 1137250763 = (2 : ZMod 2329089562843) ^ (568625381 + 568625381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 568625381 * (2 : ZMod 2329089562843) ^ 568625381) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 907369370865 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 2329089562843) ^ 2274501526 = 412622242984 := by
        calc
          (2 : ZMod 2329089562843) ^ 2274501526 = (2 : ZMod 2329089562843) ^ (1137250763 + 1137250763) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1137250763 * (2 : ZMod 2329089562843) ^ 1137250763 := by rw [pow_add]
          _ = 412622242984 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 2329089562843) ^ 4549003052 = 1124704671290 := by
        calc
          (2 : ZMod 2329089562843) ^ 4549003052 = (2 : ZMod 2329089562843) ^ (2274501526 + 2274501526) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2274501526 * (2 : ZMod 2329089562843) ^ 2274501526 := by rw [pow_add]
          _ = 1124704671290 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 2329089562843) ^ 9098006104 = 1615238502695 := by
        calc
          (2 : ZMod 2329089562843) ^ 9098006104 = (2 : ZMod 2329089562843) ^ (4549003052 + 4549003052) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4549003052 * (2 : ZMod 2329089562843) ^ 4549003052 := by rw [pow_add]
          _ = 1615238502695 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 2329089562843) ^ 18196012209 = 2048791318685 := by
        calc
          (2 : ZMod 2329089562843) ^ 18196012209 = (2 : ZMod 2329089562843) ^ (9098006104 + 9098006104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 9098006104 * (2 : ZMod 2329089562843) ^ 9098006104) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2048791318685 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 2329089562843) ^ 36392024419 = 2313131125456 := by
        calc
          (2 : ZMod 2329089562843) ^ 36392024419 = (2 : ZMod 2329089562843) ^ (18196012209 + 18196012209 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 18196012209 * (2 : ZMod 2329089562843) ^ 18196012209) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2313131125456 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 2329089562843) ^ 72784048838 = 1558788057127 := by
        calc
          (2 : ZMod 2329089562843) ^ 72784048838 = (2 : ZMod 2329089562843) ^ (36392024419 + 36392024419) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 36392024419 * (2 : ZMod 2329089562843) ^ 36392024419 := by rw [pow_add]
          _ = 1558788057127 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 2329089562843) ^ 145568097677 = 1672714008582 := by
        calc
          (2 : ZMod 2329089562843) ^ 145568097677 = (2 : ZMod 2329089562843) ^ (72784048838 + 72784048838 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 72784048838 * (2 : ZMod 2329089562843) ^ 72784048838) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1672714008582 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 2329089562843) ^ 291136195355 = 1568857744271 := by
        calc
          (2 : ZMod 2329089562843) ^ 291136195355 = (2 : ZMod 2329089562843) ^ (145568097677 + 145568097677 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 145568097677 * (2 : ZMod 2329089562843) ^ 145568097677) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1568857744271 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 2329089562843) ^ 582272390710 = 1507298319142 := by
        calc
          (2 : ZMod 2329089562843) ^ 582272390710 = (2 : ZMod 2329089562843) ^ (291136195355 + 291136195355) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 291136195355 * (2 : ZMod 2329089562843) ^ 291136195355 := by rw [pow_add]
          _ = 1507298319142 := by rw [factor_0_38]; decide
      have factor_0_40 : (2 : ZMod 2329089562843) ^ 1164544781421 = 2329089562842 := by
        calc
          (2 : ZMod 2329089562843) ^ 1164544781421 = (2 : ZMod 2329089562843) ^ (582272390710 + 582272390710 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 582272390710 * (2 : ZMod 2329089562843) ^ 582272390710) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2329089562842 := by rw [factor_0_39]; decide
      change (2 : ZMod 2329089562843) ^ 1164544781421 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (2 : ZMod 2329089562843) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 2329089562843) ^ 2 = 4 := by
        calc
          (2 : ZMod 2329089562843) ^ 2 = (2 : ZMod 2329089562843) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1 * (2 : ZMod 2329089562843) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 2329089562843) ^ 5 = 32 := by
        calc
          (2 : ZMod 2329089562843) ^ 5 = (2 : ZMod 2329089562843) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 2 * (2 : ZMod 2329089562843) ^ 2) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 2329089562843) ^ 11 = 2048 := by
        calc
          (2 : ZMod 2329089562843) ^ 11 = (2 : ZMod 2329089562843) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 5 * (2 : ZMod 2329089562843) ^ 5) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 2329089562843) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 2329089562843) ^ 22 = (2 : ZMod 2329089562843) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 11 * (2 : ZMod 2329089562843) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 2329089562843) ^ 45 = 248028646187 := by
        calc
          (2 : ZMod 2329089562843) ^ 45 = (2 : ZMod 2329089562843) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 22 * (2 : ZMod 2329089562843) ^ 22) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 248028646187 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 2329089562843) ^ 90 = 319171479654 := by
        calc
          (2 : ZMod 2329089562843) ^ 90 = (2 : ZMod 2329089562843) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 45 * (2 : ZMod 2329089562843) ^ 45 := by rw [pow_add]
          _ = 319171479654 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 2329089562843) ^ 180 = 416649104643 := by
        calc
          (2 : ZMod 2329089562843) ^ 180 = (2 : ZMod 2329089562843) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 90 * (2 : ZMod 2329089562843) ^ 90 := by rw [pow_add]
          _ = 416649104643 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 2329089562843) ^ 361 = 1872384716286 := by
        calc
          (2 : ZMod 2329089562843) ^ 361 = (2 : ZMod 2329089562843) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 180 * (2 : ZMod 2329089562843) ^ 180) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1872384716286 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 2329089562843) ^ 723 = 1518466126170 := by
        calc
          (2 : ZMod 2329089562843) ^ 723 = (2 : ZMod 2329089562843) ^ (361 + 361 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 361 * (2 : ZMod 2329089562843) ^ 361) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1518466126170 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 2329089562843) ^ 1446 = 1178082572983 := by
        calc
          (2 : ZMod 2329089562843) ^ 1446 = (2 : ZMod 2329089562843) ^ (723 + 723) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 723 * (2 : ZMod 2329089562843) ^ 723 := by rw [pow_add]
          _ = 1178082572983 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 2329089562843) ^ 2892 = 820498205997 := by
        calc
          (2 : ZMod 2329089562843) ^ 2892 = (2 : ZMod 2329089562843) ^ (1446 + 1446) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1446 * (2 : ZMod 2329089562843) ^ 1446 := by rw [pow_add]
          _ = 820498205997 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 2329089562843) ^ 5784 = 1939656035494 := by
        calc
          (2 : ZMod 2329089562843) ^ 5784 = (2 : ZMod 2329089562843) ^ (2892 + 2892) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2892 * (2 : ZMod 2329089562843) ^ 2892 := by rw [pow_add]
          _ = 1939656035494 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 2329089562843) ^ 11568 = 1938958822898 := by
        calc
          (2 : ZMod 2329089562843) ^ 11568 = (2 : ZMod 2329089562843) ^ (5784 + 5784) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 5784 * (2 : ZMod 2329089562843) ^ 5784 := by rw [pow_add]
          _ = 1938958822898 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 2329089562843) ^ 23137 = 932183031032 := by
        calc
          (2 : ZMod 2329089562843) ^ 23137 = (2 : ZMod 2329089562843) ^ (11568 + 11568 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 11568 * (2 : ZMod 2329089562843) ^ 11568) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 932183031032 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 2329089562843) ^ 46274 = 1226780569305 := by
        calc
          (2 : ZMod 2329089562843) ^ 46274 = (2 : ZMod 2329089562843) ^ (23137 + 23137) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 23137 * (2 : ZMod 2329089562843) ^ 23137 := by rw [pow_add]
          _ = 1226780569305 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 2329089562843) ^ 92549 = 1003340802709 := by
        calc
          (2 : ZMod 2329089562843) ^ 92549 = (2 : ZMod 2329089562843) ^ (46274 + 46274 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 46274 * (2 : ZMod 2329089562843) ^ 46274) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1003340802709 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 2329089562843) ^ 185099 = 2089132608885 := by
        calc
          (2 : ZMod 2329089562843) ^ 185099 = (2 : ZMod 2329089562843) ^ (92549 + 92549 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 92549 * (2 : ZMod 2329089562843) ^ 92549) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2089132608885 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 2329089562843) ^ 370198 = 1402336727146 := by
        calc
          (2 : ZMod 2329089562843) ^ 370198 = (2 : ZMod 2329089562843) ^ (185099 + 185099) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 185099 * (2 : ZMod 2329089562843) ^ 185099 := by rw [pow_add]
          _ = 1402336727146 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 2329089562843) ^ 740397 = 265802664289 := by
        calc
          (2 : ZMod 2329089562843) ^ 740397 = (2 : ZMod 2329089562843) ^ (370198 + 370198 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 370198 * (2 : ZMod 2329089562843) ^ 370198) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 265802664289 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 2329089562843) ^ 1480795 = 481402916262 := by
        calc
          (2 : ZMod 2329089562843) ^ 1480795 = (2 : ZMod 2329089562843) ^ (740397 + 740397 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 740397 * (2 : ZMod 2329089562843) ^ 740397) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 481402916262 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 2329089562843) ^ 2961590 = 143133762304 := by
        calc
          (2 : ZMod 2329089562843) ^ 2961590 = (2 : ZMod 2329089562843) ^ (1480795 + 1480795) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1480795 * (2 : ZMod 2329089562843) ^ 1480795 := by rw [pow_add]
          _ = 143133762304 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 2329089562843) ^ 5923181 = 594314432112 := by
        calc
          (2 : ZMod 2329089562843) ^ 5923181 = (2 : ZMod 2329089562843) ^ (2961590 + 2961590 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 2961590 * (2 : ZMod 2329089562843) ^ 2961590) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 594314432112 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 2329089562843) ^ 11846362 = 1317423004732 := by
        calc
          (2 : ZMod 2329089562843) ^ 11846362 = (2 : ZMod 2329089562843) ^ (5923181 + 5923181) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 5923181 * (2 : ZMod 2329089562843) ^ 5923181 := by rw [pow_add]
          _ = 1317423004732 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 2329089562843) ^ 23692724 = 388516612348 := by
        calc
          (2 : ZMod 2329089562843) ^ 23692724 = (2 : ZMod 2329089562843) ^ (11846362 + 11846362) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 11846362 * (2 : ZMod 2329089562843) ^ 11846362 := by rw [pow_add]
          _ = 388516612348 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 2329089562843) ^ 47385448 = 1249242916013 := by
        calc
          (2 : ZMod 2329089562843) ^ 47385448 = (2 : ZMod 2329089562843) ^ (23692724 + 23692724) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 23692724 * (2 : ZMod 2329089562843) ^ 23692724 := by rw [pow_add]
          _ = 1249242916013 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 2329089562843) ^ 94770896 = 574108964356 := by
        calc
          (2 : ZMod 2329089562843) ^ 94770896 = (2 : ZMod 2329089562843) ^ (47385448 + 47385448) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 47385448 * (2 : ZMod 2329089562843) ^ 47385448 := by rw [pow_add]
          _ = 574108964356 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 2329089562843) ^ 189541793 = 246824975859 := by
        calc
          (2 : ZMod 2329089562843) ^ 189541793 = (2 : ZMod 2329089562843) ^ (94770896 + 94770896 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 94770896 * (2 : ZMod 2329089562843) ^ 94770896) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 246824975859 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 2329089562843) ^ 379083587 = 1161945803298 := by
        calc
          (2 : ZMod 2329089562843) ^ 379083587 = (2 : ZMod 2329089562843) ^ (189541793 + 189541793 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 189541793 * (2 : ZMod 2329089562843) ^ 189541793) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1161945803298 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 2329089562843) ^ 758167175 = 1798751385043 := by
        calc
          (2 : ZMod 2329089562843) ^ 758167175 = (2 : ZMod 2329089562843) ^ (379083587 + 379083587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 379083587 * (2 : ZMod 2329089562843) ^ 379083587) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1798751385043 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 2329089562843) ^ 1516334350 = 139125421946 := by
        calc
          (2 : ZMod 2329089562843) ^ 1516334350 = (2 : ZMod 2329089562843) ^ (758167175 + 758167175) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 758167175 * (2 : ZMod 2329089562843) ^ 758167175 := by rw [pow_add]
          _ = 139125421946 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 2329089562843) ^ 3032668701 = 784239939325 := by
        calc
          (2 : ZMod 2329089562843) ^ 3032668701 = (2 : ZMod 2329089562843) ^ (1516334350 + 1516334350 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 1516334350 * (2 : ZMod 2329089562843) ^ 1516334350) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 784239939325 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 2329089562843) ^ 6065337403 = 341910244304 := by
        calc
          (2 : ZMod 2329089562843) ^ 6065337403 = (2 : ZMod 2329089562843) ^ (3032668701 + 3032668701 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 3032668701 * (2 : ZMod 2329089562843) ^ 3032668701) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 341910244304 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 2329089562843) ^ 12130674806 = 2089819646978 := by
        calc
          (2 : ZMod 2329089562843) ^ 12130674806 = (2 : ZMod 2329089562843) ^ (6065337403 + 6065337403) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 6065337403 * (2 : ZMod 2329089562843) ^ 6065337403 := by rw [pow_add]
          _ = 2089819646978 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 2329089562843) ^ 24261349612 = 136943759880 := by
        calc
          (2 : ZMod 2329089562843) ^ 24261349612 = (2 : ZMod 2329089562843) ^ (12130674806 + 12130674806) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 12130674806 * (2 : ZMod 2329089562843) ^ 12130674806 := by rw [pow_add]
          _ = 136943759880 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 2329089562843) ^ 48522699225 = 198670302382 := by
        calc
          (2 : ZMod 2329089562843) ^ 48522699225 = (2 : ZMod 2329089562843) ^ (24261349612 + 24261349612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 24261349612 * (2 : ZMod 2329089562843) ^ 24261349612) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 198670302382 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 2329089562843) ^ 97045398451 = 115899580031 := by
        calc
          (2 : ZMod 2329089562843) ^ 97045398451 = (2 : ZMod 2329089562843) ^ (48522699225 + 48522699225 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 48522699225 * (2 : ZMod 2329089562843) ^ 48522699225) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 115899580031 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 2329089562843) ^ 194090796903 = 866715828651 := by
        calc
          (2 : ZMod 2329089562843) ^ 194090796903 = (2 : ZMod 2329089562843) ^ (97045398451 + 97045398451 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 97045398451 * (2 : ZMod 2329089562843) ^ 97045398451) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 866715828651 := by rw [factor_1_36]; decide
      have factor_1_38 : (2 : ZMod 2329089562843) ^ 388181593807 = 293637684047 := by
        calc
          (2 : ZMod 2329089562843) ^ 388181593807 = (2 : ZMod 2329089562843) ^ (194090796903 + 194090796903 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 194090796903 * (2 : ZMod 2329089562843) ^ 194090796903) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 293637684047 := by rw [factor_1_37]; decide
      have factor_1_39 : (2 : ZMod 2329089562843) ^ 776363187614 = 293637684046 := by
        calc
          (2 : ZMod 2329089562843) ^ 776363187614 = (2 : ZMod 2329089562843) ^ (388181593807 + 388181593807) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 388181593807 * (2 : ZMod 2329089562843) ^ 388181593807 := by rw [pow_add]
          _ = 293637684046 := by rw [factor_1_38]; decide
      change (2 : ZMod 2329089562843) ^ 776363187614 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (2 : ZMod 2329089562843) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 2329089562843) ^ 2 = 4 := by
        calc
          (2 : ZMod 2329089562843) ^ 2 = (2 : ZMod 2329089562843) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1 * (2 : ZMod 2329089562843) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 2329089562843) ^ 4 = 16 := by
        calc
          (2 : ZMod 2329089562843) ^ 4 = (2 : ZMod 2329089562843) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2 * (2 : ZMod 2329089562843) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 2329089562843) ^ 9 = 512 := by
        calc
          (2 : ZMod 2329089562843) ^ 9 = (2 : ZMod 2329089562843) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 4 * (2 : ZMod 2329089562843) ^ 4) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 2329089562843) ^ 19 = 524288 := by
        calc
          (2 : ZMod 2329089562843) ^ 19 = (2 : ZMod 2329089562843) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 9 * (2 : ZMod 2329089562843) ^ 9) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 2329089562843) ^ 38 = 274877906944 := by
        calc
          (2 : ZMod 2329089562843) ^ 38 = (2 : ZMod 2329089562843) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 19 * (2 : ZMod 2329089562843) ^ 19 := by rw [pow_add]
          _ = 274877906944 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 2329089562843) ^ 77 = 1523386358544 := by
        calc
          (2 : ZMod 2329089562843) ^ 77 = (2 : ZMod 2329089562843) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 38 * (2 : ZMod 2329089562843) ^ 38) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1523386358544 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 2329089562843) ^ 154 = 1284800414000 := by
        calc
          (2 : ZMod 2329089562843) ^ 154 = (2 : ZMod 2329089562843) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 77 * (2 : ZMod 2329089562843) ^ 77 := by rw [pow_add]
          _ = 1284800414000 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 2329089562843) ^ 309 = 166237674070 := by
        calc
          (2 : ZMod 2329089562843) ^ 309 = (2 : ZMod 2329089562843) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 154 * (2 : ZMod 2329089562843) ^ 154) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 166237674070 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 2329089562843) ^ 619 = 1272364974960 := by
        calc
          (2 : ZMod 2329089562843) ^ 619 = (2 : ZMod 2329089562843) ^ (309 + 309 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 309 * (2 : ZMod 2329089562843) ^ 309) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1272364974960 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 2329089562843) ^ 1239 = 76256014690 := by
        calc
          (2 : ZMod 2329089562843) ^ 1239 = (2 : ZMod 2329089562843) ^ (619 + 619 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 619 * (2 : ZMod 2329089562843) ^ 619) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 76256014690 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 2329089562843) ^ 2479 = 182822077603 := by
        calc
          (2 : ZMod 2329089562843) ^ 2479 = (2 : ZMod 2329089562843) ^ (1239 + 1239 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 1239 * (2 : ZMod 2329089562843) ^ 1239) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 182822077603 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 2329089562843) ^ 4958 = 841207173326 := by
        calc
          (2 : ZMod 2329089562843) ^ 4958 = (2 : ZMod 2329089562843) ^ (2479 + 2479) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2479 * (2 : ZMod 2329089562843) ^ 2479 := by rw [pow_add]
          _ = 841207173326 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 2329089562843) ^ 9916 = 1058834168699 := by
        calc
          (2 : ZMod 2329089562843) ^ 9916 = (2 : ZMod 2329089562843) ^ (4958 + 4958) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4958 * (2 : ZMod 2329089562843) ^ 4958 := by rw [pow_add]
          _ = 1058834168699 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 2329089562843) ^ 19832 = 2092140627020 := by
        calc
          (2 : ZMod 2329089562843) ^ 19832 = (2 : ZMod 2329089562843) ^ (9916 + 9916) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 9916 * (2 : ZMod 2329089562843) ^ 9916 := by rw [pow_add]
          _ = 2092140627020 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 2329089562843) ^ 39664 = 2239450955746 := by
        calc
          (2 : ZMod 2329089562843) ^ 39664 = (2 : ZMod 2329089562843) ^ (19832 + 19832) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 19832 * (2 : ZMod 2329089562843) ^ 19832 := by rw [pow_add]
          _ = 2239450955746 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 2329089562843) ^ 79328 = 1587931184000 := by
        calc
          (2 : ZMod 2329089562843) ^ 79328 = (2 : ZMod 2329089562843) ^ (39664 + 39664) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 39664 * (2 : ZMod 2329089562843) ^ 39664 := by rw [pow_add]
          _ = 1587931184000 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 2329089562843) ^ 158656 = 86336376928 := by
        calc
          (2 : ZMod 2329089562843) ^ 158656 = (2 : ZMod 2329089562843) ^ (79328 + 79328) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 79328 * (2 : ZMod 2329089562843) ^ 79328 := by rw [pow_add]
          _ = 86336376928 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 2329089562843) ^ 317313 = 1075212122602 := by
        calc
          (2 : ZMod 2329089562843) ^ 317313 = (2 : ZMod 2329089562843) ^ (158656 + 158656 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 158656 * (2 : ZMod 2329089562843) ^ 158656) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1075212122602 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 2329089562843) ^ 634626 = 1653132356624 := by
        calc
          (2 : ZMod 2329089562843) ^ 634626 = (2 : ZMod 2329089562843) ^ (317313 + 317313) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 317313 * (2 : ZMod 2329089562843) ^ 317313 := by rw [pow_add]
          _ = 1653132356624 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 2329089562843) ^ 1269253 = 35101334202 := by
        calc
          (2 : ZMod 2329089562843) ^ 1269253 = (2 : ZMod 2329089562843) ^ (634626 + 634626 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 634626 * (2 : ZMod 2329089562843) ^ 634626) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 35101334202 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 2329089562843) ^ 2538506 = 530836601038 := by
        calc
          (2 : ZMod 2329089562843) ^ 2538506 = (2 : ZMod 2329089562843) ^ (1269253 + 1269253) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1269253 * (2 : ZMod 2329089562843) ^ 1269253 := by rw [pow_add]
          _ = 530836601038 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 2329089562843) ^ 5077012 = 222547459658 := by
        calc
          (2 : ZMod 2329089562843) ^ 5077012 = (2 : ZMod 2329089562843) ^ (2538506 + 2538506) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2538506 * (2 : ZMod 2329089562843) ^ 2538506 := by rw [pow_add]
          _ = 222547459658 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 2329089562843) ^ 10154024 = 1903323804274 := by
        calc
          (2 : ZMod 2329089562843) ^ 10154024 = (2 : ZMod 2329089562843) ^ (5077012 + 5077012) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 5077012 * (2 : ZMod 2329089562843) ^ 5077012 := by rw [pow_add]
          _ = 1903323804274 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 2329089562843) ^ 20308049 = 2186106070141 := by
        calc
          (2 : ZMod 2329089562843) ^ 20308049 = (2 : ZMod 2329089562843) ^ (10154024 + 10154024 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 10154024 * (2 : ZMod 2329089562843) ^ 10154024) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2186106070141 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 2329089562843) ^ 40616098 = 2075944704342 := by
        calc
          (2 : ZMod 2329089562843) ^ 40616098 = (2 : ZMod 2329089562843) ^ (20308049 + 20308049) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 20308049 * (2 : ZMod 2329089562843) ^ 20308049 := by rw [pow_add]
          _ = 2075944704342 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 2329089562843) ^ 81232197 = 2066214567574 := by
        calc
          (2 : ZMod 2329089562843) ^ 81232197 = (2 : ZMod 2329089562843) ^ (40616098 + 40616098 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 40616098 * (2 : ZMod 2329089562843) ^ 40616098) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2066214567574 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 2329089562843) ^ 162464394 = 719476071928 := by
        calc
          (2 : ZMod 2329089562843) ^ 162464394 = (2 : ZMod 2329089562843) ^ (81232197 + 81232197) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 81232197 * (2 : ZMod 2329089562843) ^ 81232197 := by rw [pow_add]
          _ = 719476071928 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 2329089562843) ^ 324928789 = 2002045897080 := by
        calc
          (2 : ZMod 2329089562843) ^ 324928789 = (2 : ZMod 2329089562843) ^ (162464394 + 162464394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 162464394 * (2 : ZMod 2329089562843) ^ 162464394) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2002045897080 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 2329089562843) ^ 649857578 = 1759834514155 := by
        calc
          (2 : ZMod 2329089562843) ^ 649857578 = (2 : ZMod 2329089562843) ^ (324928789 + 324928789) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 324928789 * (2 : ZMod 2329089562843) ^ 324928789 := by rw [pow_add]
          _ = 1759834514155 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 2329089562843) ^ 1299715157 = 1248007363237 := by
        calc
          (2 : ZMod 2329089562843) ^ 1299715157 = (2 : ZMod 2329089562843) ^ (649857578 + 649857578 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 649857578 * (2 : ZMod 2329089562843) ^ 649857578) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1248007363237 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 2329089562843) ^ 2599430315 = 540343466262 := by
        calc
          (2 : ZMod 2329089562843) ^ 2599430315 = (2 : ZMod 2329089562843) ^ (1299715157 + 1299715157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 1299715157 * (2 : ZMod 2329089562843) ^ 1299715157) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 540343466262 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 2329089562843) ^ 5198860631 = 1038767745566 := by
        calc
          (2 : ZMod 2329089562843) ^ 5198860631 = (2 : ZMod 2329089562843) ^ (2599430315 + 2599430315 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 2599430315 * (2 : ZMod 2329089562843) ^ 2599430315) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1038767745566 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 2329089562843) ^ 10397721262 = 2085119230102 := by
        calc
          (2 : ZMod 2329089562843) ^ 10397721262 = (2 : ZMod 2329089562843) ^ (5198860631 + 5198860631) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 5198860631 * (2 : ZMod 2329089562843) ^ 5198860631 := by rw [pow_add]
          _ = 2085119230102 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 2329089562843) ^ 20795442525 = 1101705011158 := by
        calc
          (2 : ZMod 2329089562843) ^ 20795442525 = (2 : ZMod 2329089562843) ^ (10397721262 + 10397721262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 10397721262 * (2 : ZMod 2329089562843) ^ 10397721262) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1101705011158 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 2329089562843) ^ 41590885050 = 1915425764072 := by
        calc
          (2 : ZMod 2329089562843) ^ 41590885050 = (2 : ZMod 2329089562843) ^ (20795442525 + 20795442525) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 20795442525 * (2 : ZMod 2329089562843) ^ 20795442525 := by rw [pow_add]
          _ = 1915425764072 := by rw [factor_2_34]; decide
      have factor_2_36 : (2 : ZMod 2329089562843) ^ 83181770101 = 631145548612 := by
        calc
          (2 : ZMod 2329089562843) ^ 83181770101 = (2 : ZMod 2329089562843) ^ (41590885050 + 41590885050 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 41590885050 * (2 : ZMod 2329089562843) ^ 41590885050) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 631145548612 := by rw [factor_2_35]; decide
      have factor_2_37 : (2 : ZMod 2329089562843) ^ 166363540203 = 1991650203367 := by
        calc
          (2 : ZMod 2329089562843) ^ 166363540203 = (2 : ZMod 2329089562843) ^ (83181770101 + 83181770101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 83181770101 * (2 : ZMod 2329089562843) ^ 83181770101) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1991650203367 := by rw [factor_2_36]; decide
      have factor_2_38 : (2 : ZMod 2329089562843) ^ 332727080406 = 487100976373 := by
        calc
          (2 : ZMod 2329089562843) ^ 332727080406 = (2 : ZMod 2329089562843) ^ (166363540203 + 166363540203) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 166363540203 * (2 : ZMod 2329089562843) ^ 166363540203 := by rw [pow_add]
          _ = 487100976373 := by rw [factor_2_37]; decide
      change (2 : ZMod 2329089562843) ^ 332727080406 ≠ 1
      rw [factor_2_38]
      decide
    ·
      have factor_3_0 : (2 : ZMod 2329089562843) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 2329089562843) ^ 2 = 4 := by
        calc
          (2 : ZMod 2329089562843) ^ 2 = (2 : ZMod 2329089562843) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1 * (2 : ZMod 2329089562843) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 2329089562843) ^ 4 = 16 := by
        calc
          (2 : ZMod 2329089562843) ^ 4 = (2 : ZMod 2329089562843) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2 * (2 : ZMod 2329089562843) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 2329089562843) ^ 8 = 256 := by
        calc
          (2 : ZMod 2329089562843) ^ 8 = (2 : ZMod 2329089562843) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4 * (2 : ZMod 2329089562843) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 2329089562843) ^ 17 = 131072 := by
        calc
          (2 : ZMod 2329089562843) ^ 17 = (2 : ZMod 2329089562843) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 8 * (2 : ZMod 2329089562843) ^ 8) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 2329089562843) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 2329089562843) ^ 34 = (2 : ZMod 2329089562843) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 17 * (2 : ZMod 2329089562843) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 2329089562843) ^ 69 = 1898335997773 := by
        calc
          (2 : ZMod 2329089562843) ^ 69 = (2 : ZMod 2329089562843) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 34 * (2 : ZMod 2329089562843) ^ 34) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1898335997773 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 2329089562843) ^ 139 = 244548123065 := by
        calc
          (2 : ZMod 2329089562843) ^ 139 = (2 : ZMod 2329089562843) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 69 * (2 : ZMod 2329089562843) ^ 69) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 244548123065 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 2329089562843) ^ 279 = 1138772345470 := by
        calc
          (2 : ZMod 2329089562843) ^ 279 = (2 : ZMod 2329089562843) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 139 * (2 : ZMod 2329089562843) ^ 139) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1138772345470 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 2329089562843) ^ 559 = 1196164099131 := by
        calc
          (2 : ZMod 2329089562843) ^ 559 = (2 : ZMod 2329089562843) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 279 * (2 : ZMod 2329089562843) ^ 279) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1196164099131 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 2329089562843) ^ 1119 = 1562311548860 := by
        calc
          (2 : ZMod 2329089562843) ^ 1119 = (2 : ZMod 2329089562843) ^ (559 + 559 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 559 * (2 : ZMod 2329089562843) ^ 559) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1562311548860 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 2329089562843) ^ 2239 = 1549781592226 := by
        calc
          (2 : ZMod 2329089562843) ^ 2239 = (2 : ZMod 2329089562843) ^ (1119 + 1119 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 1119 * (2 : ZMod 2329089562843) ^ 1119) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1549781592226 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 2329089562843) ^ 4478 = 2000947773488 := by
        calc
          (2 : ZMod 2329089562843) ^ 4478 = (2 : ZMod 2329089562843) ^ (2239 + 2239) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2239 * (2 : ZMod 2329089562843) ^ 2239 := by rw [pow_add]
          _ = 2000947773488 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 2329089562843) ^ 8956 = 1192490920984 := by
        calc
          (2 : ZMod 2329089562843) ^ 8956 = (2 : ZMod 2329089562843) ^ (4478 + 4478) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4478 * (2 : ZMod 2329089562843) ^ 4478 := by rw [pow_add]
          _ = 1192490920984 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 2329089562843) ^ 17912 = 930770351709 := by
        calc
          (2 : ZMod 2329089562843) ^ 17912 = (2 : ZMod 2329089562843) ^ (8956 + 8956) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 8956 * (2 : ZMod 2329089562843) ^ 8956 := by rw [pow_add]
          _ = 930770351709 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 2329089562843) ^ 35825 = 960920720986 := by
        calc
          (2 : ZMod 2329089562843) ^ 35825 = (2 : ZMod 2329089562843) ^ (17912 + 17912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 17912 * (2 : ZMod 2329089562843) ^ 17912) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 960920720986 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 2329089562843) ^ 71651 = 1132320923426 := by
        calc
          (2 : ZMod 2329089562843) ^ 71651 = (2 : ZMod 2329089562843) ^ (35825 + 35825 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 35825 * (2 : ZMod 2329089562843) ^ 35825) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1132320923426 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 2329089562843) ^ 143302 = 782653809948 := by
        calc
          (2 : ZMod 2329089562843) ^ 143302 = (2 : ZMod 2329089562843) ^ (71651 + 71651) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 71651 * (2 : ZMod 2329089562843) ^ 71651 := by rw [pow_add]
          _ = 782653809948 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 2329089562843) ^ 286605 = 1254749352529 := by
        calc
          (2 : ZMod 2329089562843) ^ 286605 = (2 : ZMod 2329089562843) ^ (143302 + 143302 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 143302 * (2 : ZMod 2329089562843) ^ 143302) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1254749352529 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 2329089562843) ^ 573211 = 961953170880 := by
        calc
          (2 : ZMod 2329089562843) ^ 573211 = (2 : ZMod 2329089562843) ^ (286605 + 286605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 286605 * (2 : ZMod 2329089562843) ^ 286605) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 961953170880 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 2329089562843) ^ 1146422 = 1041560550677 := by
        calc
          (2 : ZMod 2329089562843) ^ 1146422 = (2 : ZMod 2329089562843) ^ (573211 + 573211) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 573211 * (2 : ZMod 2329089562843) ^ 573211 := by rw [pow_add]
          _ = 1041560550677 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 2329089562843) ^ 2292844 = 1360352630584 := by
        calc
          (2 : ZMod 2329089562843) ^ 2292844 = (2 : ZMod 2329089562843) ^ (1146422 + 1146422) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1146422 * (2 : ZMod 2329089562843) ^ 1146422 := by rw [pow_add]
          _ = 1360352630584 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 2329089562843) ^ 4585688 = 2163044995746 := by
        calc
          (2 : ZMod 2329089562843) ^ 4585688 = (2 : ZMod 2329089562843) ^ (2292844 + 2292844) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2292844 * (2 : ZMod 2329089562843) ^ 2292844 := by rw [pow_add]
          _ = 2163044995746 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 2329089562843) ^ 9171377 = 1760463504829 := by
        calc
          (2 : ZMod 2329089562843) ^ 9171377 = (2 : ZMod 2329089562843) ^ (4585688 + 4585688 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 4585688 * (2 : ZMod 2329089562843) ^ 4585688) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1760463504829 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 2329089562843) ^ 18342754 = 1206593982518 := by
        calc
          (2 : ZMod 2329089562843) ^ 18342754 = (2 : ZMod 2329089562843) ^ (9171377 + 9171377) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 9171377 * (2 : ZMod 2329089562843) ^ 9171377 := by rw [pow_add]
          _ = 1206593982518 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 2329089562843) ^ 36685508 = 838844153924 := by
        calc
          (2 : ZMod 2329089562843) ^ 36685508 = (2 : ZMod 2329089562843) ^ (18342754 + 18342754) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 18342754 * (2 : ZMod 2329089562843) ^ 18342754 := by rw [pow_add]
          _ = 838844153924 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 2329089562843) ^ 73371016 = 2300208806895 := by
        calc
          (2 : ZMod 2329089562843) ^ 73371016 = (2 : ZMod 2329089562843) ^ (36685508 + 36685508) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 36685508 * (2 : ZMod 2329089562843) ^ 36685508 := by rw [pow_add]
          _ = 2300208806895 := by rw [factor_3_25]; decide
      have factor_3_27 : (2 : ZMod 2329089562843) ^ 146742033 = 1530417109312 := by
        calc
          (2 : ZMod 2329089562843) ^ 146742033 = (2 : ZMod 2329089562843) ^ (73371016 + 73371016 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 73371016 * (2 : ZMod 2329089562843) ^ 73371016) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1530417109312 := by rw [factor_3_26]; decide
      have factor_3_28 : (2 : ZMod 2329089562843) ^ 293484067 = 1532263470241 := by
        calc
          (2 : ZMod 2329089562843) ^ 293484067 = (2 : ZMod 2329089562843) ^ (146742033 + 146742033 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 146742033 * (2 : ZMod 2329089562843) ^ 146742033) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1532263470241 := by rw [factor_3_27]; decide
      have factor_3_29 : (2 : ZMod 2329089562843) ^ 586968135 = 852045783018 := by
        calc
          (2 : ZMod 2329089562843) ^ 586968135 = (2 : ZMod 2329089562843) ^ (293484067 + 293484067 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 293484067 * (2 : ZMod 2329089562843) ^ 293484067) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 852045783018 := by rw [factor_3_28]; decide
      have factor_3_30 : (2 : ZMod 2329089562843) ^ 1173936271 = 1033957717240 := by
        calc
          (2 : ZMod 2329089562843) ^ 1173936271 = (2 : ZMod 2329089562843) ^ (586968135 + 586968135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 586968135 * (2 : ZMod 2329089562843) ^ 586968135) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1033957717240 := by rw [factor_3_29]; decide
      have factor_3_31 : (2 : ZMod 2329089562843) ^ 2347872543 = 2128227199122 := by
        calc
          (2 : ZMod 2329089562843) ^ 2347872543 = (2 : ZMod 2329089562843) ^ (1173936271 + 1173936271 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 1173936271 * (2 : ZMod 2329089562843) ^ 1173936271) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2128227199122 := by rw [factor_3_30]; decide
      have factor_3_32 : (2 : ZMod 2329089562843) ^ 4695745086 = 721597531053 := by
        calc
          (2 : ZMod 2329089562843) ^ 4695745086 = (2 : ZMod 2329089562843) ^ (2347872543 + 2347872543) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2347872543 * (2 : ZMod 2329089562843) ^ 2347872543 := by rw [pow_add]
          _ = 721597531053 := by rw [factor_3_31]; decide
      have factor_3_33 : (2 : ZMod 2329089562843) ^ 9391490172 = 1414003413154 := by
        calc
          (2 : ZMod 2329089562843) ^ 9391490172 = (2 : ZMod 2329089562843) ^ (4695745086 + 4695745086) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4695745086 * (2 : ZMod 2329089562843) ^ 4695745086 := by rw [pow_add]
          _ = 1414003413154 := by rw [factor_3_32]; decide
      have factor_3_34 : (2 : ZMod 2329089562843) ^ 18782980345 = 2088117101983 := by
        calc
          (2 : ZMod 2329089562843) ^ 18782980345 = (2 : ZMod 2329089562843) ^ (9391490172 + 9391490172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 9391490172 * (2 : ZMod 2329089562843) ^ 9391490172) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2088117101983 := by rw [factor_3_33]; decide
      have factor_3_35 : (2 : ZMod 2329089562843) ^ 37565960691 = 1128617846221 := by
        calc
          (2 : ZMod 2329089562843) ^ 37565960691 = (2 : ZMod 2329089562843) ^ (18782980345 + 18782980345 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 18782980345 * (2 : ZMod 2329089562843) ^ 18782980345) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1128617846221 := by rw [factor_3_34]; decide
      have factor_3_36 : (2 : ZMod 2329089562843) ^ 75131921382 = 105267679823 := by
        calc
          (2 : ZMod 2329089562843) ^ 75131921382 = (2 : ZMod 2329089562843) ^ (37565960691 + 37565960691) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 37565960691 * (2 : ZMod 2329089562843) ^ 37565960691 := by rw [pow_add]
          _ = 105267679823 := by rw [factor_3_35]; decide
      change (2 : ZMod 2329089562843) ^ 75131921382 ≠ 1
      rw [factor_3_36]
      decide
    ·
      have factor_4_0 : (2 : ZMod 2329089562843) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 2329089562843) ^ 2 = 4 := by
        calc
          (2 : ZMod 2329089562843) ^ 2 = (2 : ZMod 2329089562843) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1 * (2 : ZMod 2329089562843) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 2329089562843) ^ 4 = 16 := by
        calc
          (2 : ZMod 2329089562843) ^ 4 = (2 : ZMod 2329089562843) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 2 * (2 : ZMod 2329089562843) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 2329089562843) ^ 8 = 256 := by
        calc
          (2 : ZMod 2329089562843) ^ 8 = (2 : ZMod 2329089562843) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4 * (2 : ZMod 2329089562843) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 2329089562843) ^ 17 = 131072 := by
        calc
          (2 : ZMod 2329089562843) ^ 17 = (2 : ZMod 2329089562843) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 8 * (2 : ZMod 2329089562843) ^ 8) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 2329089562843) ^ 35 = 34359738368 := by
        calc
          (2 : ZMod 2329089562843) ^ 35 = (2 : ZMod 2329089562843) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 17 * (2 : ZMod 2329089562843) ^ 17) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 34359738368 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 2329089562843) ^ 71 = 606075302563 := by
        calc
          (2 : ZMod 2329089562843) ^ 71 = (2 : ZMod 2329089562843) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 35 * (2 : ZMod 2329089562843) ^ 35) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 606075302563 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 2329089562843) ^ 142 = 1956384984520 := by
        calc
          (2 : ZMod 2329089562843) ^ 142 = (2 : ZMod 2329089562843) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 71 * (2 : ZMod 2329089562843) ^ 71 := by rw [pow_add]
          _ = 1956384984520 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 2329089562843) ^ 284 = 1504371612395 := by
        calc
          (2 : ZMod 2329089562843) ^ 284 = (2 : ZMod 2329089562843) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 142 * (2 : ZMod 2329089562843) ^ 142 := by rw [pow_add]
          _ = 1504371612395 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 2329089562843) ^ 569 = 2100017017569 := by
        calc
          (2 : ZMod 2329089562843) ^ 569 = (2 : ZMod 2329089562843) ^ (284 + 284 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 284 * (2 : ZMod 2329089562843) ^ 284) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2100017017569 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 2329089562843) ^ 1139 = 2314288356665 := by
        calc
          (2 : ZMod 2329089562843) ^ 1139 = (2 : ZMod 2329089562843) ^ (569 + 569 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 569 * (2 : ZMod 2329089562843) ^ 569) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 2314288356665 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 2329089562843) ^ 2278 = 514451748461 := by
        calc
          (2 : ZMod 2329089562843) ^ 2278 = (2 : ZMod 2329089562843) ^ (1139 + 1139) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 1139 * (2 : ZMod 2329089562843) ^ 1139 := by rw [pow_add]
          _ = 514451748461 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 2329089562843) ^ 4557 = 1901869651632 := by
        calc
          (2 : ZMod 2329089562843) ^ 4557 = (2 : ZMod 2329089562843) ^ (2278 + 2278 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = ((2 : ZMod 2329089562843) ^ 2278 * (2 : ZMod 2329089562843) ^ 2278) * (2 : ZMod 2329089562843) := by rw [pow_succ, pow_add]
          _ = 1901869651632 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 2329089562843) ^ 9114 = 1018247557492 := by
        calc
          (2 : ZMod 2329089562843) ^ 9114 = (2 : ZMod 2329089562843) ^ (4557 + 4557) :=
            congrArg (fun n : ℕ => (2 : ZMod 2329089562843) ^ n) (by norm_num)
          _ = (2 : ZMod 2329089562843) ^ 4557 * (2 : ZMod 2329089562843) ^ 4557 := by rw [pow_add]
          _ = 1018247557492 := by rw [factor_4_12]; decide
      change (2 : ZMod 2329089562843) ^ 9114 ≠ 1
      rw [factor_4_13]
      decide

#print axioms prime_lucas_2329089562843

end TotientTailPeriodKiller
end Erdos249257
