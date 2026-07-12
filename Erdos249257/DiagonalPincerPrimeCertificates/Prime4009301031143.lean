import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10720056233

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_4009301031143 : Nat.Prime 4009301031143 := by
  apply lucas_primality 4009301031143 (5 : ZMod 4009301031143)
  ·
      have fermat_0 : (5 : ZMod 4009301031143) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 4009301031143) ^ 3 = 125 := by
        calc
          (5 : ZMod 4009301031143) ^ 3 = (5 : ZMod 4009301031143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1 * (5 : ZMod 4009301031143) ^ 1) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 4009301031143) ^ 7 = 78125 := by
        calc
          (5 : ZMod 4009301031143) ^ 7 = (5 : ZMod 4009301031143) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 3 * (5 : ZMod 4009301031143) ^ 3) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 4009301031143) ^ 14 = 6103515625 := by
        calc
          (5 : ZMod 4009301031143) ^ 14 = (5 : ZMod 4009301031143) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 7 * (5 : ZMod 4009301031143) ^ 7 := by rw [pow_add]
          _ = 6103515625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 4009301031143) ^ 29 = 2678850063682 := by
        calc
          (5 : ZMod 4009301031143) ^ 29 = (5 : ZMod 4009301031143) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 14 * (5 : ZMod 4009301031143) ^ 14) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2678850063682 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 4009301031143) ^ 58 = 1336332387273 := by
        calc
          (5 : ZMod 4009301031143) ^ 58 = (5 : ZMod 4009301031143) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 29 * (5 : ZMod 4009301031143) ^ 29 := by rw [pow_add]
          _ = 1336332387273 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 4009301031143) ^ 116 = 2935458575616 := by
        calc
          (5 : ZMod 4009301031143) ^ 116 = (5 : ZMod 4009301031143) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 58 * (5 : ZMod 4009301031143) ^ 58 := by rw [pow_add]
          _ = 2935458575616 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 4009301031143) ^ 233 = 672352080107 := by
        calc
          (5 : ZMod 4009301031143) ^ 233 = (5 : ZMod 4009301031143) ^ (116 + 116 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 116 * (5 : ZMod 4009301031143) ^ 116) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 672352080107 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 4009301031143) ^ 466 = 2217586717151 := by
        calc
          (5 : ZMod 4009301031143) ^ 466 = (5 : ZMod 4009301031143) ^ (233 + 233) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 233 * (5 : ZMod 4009301031143) ^ 233 := by rw [pow_add]
          _ = 2217586717151 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 4009301031143) ^ 933 = 233932523477 := by
        calc
          (5 : ZMod 4009301031143) ^ 933 = (5 : ZMod 4009301031143) ^ (466 + 466 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 466 * (5 : ZMod 4009301031143) ^ 466) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 233932523477 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 4009301031143) ^ 1866 = 2676300898374 := by
        calc
          (5 : ZMod 4009301031143) ^ 1866 = (5 : ZMod 4009301031143) ^ (933 + 933) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 933 * (5 : ZMod 4009301031143) ^ 933 := by rw [pow_add]
          _ = 2676300898374 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 4009301031143) ^ 3733 = 2817191301877 := by
        calc
          (5 : ZMod 4009301031143) ^ 3733 = (5 : ZMod 4009301031143) ^ (1866 + 1866 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1866 * (5 : ZMod 4009301031143) ^ 1866) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2817191301877 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 4009301031143) ^ 7467 = 2781933733998 := by
        calc
          (5 : ZMod 4009301031143) ^ 7467 = (5 : ZMod 4009301031143) ^ (3733 + 3733 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 3733 * (5 : ZMod 4009301031143) ^ 3733) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2781933733998 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 4009301031143) ^ 14935 = 1338655202946 := by
        calc
          (5 : ZMod 4009301031143) ^ 14935 = (5 : ZMod 4009301031143) ^ (7467 + 7467 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 7467 * (5 : ZMod 4009301031143) ^ 7467) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1338655202946 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 4009301031143) ^ 29871 = 1455016149618 := by
        calc
          (5 : ZMod 4009301031143) ^ 29871 = (5 : ZMod 4009301031143) ^ (14935 + 14935 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 14935 * (5 : ZMod 4009301031143) ^ 14935) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1455016149618 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 4009301031143) ^ 59743 = 359044044622 := by
        calc
          (5 : ZMod 4009301031143) ^ 59743 = (5 : ZMod 4009301031143) ^ (29871 + 29871 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 29871 * (5 : ZMod 4009301031143) ^ 29871) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 359044044622 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 4009301031143) ^ 119486 = 2179083458374 := by
        calc
          (5 : ZMod 4009301031143) ^ 119486 = (5 : ZMod 4009301031143) ^ (59743 + 59743) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 59743 * (5 : ZMod 4009301031143) ^ 59743 := by rw [pow_add]
          _ = 2179083458374 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 4009301031143) ^ 238972 = 1293520536028 := by
        calc
          (5 : ZMod 4009301031143) ^ 238972 = (5 : ZMod 4009301031143) ^ (119486 + 119486) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 119486 * (5 : ZMod 4009301031143) ^ 119486 := by rw [pow_add]
          _ = 1293520536028 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 4009301031143) ^ 477945 = 1567048670164 := by
        calc
          (5 : ZMod 4009301031143) ^ 477945 = (5 : ZMod 4009301031143) ^ (238972 + 238972 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 238972 * (5 : ZMod 4009301031143) ^ 238972) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1567048670164 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 4009301031143) ^ 955891 = 778750708072 := by
        calc
          (5 : ZMod 4009301031143) ^ 955891 = (5 : ZMod 4009301031143) ^ (477945 + 477945 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 477945 * (5 : ZMod 4009301031143) ^ 477945) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 778750708072 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 4009301031143) ^ 1911783 = 25806707292 := by
        calc
          (5 : ZMod 4009301031143) ^ 1911783 = (5 : ZMod 4009301031143) ^ (955891 + 955891 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 955891 * (5 : ZMod 4009301031143) ^ 955891) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 25806707292 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 4009301031143) ^ 3823567 = 1558536681830 := by
        calc
          (5 : ZMod 4009301031143) ^ 3823567 = (5 : ZMod 4009301031143) ^ (1911783 + 1911783 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1911783 * (5 : ZMod 4009301031143) ^ 1911783) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1558536681830 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 4009301031143) ^ 7647134 = 3271775189926 := by
        calc
          (5 : ZMod 4009301031143) ^ 7647134 = (5 : ZMod 4009301031143) ^ (3823567 + 3823567) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 3823567 * (5 : ZMod 4009301031143) ^ 3823567 := by rw [pow_add]
          _ = 3271775189926 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 4009301031143) ^ 15294269 = 3489684275699 := by
        calc
          (5 : ZMod 4009301031143) ^ 15294269 = (5 : ZMod 4009301031143) ^ (7647134 + 7647134 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 7647134 * (5 : ZMod 4009301031143) ^ 7647134) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3489684275699 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 4009301031143) ^ 30588539 = 2536598610083 := by
        calc
          (5 : ZMod 4009301031143) ^ 30588539 = (5 : ZMod 4009301031143) ^ (15294269 + 15294269 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 15294269 * (5 : ZMod 4009301031143) ^ 15294269) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2536598610083 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 4009301031143) ^ 61177078 = 629287035478 := by
        calc
          (5 : ZMod 4009301031143) ^ 61177078 = (5 : ZMod 4009301031143) ^ (30588539 + 30588539) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 30588539 * (5 : ZMod 4009301031143) ^ 30588539 := by rw [pow_add]
          _ = 629287035478 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 4009301031143) ^ 122354157 = 1851034745343 := by
        calc
          (5 : ZMod 4009301031143) ^ 122354157 = (5 : ZMod 4009301031143) ^ (61177078 + 61177078 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 61177078 * (5 : ZMod 4009301031143) ^ 61177078) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1851034745343 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 4009301031143) ^ 244708314 = 1597749648956 := by
        calc
          (5 : ZMod 4009301031143) ^ 244708314 = (5 : ZMod 4009301031143) ^ (122354157 + 122354157) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 122354157 * (5 : ZMod 4009301031143) ^ 122354157 := by rw [pow_add]
          _ = 1597749648956 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 4009301031143) ^ 489416629 = 2477557971387 := by
        calc
          (5 : ZMod 4009301031143) ^ 489416629 = (5 : ZMod 4009301031143) ^ (244708314 + 244708314 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 244708314 * (5 : ZMod 4009301031143) ^ 244708314) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2477557971387 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 4009301031143) ^ 978833259 = 3594492600112 := by
        calc
          (5 : ZMod 4009301031143) ^ 978833259 = (5 : ZMod 4009301031143) ^ (489416629 + 489416629 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 489416629 * (5 : ZMod 4009301031143) ^ 489416629) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3594492600112 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 4009301031143) ^ 1957666519 = 3039532867530 := by
        calc
          (5 : ZMod 4009301031143) ^ 1957666519 = (5 : ZMod 4009301031143) ^ (978833259 + 978833259 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 978833259 * (5 : ZMod 4009301031143) ^ 978833259) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3039532867530 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 4009301031143) ^ 3915333038 = 540468590953 := by
        calc
          (5 : ZMod 4009301031143) ^ 3915333038 = (5 : ZMod 4009301031143) ^ (1957666519 + 1957666519) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1957666519 * (5 : ZMod 4009301031143) ^ 1957666519 := by rw [pow_add]
          _ = 540468590953 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 4009301031143) ^ 7830666076 = 2844047426671 := by
        calc
          (5 : ZMod 4009301031143) ^ 7830666076 = (5 : ZMod 4009301031143) ^ (3915333038 + 3915333038) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 3915333038 * (5 : ZMod 4009301031143) ^ 3915333038 := by rw [pow_add]
          _ = 2844047426671 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 4009301031143) ^ 15661332152 = 434832832247 := by
        calc
          (5 : ZMod 4009301031143) ^ 15661332152 = (5 : ZMod 4009301031143) ^ (7830666076 + 7830666076) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 7830666076 * (5 : ZMod 4009301031143) ^ 7830666076 := by rw [pow_add]
          _ = 434832832247 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 4009301031143) ^ 31322664305 = 2570367235696 := by
        calc
          (5 : ZMod 4009301031143) ^ 31322664305 = (5 : ZMod 4009301031143) ^ (15661332152 + 15661332152 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 15661332152 * (5 : ZMod 4009301031143) ^ 15661332152) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2570367235696 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 4009301031143) ^ 62645328611 = 989868084543 := by
        calc
          (5 : ZMod 4009301031143) ^ 62645328611 = (5 : ZMod 4009301031143) ^ (31322664305 + 31322664305 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 31322664305 * (5 : ZMod 4009301031143) ^ 31322664305) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 989868084543 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 4009301031143) ^ 125290657223 = 3648787874019 := by
        calc
          (5 : ZMod 4009301031143) ^ 125290657223 = (5 : ZMod 4009301031143) ^ (62645328611 + 62645328611 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 62645328611 * (5 : ZMod 4009301031143) ^ 62645328611) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3648787874019 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 4009301031143) ^ 250581314446 = 3144831766790 := by
        calc
          (5 : ZMod 4009301031143) ^ 250581314446 = (5 : ZMod 4009301031143) ^ (125290657223 + 125290657223) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 125290657223 * (5 : ZMod 4009301031143) ^ 125290657223 := by rw [pow_add]
          _ = 3144831766790 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 4009301031143) ^ 501162628892 = 1744811836519 := by
        calc
          (5 : ZMod 4009301031143) ^ 501162628892 = (5 : ZMod 4009301031143) ^ (250581314446 + 250581314446) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 250581314446 * (5 : ZMod 4009301031143) ^ 250581314446 := by rw [pow_add]
          _ = 1744811836519 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 4009301031143) ^ 1002325257785 = 3873646642477 := by
        calc
          (5 : ZMod 4009301031143) ^ 1002325257785 = (5 : ZMod 4009301031143) ^ (501162628892 + 501162628892 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 501162628892 * (5 : ZMod 4009301031143) ^ 501162628892) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3873646642477 := by rw [fermat_38]; decide
      have fermat_40 : (5 : ZMod 4009301031143) ^ 2004650515571 = 4009301031142 := by
        calc
          (5 : ZMod 4009301031143) ^ 2004650515571 = (5 : ZMod 4009301031143) ^ (1002325257785 + 1002325257785 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1002325257785 * (5 : ZMod 4009301031143) ^ 1002325257785) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 4009301031142 := by rw [fermat_39]; decide
      have fermat_41 : (5 : ZMod 4009301031143) ^ 4009301031142 = 1 := by
        calc
          (5 : ZMod 4009301031143) ^ 4009301031142 = (5 : ZMod 4009301031143) ^ (2004650515571 + 2004650515571) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 2004650515571 * (5 : ZMod 4009301031143) ^ 2004650515571 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (10720056233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (10720056233, 1)] : List FactorBlock).map factorBlockValue).prod = 4009301031143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_10720056233) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 4009301031143) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 4009301031143) ^ 3 = 125 := by
        calc
          (5 : ZMod 4009301031143) ^ 3 = (5 : ZMod 4009301031143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1 * (5 : ZMod 4009301031143) ^ 1) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 4009301031143) ^ 7 = 78125 := by
        calc
          (5 : ZMod 4009301031143) ^ 7 = (5 : ZMod 4009301031143) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 3 * (5 : ZMod 4009301031143) ^ 3) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 4009301031143) ^ 14 = 6103515625 := by
        calc
          (5 : ZMod 4009301031143) ^ 14 = (5 : ZMod 4009301031143) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 7 * (5 : ZMod 4009301031143) ^ 7 := by rw [pow_add]
          _ = 6103515625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 4009301031143) ^ 29 = 2678850063682 := by
        calc
          (5 : ZMod 4009301031143) ^ 29 = (5 : ZMod 4009301031143) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 14 * (5 : ZMod 4009301031143) ^ 14) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2678850063682 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 4009301031143) ^ 58 = 1336332387273 := by
        calc
          (5 : ZMod 4009301031143) ^ 58 = (5 : ZMod 4009301031143) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 29 * (5 : ZMod 4009301031143) ^ 29 := by rw [pow_add]
          _ = 1336332387273 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 4009301031143) ^ 116 = 2935458575616 := by
        calc
          (5 : ZMod 4009301031143) ^ 116 = (5 : ZMod 4009301031143) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 58 * (5 : ZMod 4009301031143) ^ 58 := by rw [pow_add]
          _ = 2935458575616 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 4009301031143) ^ 233 = 672352080107 := by
        calc
          (5 : ZMod 4009301031143) ^ 233 = (5 : ZMod 4009301031143) ^ (116 + 116 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 116 * (5 : ZMod 4009301031143) ^ 116) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 672352080107 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 4009301031143) ^ 466 = 2217586717151 := by
        calc
          (5 : ZMod 4009301031143) ^ 466 = (5 : ZMod 4009301031143) ^ (233 + 233) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 233 * (5 : ZMod 4009301031143) ^ 233 := by rw [pow_add]
          _ = 2217586717151 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 4009301031143) ^ 933 = 233932523477 := by
        calc
          (5 : ZMod 4009301031143) ^ 933 = (5 : ZMod 4009301031143) ^ (466 + 466 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 466 * (5 : ZMod 4009301031143) ^ 466) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 233932523477 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 4009301031143) ^ 1866 = 2676300898374 := by
        calc
          (5 : ZMod 4009301031143) ^ 1866 = (5 : ZMod 4009301031143) ^ (933 + 933) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 933 * (5 : ZMod 4009301031143) ^ 933 := by rw [pow_add]
          _ = 2676300898374 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 4009301031143) ^ 3733 = 2817191301877 := by
        calc
          (5 : ZMod 4009301031143) ^ 3733 = (5 : ZMod 4009301031143) ^ (1866 + 1866 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1866 * (5 : ZMod 4009301031143) ^ 1866) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2817191301877 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 4009301031143) ^ 7467 = 2781933733998 := by
        calc
          (5 : ZMod 4009301031143) ^ 7467 = (5 : ZMod 4009301031143) ^ (3733 + 3733 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 3733 * (5 : ZMod 4009301031143) ^ 3733) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2781933733998 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 4009301031143) ^ 14935 = 1338655202946 := by
        calc
          (5 : ZMod 4009301031143) ^ 14935 = (5 : ZMod 4009301031143) ^ (7467 + 7467 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 7467 * (5 : ZMod 4009301031143) ^ 7467) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1338655202946 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 4009301031143) ^ 29871 = 1455016149618 := by
        calc
          (5 : ZMod 4009301031143) ^ 29871 = (5 : ZMod 4009301031143) ^ (14935 + 14935 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 14935 * (5 : ZMod 4009301031143) ^ 14935) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1455016149618 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 4009301031143) ^ 59743 = 359044044622 := by
        calc
          (5 : ZMod 4009301031143) ^ 59743 = (5 : ZMod 4009301031143) ^ (29871 + 29871 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 29871 * (5 : ZMod 4009301031143) ^ 29871) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 359044044622 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 4009301031143) ^ 119486 = 2179083458374 := by
        calc
          (5 : ZMod 4009301031143) ^ 119486 = (5 : ZMod 4009301031143) ^ (59743 + 59743) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 59743 * (5 : ZMod 4009301031143) ^ 59743 := by rw [pow_add]
          _ = 2179083458374 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 4009301031143) ^ 238972 = 1293520536028 := by
        calc
          (5 : ZMod 4009301031143) ^ 238972 = (5 : ZMod 4009301031143) ^ (119486 + 119486) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 119486 * (5 : ZMod 4009301031143) ^ 119486 := by rw [pow_add]
          _ = 1293520536028 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 4009301031143) ^ 477945 = 1567048670164 := by
        calc
          (5 : ZMod 4009301031143) ^ 477945 = (5 : ZMod 4009301031143) ^ (238972 + 238972 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 238972 * (5 : ZMod 4009301031143) ^ 238972) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1567048670164 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 4009301031143) ^ 955891 = 778750708072 := by
        calc
          (5 : ZMod 4009301031143) ^ 955891 = (5 : ZMod 4009301031143) ^ (477945 + 477945 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 477945 * (5 : ZMod 4009301031143) ^ 477945) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 778750708072 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 4009301031143) ^ 1911783 = 25806707292 := by
        calc
          (5 : ZMod 4009301031143) ^ 1911783 = (5 : ZMod 4009301031143) ^ (955891 + 955891 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 955891 * (5 : ZMod 4009301031143) ^ 955891) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 25806707292 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 4009301031143) ^ 3823567 = 1558536681830 := by
        calc
          (5 : ZMod 4009301031143) ^ 3823567 = (5 : ZMod 4009301031143) ^ (1911783 + 1911783 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1911783 * (5 : ZMod 4009301031143) ^ 1911783) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1558536681830 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 4009301031143) ^ 7647134 = 3271775189926 := by
        calc
          (5 : ZMod 4009301031143) ^ 7647134 = (5 : ZMod 4009301031143) ^ (3823567 + 3823567) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 3823567 * (5 : ZMod 4009301031143) ^ 3823567 := by rw [pow_add]
          _ = 3271775189926 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 4009301031143) ^ 15294269 = 3489684275699 := by
        calc
          (5 : ZMod 4009301031143) ^ 15294269 = (5 : ZMod 4009301031143) ^ (7647134 + 7647134 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 7647134 * (5 : ZMod 4009301031143) ^ 7647134) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3489684275699 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 4009301031143) ^ 30588539 = 2536598610083 := by
        calc
          (5 : ZMod 4009301031143) ^ 30588539 = (5 : ZMod 4009301031143) ^ (15294269 + 15294269 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 15294269 * (5 : ZMod 4009301031143) ^ 15294269) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2536598610083 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 4009301031143) ^ 61177078 = 629287035478 := by
        calc
          (5 : ZMod 4009301031143) ^ 61177078 = (5 : ZMod 4009301031143) ^ (30588539 + 30588539) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 30588539 * (5 : ZMod 4009301031143) ^ 30588539 := by rw [pow_add]
          _ = 629287035478 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 4009301031143) ^ 122354157 = 1851034745343 := by
        calc
          (5 : ZMod 4009301031143) ^ 122354157 = (5 : ZMod 4009301031143) ^ (61177078 + 61177078 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 61177078 * (5 : ZMod 4009301031143) ^ 61177078) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1851034745343 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 4009301031143) ^ 244708314 = 1597749648956 := by
        calc
          (5 : ZMod 4009301031143) ^ 244708314 = (5 : ZMod 4009301031143) ^ (122354157 + 122354157) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 122354157 * (5 : ZMod 4009301031143) ^ 122354157 := by rw [pow_add]
          _ = 1597749648956 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 4009301031143) ^ 489416629 = 2477557971387 := by
        calc
          (5 : ZMod 4009301031143) ^ 489416629 = (5 : ZMod 4009301031143) ^ (244708314 + 244708314 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 244708314 * (5 : ZMod 4009301031143) ^ 244708314) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2477557971387 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 4009301031143) ^ 978833259 = 3594492600112 := by
        calc
          (5 : ZMod 4009301031143) ^ 978833259 = (5 : ZMod 4009301031143) ^ (489416629 + 489416629 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 489416629 * (5 : ZMod 4009301031143) ^ 489416629) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3594492600112 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 4009301031143) ^ 1957666519 = 3039532867530 := by
        calc
          (5 : ZMod 4009301031143) ^ 1957666519 = (5 : ZMod 4009301031143) ^ (978833259 + 978833259 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 978833259 * (5 : ZMod 4009301031143) ^ 978833259) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3039532867530 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 4009301031143) ^ 3915333038 = 540468590953 := by
        calc
          (5 : ZMod 4009301031143) ^ 3915333038 = (5 : ZMod 4009301031143) ^ (1957666519 + 1957666519) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1957666519 * (5 : ZMod 4009301031143) ^ 1957666519 := by rw [pow_add]
          _ = 540468590953 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 4009301031143) ^ 7830666076 = 2844047426671 := by
        calc
          (5 : ZMod 4009301031143) ^ 7830666076 = (5 : ZMod 4009301031143) ^ (3915333038 + 3915333038) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 3915333038 * (5 : ZMod 4009301031143) ^ 3915333038 := by rw [pow_add]
          _ = 2844047426671 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 4009301031143) ^ 15661332152 = 434832832247 := by
        calc
          (5 : ZMod 4009301031143) ^ 15661332152 = (5 : ZMod 4009301031143) ^ (7830666076 + 7830666076) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 7830666076 * (5 : ZMod 4009301031143) ^ 7830666076 := by rw [pow_add]
          _ = 434832832247 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 4009301031143) ^ 31322664305 = 2570367235696 := by
        calc
          (5 : ZMod 4009301031143) ^ 31322664305 = (5 : ZMod 4009301031143) ^ (15661332152 + 15661332152 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 15661332152 * (5 : ZMod 4009301031143) ^ 15661332152) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2570367235696 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 4009301031143) ^ 62645328611 = 989868084543 := by
        calc
          (5 : ZMod 4009301031143) ^ 62645328611 = (5 : ZMod 4009301031143) ^ (31322664305 + 31322664305 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 31322664305 * (5 : ZMod 4009301031143) ^ 31322664305) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 989868084543 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 4009301031143) ^ 125290657223 = 3648787874019 := by
        calc
          (5 : ZMod 4009301031143) ^ 125290657223 = (5 : ZMod 4009301031143) ^ (62645328611 + 62645328611 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 62645328611 * (5 : ZMod 4009301031143) ^ 62645328611) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3648787874019 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 4009301031143) ^ 250581314446 = 3144831766790 := by
        calc
          (5 : ZMod 4009301031143) ^ 250581314446 = (5 : ZMod 4009301031143) ^ (125290657223 + 125290657223) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 125290657223 * (5 : ZMod 4009301031143) ^ 125290657223 := by rw [pow_add]
          _ = 3144831766790 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 4009301031143) ^ 501162628892 = 1744811836519 := by
        calc
          (5 : ZMod 4009301031143) ^ 501162628892 = (5 : ZMod 4009301031143) ^ (250581314446 + 250581314446) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 250581314446 * (5 : ZMod 4009301031143) ^ 250581314446 := by rw [pow_add]
          _ = 1744811836519 := by rw [factor_0_37]; decide
      have factor_0_39 : (5 : ZMod 4009301031143) ^ 1002325257785 = 3873646642477 := by
        calc
          (5 : ZMod 4009301031143) ^ 1002325257785 = (5 : ZMod 4009301031143) ^ (501162628892 + 501162628892 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 501162628892 * (5 : ZMod 4009301031143) ^ 501162628892) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3873646642477 := by rw [factor_0_38]; decide
      have factor_0_40 : (5 : ZMod 4009301031143) ^ 2004650515571 = 4009301031142 := by
        calc
          (5 : ZMod 4009301031143) ^ 2004650515571 = (5 : ZMod 4009301031143) ^ (1002325257785 + 1002325257785 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1002325257785 * (5 : ZMod 4009301031143) ^ 1002325257785) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 4009301031142 := by rw [factor_0_39]; decide
      change (5 : ZMod 4009301031143) ^ 2004650515571 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (5 : ZMod 4009301031143) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 4009301031143) ^ 2 = 25 := by
        calc
          (5 : ZMod 4009301031143) ^ 2 = (5 : ZMod 4009301031143) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1 * (5 : ZMod 4009301031143) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 4009301031143) ^ 5 = 3125 := by
        calc
          (5 : ZMod 4009301031143) ^ 5 = (5 : ZMod 4009301031143) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 2 * (5 : ZMod 4009301031143) ^ 2) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 4009301031143) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 4009301031143) ^ 10 = (5 : ZMod 4009301031143) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 5 * (5 : ZMod 4009301031143) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 4009301031143) ^ 21 = 3739636528251 := by
        calc
          (5 : ZMod 4009301031143) ^ 21 = (5 : ZMod 4009301031143) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 10 * (5 : ZMod 4009301031143) ^ 10) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3739636528251 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 4009301031143) ^ 42 = 3405974852875 := by
        calc
          (5 : ZMod 4009301031143) ^ 42 = (5 : ZMod 4009301031143) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 21 * (5 : ZMod 4009301031143) ^ 21 := by rw [pow_add]
          _ = 3405974852875 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 4009301031143) ^ 84 = 433465272634 := by
        calc
          (5 : ZMod 4009301031143) ^ 84 = (5 : ZMod 4009301031143) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 42 * (5 : ZMod 4009301031143) ^ 42 := by rw [pow_add]
          _ = 433465272634 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 4009301031143) ^ 169 = 37156151913 := by
        calc
          (5 : ZMod 4009301031143) ^ 169 = (5 : ZMod 4009301031143) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 84 * (5 : ZMod 4009301031143) ^ 84) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 37156151913 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 4009301031143) ^ 339 = 3478523047690 := by
        calc
          (5 : ZMod 4009301031143) ^ 339 = (5 : ZMod 4009301031143) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 169 * (5 : ZMod 4009301031143) ^ 169) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3478523047690 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 4009301031143) ^ 678 = 3404138904368 := by
        calc
          (5 : ZMod 4009301031143) ^ 678 = (5 : ZMod 4009301031143) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 339 * (5 : ZMod 4009301031143) ^ 339 := by rw [pow_add]
          _ = 3404138904368 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 4009301031143) ^ 1357 = 2570536208181 := by
        calc
          (5 : ZMod 4009301031143) ^ 1357 = (5 : ZMod 4009301031143) ^ (678 + 678 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 678 * (5 : ZMod 4009301031143) ^ 678) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2570536208181 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 4009301031143) ^ 2715 = 1854066731691 := by
        calc
          (5 : ZMod 4009301031143) ^ 2715 = (5 : ZMod 4009301031143) ^ (1357 + 1357 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1357 * (5 : ZMod 4009301031143) ^ 1357) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1854066731691 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 4009301031143) ^ 5431 = 2061508698623 := by
        calc
          (5 : ZMod 4009301031143) ^ 5431 = (5 : ZMod 4009301031143) ^ (2715 + 2715 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 2715 * (5 : ZMod 4009301031143) ^ 2715) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2061508698623 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 4009301031143) ^ 10862 = 3280113432538 := by
        calc
          (5 : ZMod 4009301031143) ^ 10862 = (5 : ZMod 4009301031143) ^ (5431 + 5431) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 5431 * (5 : ZMod 4009301031143) ^ 5431 := by rw [pow_add]
          _ = 3280113432538 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 4009301031143) ^ 21724 = 2485980500569 := by
        calc
          (5 : ZMod 4009301031143) ^ 21724 = (5 : ZMod 4009301031143) ^ (10862 + 10862) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 10862 * (5 : ZMod 4009301031143) ^ 10862 := by rw [pow_add]
          _ = 2485980500569 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 4009301031143) ^ 43449 = 496728884418 := by
        calc
          (5 : ZMod 4009301031143) ^ 43449 = (5 : ZMod 4009301031143) ^ (21724 + 21724 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 21724 * (5 : ZMod 4009301031143) ^ 21724) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 496728884418 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 4009301031143) ^ 86899 = 3734940928467 := by
        calc
          (5 : ZMod 4009301031143) ^ 86899 = (5 : ZMod 4009301031143) ^ (43449 + 43449 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 43449 * (5 : ZMod 4009301031143) ^ 43449) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3734940928467 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 4009301031143) ^ 173798 = 1854112034627 := by
        calc
          (5 : ZMod 4009301031143) ^ 173798 = (5 : ZMod 4009301031143) ^ (86899 + 86899) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 86899 * (5 : ZMod 4009301031143) ^ 86899 := by rw [pow_add]
          _ = 1854112034627 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 4009301031143) ^ 347597 = 3279716813708 := by
        calc
          (5 : ZMod 4009301031143) ^ 347597 = (5 : ZMod 4009301031143) ^ (173798 + 173798 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 173798 * (5 : ZMod 4009301031143) ^ 173798) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3279716813708 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 4009301031143) ^ 695194 = 3194601734835 := by
        calc
          (5 : ZMod 4009301031143) ^ 695194 = (5 : ZMod 4009301031143) ^ (347597 + 347597) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 347597 * (5 : ZMod 4009301031143) ^ 347597 := by rw [pow_add]
          _ = 3194601734835 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 4009301031143) ^ 1390388 = 505212918545 := by
        calc
          (5 : ZMod 4009301031143) ^ 1390388 = (5 : ZMod 4009301031143) ^ (695194 + 695194) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 695194 * (5 : ZMod 4009301031143) ^ 695194 := by rw [pow_add]
          _ = 505212918545 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 4009301031143) ^ 2780776 = 3833344606922 := by
        calc
          (5 : ZMod 4009301031143) ^ 2780776 = (5 : ZMod 4009301031143) ^ (1390388 + 1390388) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1390388 * (5 : ZMod 4009301031143) ^ 1390388 := by rw [pow_add]
          _ = 3833344606922 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 4009301031143) ^ 5561552 = 3941962486030 := by
        calc
          (5 : ZMod 4009301031143) ^ 5561552 = (5 : ZMod 4009301031143) ^ (2780776 + 2780776) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 2780776 * (5 : ZMod 4009301031143) ^ 2780776 := by rw [pow_add]
          _ = 3941962486030 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 4009301031143) ^ 11123105 = 313707008080 := by
        calc
          (5 : ZMod 4009301031143) ^ 11123105 = (5 : ZMod 4009301031143) ^ (5561552 + 5561552 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 5561552 * (5 : ZMod 4009301031143) ^ 5561552) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 313707008080 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 4009301031143) ^ 22246210 = 1608609610389 := by
        calc
          (5 : ZMod 4009301031143) ^ 22246210 = (5 : ZMod 4009301031143) ^ (11123105 + 11123105) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 11123105 * (5 : ZMod 4009301031143) ^ 11123105 := by rw [pow_add]
          _ = 1608609610389 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 4009301031143) ^ 44492420 = 3091412932817 := by
        calc
          (5 : ZMod 4009301031143) ^ 44492420 = (5 : ZMod 4009301031143) ^ (22246210 + 22246210) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 22246210 * (5 : ZMod 4009301031143) ^ 22246210 := by rw [pow_add]
          _ = 3091412932817 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 4009301031143) ^ 88984841 = 3997288923204 := by
        calc
          (5 : ZMod 4009301031143) ^ 88984841 = (5 : ZMod 4009301031143) ^ (44492420 + 44492420 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 44492420 * (5 : ZMod 4009301031143) ^ 44492420) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3997288923204 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 4009301031143) ^ 177969683 = 3623304941319 := by
        calc
          (5 : ZMod 4009301031143) ^ 177969683 = (5 : ZMod 4009301031143) ^ (88984841 + 88984841 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 88984841 * (5 : ZMod 4009301031143) ^ 88984841) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3623304941319 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 4009301031143) ^ 355939367 = 1251649397098 := by
        calc
          (5 : ZMod 4009301031143) ^ 355939367 = (5 : ZMod 4009301031143) ^ (177969683 + 177969683 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 177969683 * (5 : ZMod 4009301031143) ^ 177969683) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1251649397098 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 4009301031143) ^ 711878734 = 1567792392237 := by
        calc
          (5 : ZMod 4009301031143) ^ 711878734 = (5 : ZMod 4009301031143) ^ (355939367 + 355939367) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 355939367 * (5 : ZMod 4009301031143) ^ 355939367 := by rw [pow_add]
          _ = 1567792392237 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 4009301031143) ^ 1423757468 = 3504263138193 := by
        calc
          (5 : ZMod 4009301031143) ^ 1423757468 = (5 : ZMod 4009301031143) ^ (711878734 + 711878734) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 711878734 * (5 : ZMod 4009301031143) ^ 711878734 := by rw [pow_add]
          _ = 3504263138193 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 4009301031143) ^ 2847514936 = 127167030738 := by
        calc
          (5 : ZMod 4009301031143) ^ 2847514936 = (5 : ZMod 4009301031143) ^ (1423757468 + 1423757468) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1423757468 * (5 : ZMod 4009301031143) ^ 1423757468 := by rw [pow_add]
          _ = 127167030738 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 4009301031143) ^ 5695029873 = 3213663724552 := by
        calc
          (5 : ZMod 4009301031143) ^ 5695029873 = (5 : ZMod 4009301031143) ^ (2847514936 + 2847514936 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 2847514936 * (5 : ZMod 4009301031143) ^ 2847514936) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3213663724552 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 4009301031143) ^ 11390059747 = 3568128071511 := by
        calc
          (5 : ZMod 4009301031143) ^ 11390059747 = (5 : ZMod 4009301031143) ^ (5695029873 + 5695029873 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 5695029873 * (5 : ZMod 4009301031143) ^ 5695029873) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3568128071511 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 4009301031143) ^ 22780119495 = 1174644590661 := by
        calc
          (5 : ZMod 4009301031143) ^ 22780119495 = (5 : ZMod 4009301031143) ^ (11390059747 + 11390059747 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 11390059747 * (5 : ZMod 4009301031143) ^ 11390059747) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1174644590661 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 4009301031143) ^ 45560238990 = 2140493745846 := by
        calc
          (5 : ZMod 4009301031143) ^ 45560238990 = (5 : ZMod 4009301031143) ^ (22780119495 + 22780119495) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 22780119495 * (5 : ZMod 4009301031143) ^ 22780119495 := by rw [pow_add]
          _ = 2140493745846 := by rw [factor_1_34]; decide
      have factor_1_36 : (5 : ZMod 4009301031143) ^ 91120477980 = 2158563016926 := by
        calc
          (5 : ZMod 4009301031143) ^ 91120477980 = (5 : ZMod 4009301031143) ^ (45560238990 + 45560238990) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 45560238990 * (5 : ZMod 4009301031143) ^ 45560238990 := by rw [pow_add]
          _ = 2158563016926 := by rw [factor_1_35]; decide
      have factor_1_37 : (5 : ZMod 4009301031143) ^ 182240955961 = 528206759942 := by
        calc
          (5 : ZMod 4009301031143) ^ 182240955961 = (5 : ZMod 4009301031143) ^ (91120477980 + 91120477980 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 91120477980 * (5 : ZMod 4009301031143) ^ 91120477980) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 528206759942 := by rw [factor_1_36]; decide
      have factor_1_38 : (5 : ZMod 4009301031143) ^ 364481911922 = 2344381828871 := by
        calc
          (5 : ZMod 4009301031143) ^ 364481911922 = (5 : ZMod 4009301031143) ^ (182240955961 + 182240955961) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 182240955961 * (5 : ZMod 4009301031143) ^ 182240955961 := by rw [pow_add]
          _ = 2344381828871 := by rw [factor_1_37]; decide
      change (5 : ZMod 4009301031143) ^ 364481911922 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (5 : ZMod 4009301031143) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 4009301031143) ^ 3 = 125 := by
        calc
          (5 : ZMod 4009301031143) ^ 3 = (5 : ZMod 4009301031143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1 * (5 : ZMod 4009301031143) ^ 1) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 4009301031143) ^ 6 = 15625 := by
        calc
          (5 : ZMod 4009301031143) ^ 6 = (5 : ZMod 4009301031143) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 3 * (5 : ZMod 4009301031143) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 4009301031143) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 4009301031143) ^ 13 = (5 : ZMod 4009301031143) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 6 * (5 : ZMod 4009301031143) ^ 6) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 4009301031143) ^ 27 = 267526043793 := by
        calc
          (5 : ZMod 4009301031143) ^ 27 = (5 : ZMod 4009301031143) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 13 * (5 : ZMod 4009301031143) ^ 13) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 267526043793 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 4009301031143) ^ 54 = 1374922804883 := by
        calc
          (5 : ZMod 4009301031143) ^ 54 = (5 : ZMod 4009301031143) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 27 * (5 : ZMod 4009301031143) ^ 27 := by rw [pow_add]
          _ = 1374922804883 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 4009301031143) ^ 109 = 2524319162604 := by
        calc
          (5 : ZMod 4009301031143) ^ 109 = (5 : ZMod 4009301031143) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 54 * (5 : ZMod 4009301031143) ^ 54) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2524319162604 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 4009301031143) ^ 219 = 2562372232995 := by
        calc
          (5 : ZMod 4009301031143) ^ 219 = (5 : ZMod 4009301031143) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 109 * (5 : ZMod 4009301031143) ^ 109) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2562372232995 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 4009301031143) ^ 439 = 831920181763 := by
        calc
          (5 : ZMod 4009301031143) ^ 439 = (5 : ZMod 4009301031143) ^ (219 + 219 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 219 * (5 : ZMod 4009301031143) ^ 219) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 831920181763 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 4009301031143) ^ 878 = 1449617530750 := by
        calc
          (5 : ZMod 4009301031143) ^ 878 = (5 : ZMod 4009301031143) ^ (439 + 439) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 439 * (5 : ZMod 4009301031143) ^ 439 := by rw [pow_add]
          _ = 1449617530750 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 4009301031143) ^ 1757 = 3380483233000 := by
        calc
          (5 : ZMod 4009301031143) ^ 1757 = (5 : ZMod 4009301031143) ^ (878 + 878 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 878 * (5 : ZMod 4009301031143) ^ 878) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3380483233000 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 4009301031143) ^ 3514 = 3159521144099 := by
        calc
          (5 : ZMod 4009301031143) ^ 3514 = (5 : ZMod 4009301031143) ^ (1757 + 1757) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1757 * (5 : ZMod 4009301031143) ^ 1757 := by rw [pow_add]
          _ = 3159521144099 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 4009301031143) ^ 7028 = 124910004543 := by
        calc
          (5 : ZMod 4009301031143) ^ 7028 = (5 : ZMod 4009301031143) ^ (3514 + 3514) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 3514 * (5 : ZMod 4009301031143) ^ 3514 := by rw [pow_add]
          _ = 124910004543 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 4009301031143) ^ 14057 = 3861946880541 := by
        calc
          (5 : ZMod 4009301031143) ^ 14057 = (5 : ZMod 4009301031143) ^ (7028 + 7028 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 7028 * (5 : ZMod 4009301031143) ^ 7028) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3861946880541 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 4009301031143) ^ 28114 = 1364793246335 := by
        calc
          (5 : ZMod 4009301031143) ^ 28114 = (5 : ZMod 4009301031143) ^ (14057 + 14057) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 14057 * (5 : ZMod 4009301031143) ^ 14057 := by rw [pow_add]
          _ = 1364793246335 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 4009301031143) ^ 56228 = 1193610956265 := by
        calc
          (5 : ZMod 4009301031143) ^ 56228 = (5 : ZMod 4009301031143) ^ (28114 + 28114) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 28114 * (5 : ZMod 4009301031143) ^ 28114 := by rw [pow_add]
          _ = 1193610956265 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 4009301031143) ^ 112457 = 685046356826 := by
        calc
          (5 : ZMod 4009301031143) ^ 112457 = (5 : ZMod 4009301031143) ^ (56228 + 56228 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 56228 * (5 : ZMod 4009301031143) ^ 56228) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 685046356826 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 4009301031143) ^ 224915 = 777080847646 := by
        calc
          (5 : ZMod 4009301031143) ^ 224915 = (5 : ZMod 4009301031143) ^ (112457 + 112457 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 112457 * (5 : ZMod 4009301031143) ^ 112457) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 777080847646 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 4009301031143) ^ 449831 = 2786113114968 := by
        calc
          (5 : ZMod 4009301031143) ^ 449831 = (5 : ZMod 4009301031143) ^ (224915 + 224915 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 224915 * (5 : ZMod 4009301031143) ^ 224915) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2786113114968 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 4009301031143) ^ 899662 = 1104310049312 := by
        calc
          (5 : ZMod 4009301031143) ^ 899662 = (5 : ZMod 4009301031143) ^ (449831 + 449831) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 449831 * (5 : ZMod 4009301031143) ^ 449831 := by rw [pow_add]
          _ = 1104310049312 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 4009301031143) ^ 1799325 = 1514978344099 := by
        calc
          (5 : ZMod 4009301031143) ^ 1799325 = (5 : ZMod 4009301031143) ^ (899662 + 899662 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 899662 * (5 : ZMod 4009301031143) ^ 899662) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1514978344099 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 4009301031143) ^ 3598651 = 973494822684 := by
        calc
          (5 : ZMod 4009301031143) ^ 3598651 = (5 : ZMod 4009301031143) ^ (1799325 + 1799325 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 1799325 * (5 : ZMod 4009301031143) ^ 1799325) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 973494822684 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 4009301031143) ^ 7197303 = 1039706387474 := by
        calc
          (5 : ZMod 4009301031143) ^ 7197303 = (5 : ZMod 4009301031143) ^ (3598651 + 3598651 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 3598651 * (5 : ZMod 4009301031143) ^ 3598651) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1039706387474 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 4009301031143) ^ 14394606 = 404027239806 := by
        calc
          (5 : ZMod 4009301031143) ^ 14394606 = (5 : ZMod 4009301031143) ^ (7197303 + 7197303) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 7197303 * (5 : ZMod 4009301031143) ^ 7197303 := by rw [pow_add]
          _ = 404027239806 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 4009301031143) ^ 28789213 = 2221025718644 := by
        calc
          (5 : ZMod 4009301031143) ^ 28789213 = (5 : ZMod 4009301031143) ^ (14394606 + 14394606 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 14394606 * (5 : ZMod 4009301031143) ^ 14394606) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2221025718644 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 4009301031143) ^ 57578427 = 1931849054959 := by
        calc
          (5 : ZMod 4009301031143) ^ 57578427 = (5 : ZMod 4009301031143) ^ (28789213 + 28789213 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 28789213 * (5 : ZMod 4009301031143) ^ 28789213) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1931849054959 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 4009301031143) ^ 115156854 = 1559140983611 := by
        calc
          (5 : ZMod 4009301031143) ^ 115156854 = (5 : ZMod 4009301031143) ^ (57578427 + 57578427) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 57578427 * (5 : ZMod 4009301031143) ^ 57578427 := by rw [pow_add]
          _ = 1559140983611 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 4009301031143) ^ 230313708 = 88552086079 := by
        calc
          (5 : ZMod 4009301031143) ^ 230313708 = (5 : ZMod 4009301031143) ^ (115156854 + 115156854) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 115156854 * (5 : ZMod 4009301031143) ^ 115156854 := by rw [pow_add]
          _ = 88552086079 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 4009301031143) ^ 460627416 = 343016074498 := by
        calc
          (5 : ZMod 4009301031143) ^ 460627416 = (5 : ZMod 4009301031143) ^ (230313708 + 230313708) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 230313708 * (5 : ZMod 4009301031143) ^ 230313708 := by rw [pow_add]
          _ = 343016074498 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 4009301031143) ^ 921254832 = 531048882284 := by
        calc
          (5 : ZMod 4009301031143) ^ 921254832 = (5 : ZMod 4009301031143) ^ (460627416 + 460627416) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 460627416 * (5 : ZMod 4009301031143) ^ 460627416 := by rw [pow_add]
          _ = 531048882284 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 4009301031143) ^ 1842509665 = 3747699255440 := by
        calc
          (5 : ZMod 4009301031143) ^ 1842509665 = (5 : ZMod 4009301031143) ^ (921254832 + 921254832 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 921254832 * (5 : ZMod 4009301031143) ^ 921254832) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3747699255440 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 4009301031143) ^ 3685019330 = 1464971682207 := by
        calc
          (5 : ZMod 4009301031143) ^ 3685019330 = (5 : ZMod 4009301031143) ^ (1842509665 + 1842509665) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1842509665 * (5 : ZMod 4009301031143) ^ 1842509665 := by rw [pow_add]
          _ = 1464971682207 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 4009301031143) ^ 7370038660 = 1078972883667 := by
        calc
          (5 : ZMod 4009301031143) ^ 7370038660 = (5 : ZMod 4009301031143) ^ (3685019330 + 3685019330) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 3685019330 * (5 : ZMod 4009301031143) ^ 3685019330 := by rw [pow_add]
          _ = 1078972883667 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 4009301031143) ^ 14740077320 = 3535157172488 := by
        calc
          (5 : ZMod 4009301031143) ^ 14740077320 = (5 : ZMod 4009301031143) ^ (7370038660 + 7370038660) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 7370038660 * (5 : ZMod 4009301031143) ^ 7370038660 := by rw [pow_add]
          _ = 3535157172488 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 4009301031143) ^ 29480154640 = 1022364193860 := by
        calc
          (5 : ZMod 4009301031143) ^ 29480154640 = (5 : ZMod 4009301031143) ^ (14740077320 + 14740077320) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 14740077320 * (5 : ZMod 4009301031143) ^ 14740077320 := by rw [pow_add]
          _ = 1022364193860 := by rw [factor_2_33]; decide
      have factor_2_35 : (5 : ZMod 4009301031143) ^ 58960309281 = 319676291048 := by
        calc
          (5 : ZMod 4009301031143) ^ 58960309281 = (5 : ZMod 4009301031143) ^ (29480154640 + 29480154640 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 29480154640 * (5 : ZMod 4009301031143) ^ 29480154640) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 319676291048 := by rw [factor_2_34]; decide
      have factor_2_36 : (5 : ZMod 4009301031143) ^ 117920618563 = 2842782682126 := by
        calc
          (5 : ZMod 4009301031143) ^ 117920618563 = (5 : ZMod 4009301031143) ^ (58960309281 + 58960309281 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 58960309281 * (5 : ZMod 4009301031143) ^ 58960309281) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 2842782682126 := by rw [factor_2_35]; decide
      have factor_2_37 : (5 : ZMod 4009301031143) ^ 235841237126 = 2945093447525 := by
        calc
          (5 : ZMod 4009301031143) ^ 235841237126 = (5 : ZMod 4009301031143) ^ (117920618563 + 117920618563) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 117920618563 * (5 : ZMod 4009301031143) ^ 117920618563 := by rw [pow_add]
          _ = 2945093447525 := by rw [factor_2_36]; decide
      change (5 : ZMod 4009301031143) ^ 235841237126 ≠ 1
      rw [factor_2_37]
      decide
    ·
      have factor_3_0 : (5 : ZMod 4009301031143) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 4009301031143) ^ 2 = 25 := by
        calc
          (5 : ZMod 4009301031143) ^ 2 = (5 : ZMod 4009301031143) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 1 * (5 : ZMod 4009301031143) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 4009301031143) ^ 5 = 3125 := by
        calc
          (5 : ZMod 4009301031143) ^ 5 = (5 : ZMod 4009301031143) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 2 * (5 : ZMod 4009301031143) ^ 2) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 4009301031143) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 4009301031143) ^ 11 = (5 : ZMod 4009301031143) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 5 * (5 : ZMod 4009301031143) ^ 5) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 4009301031143) ^ 23 = 1276989489986 := by
        calc
          (5 : ZMod 4009301031143) ^ 23 = (5 : ZMod 4009301031143) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 11 * (5 : ZMod 4009301031143) ^ 11) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1276989489986 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 4009301031143) ^ 46 = 3804736541085 := by
        calc
          (5 : ZMod 4009301031143) ^ 46 = (5 : ZMod 4009301031143) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 23 * (5 : ZMod 4009301031143) ^ 23 := by rw [pow_add]
          _ = 3804736541085 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 4009301031143) ^ 93 = 3845576094227 := by
        calc
          (5 : ZMod 4009301031143) ^ 93 = (5 : ZMod 4009301031143) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 46 * (5 : ZMod 4009301031143) ^ 46) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 3845576094227 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 4009301031143) ^ 187 = 1429787689808 := by
        calc
          (5 : ZMod 4009301031143) ^ 187 = (5 : ZMod 4009301031143) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = ((5 : ZMod 4009301031143) ^ 93 * (5 : ZMod 4009301031143) ^ 93) * (5 : ZMod 4009301031143) := by rw [pow_succ, pow_add]
          _ = 1429787689808 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 4009301031143) ^ 374 = 2114836579522 := by
        calc
          (5 : ZMod 4009301031143) ^ 374 = (5 : ZMod 4009301031143) ^ (187 + 187) :=
            congrArg (fun n : ℕ => (5 : ZMod 4009301031143) ^ n) (by norm_num)
          _ = (5 : ZMod 4009301031143) ^ 187 * (5 : ZMod 4009301031143) ^ 187 := by rw [pow_add]
          _ = 2114836579522 := by rw [factor_3_7]; decide
      change (5 : ZMod 4009301031143) ^ 374 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_4009301031143

end TotientTailPeriodKiller
end Erdos249257
