import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime123940483

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_495761933 : Nat.Prime 495761933 := by
  apply lucas_primality 495761933 (2 : ZMod 495761933)
  ·
      have fermat_0 : (2 : ZMod 495761933) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 495761933) ^ 3 = 8 := by
        calc
          (2 : ZMod 495761933) ^ 3 = (2 : ZMod 495761933) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 1 * (2 : ZMod 495761933) ^ 1) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 495761933) ^ 7 = 128 := by
        calc
          (2 : ZMod 495761933) ^ 7 = (2 : ZMod 495761933) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 3 * (2 : ZMod 495761933) ^ 3) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 495761933) ^ 14 = 16384 := by
        calc
          (2 : ZMod 495761933) ^ 14 = (2 : ZMod 495761933) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 7 * (2 : ZMod 495761933) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 495761933) ^ 29 = 41108979 := by
        calc
          (2 : ZMod 495761933) ^ 29 = (2 : ZMod 495761933) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 14 * (2 : ZMod 495761933) ^ 14) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 41108979 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 495761933) ^ 59 = 165424675 := by
        calc
          (2 : ZMod 495761933) ^ 59 = (2 : ZMod 495761933) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 29 * (2 : ZMod 495761933) ^ 29) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 165424675 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 495761933) ^ 118 = 107964197 := by
        calc
          (2 : ZMod 495761933) ^ 118 = (2 : ZMod 495761933) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 59 * (2 : ZMod 495761933) ^ 59 := by rw [pow_add]
          _ = 107964197 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 495761933) ^ 236 = 23497084 := by
        calc
          (2 : ZMod 495761933) ^ 236 = (2 : ZMod 495761933) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 118 * (2 : ZMod 495761933) ^ 118 := by rw [pow_add]
          _ = 23497084 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 495761933) ^ 472 = 243388611 := by
        calc
          (2 : ZMod 495761933) ^ 472 = (2 : ZMod 495761933) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 236 * (2 : ZMod 495761933) ^ 236 := by rw [pow_add]
          _ = 243388611 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 495761933) ^ 945 = 305982532 := by
        calc
          (2 : ZMod 495761933) ^ 945 = (2 : ZMod 495761933) ^ (472 + 472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 472 * (2 : ZMod 495761933) ^ 472) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 305982532 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 495761933) ^ 1891 = 118466814 := by
        calc
          (2 : ZMod 495761933) ^ 1891 = (2 : ZMod 495761933) ^ (945 + 945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 945 * (2 : ZMod 495761933) ^ 945) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 118466814 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 495761933) ^ 3782 = 271354836 := by
        calc
          (2 : ZMod 495761933) ^ 3782 = (2 : ZMod 495761933) ^ (1891 + 1891) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 1891 * (2 : ZMod 495761933) ^ 1891 := by rw [pow_add]
          _ = 271354836 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 495761933) ^ 7564 = 388500702 := by
        calc
          (2 : ZMod 495761933) ^ 7564 = (2 : ZMod 495761933) ^ (3782 + 3782) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 3782 * (2 : ZMod 495761933) ^ 3782 := by rw [pow_add]
          _ = 388500702 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 495761933) ^ 15129 = 488219219 := by
        calc
          (2 : ZMod 495761933) ^ 15129 = (2 : ZMod 495761933) ^ (7564 + 7564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 7564 * (2 : ZMod 495761933) ^ 7564) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 488219219 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 495761933) ^ 30258 = 382340515 := by
        calc
          (2 : ZMod 495761933) ^ 30258 = (2 : ZMod 495761933) ^ (15129 + 15129) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 15129 * (2 : ZMod 495761933) ^ 15129 := by rw [pow_add]
          _ = 382340515 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 495761933) ^ 60517 = 467154102 := by
        calc
          (2 : ZMod 495761933) ^ 60517 = (2 : ZMod 495761933) ^ (30258 + 30258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 30258 * (2 : ZMod 495761933) ^ 30258) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 467154102 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 495761933) ^ 121035 = 458865394 := by
        calc
          (2 : ZMod 495761933) ^ 121035 = (2 : ZMod 495761933) ^ (60517 + 60517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 60517 * (2 : ZMod 495761933) ^ 60517) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 458865394 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 495761933) ^ 242071 = 12940965 := by
        calc
          (2 : ZMod 495761933) ^ 242071 = (2 : ZMod 495761933) ^ (121035 + 121035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 121035 * (2 : ZMod 495761933) ^ 121035) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 12940965 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 495761933) ^ 484142 = 194163825 := by
        calc
          (2 : ZMod 495761933) ^ 484142 = (2 : ZMod 495761933) ^ (242071 + 242071) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 242071 * (2 : ZMod 495761933) ^ 242071 := by rw [pow_add]
          _ = 194163825 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 495761933) ^ 968285 = 294648209 := by
        calc
          (2 : ZMod 495761933) ^ 968285 = (2 : ZMod 495761933) ^ (484142 + 484142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 484142 * (2 : ZMod 495761933) ^ 484142) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 294648209 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 495761933) ^ 1936570 = 113772171 := by
        calc
          (2 : ZMod 495761933) ^ 1936570 = (2 : ZMod 495761933) ^ (968285 + 968285) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 968285 * (2 : ZMod 495761933) ^ 968285 := by rw [pow_add]
          _ = 113772171 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 495761933) ^ 3873140 = 293389148 := by
        calc
          (2 : ZMod 495761933) ^ 3873140 = (2 : ZMod 495761933) ^ (1936570 + 1936570) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 1936570 * (2 : ZMod 495761933) ^ 1936570 := by rw [pow_add]
          _ = 293389148 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 495761933) ^ 7746280 = 47868058 := by
        calc
          (2 : ZMod 495761933) ^ 7746280 = (2 : ZMod 495761933) ^ (3873140 + 3873140) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 3873140 * (2 : ZMod 495761933) ^ 3873140 := by rw [pow_add]
          _ = 47868058 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 495761933) ^ 15492560 = 301083123 := by
        calc
          (2 : ZMod 495761933) ^ 15492560 = (2 : ZMod 495761933) ^ (7746280 + 7746280) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 7746280 * (2 : ZMod 495761933) ^ 7746280 := by rw [pow_add]
          _ = 301083123 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 495761933) ^ 30985120 = 359613186 := by
        calc
          (2 : ZMod 495761933) ^ 30985120 = (2 : ZMod 495761933) ^ (15492560 + 15492560) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 15492560 * (2 : ZMod 495761933) ^ 15492560 := by rw [pow_add]
          _ = 359613186 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 495761933) ^ 61970241 = 286368474 := by
        calc
          (2 : ZMod 495761933) ^ 61970241 = (2 : ZMod 495761933) ^ (30985120 + 30985120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 30985120 * (2 : ZMod 495761933) ^ 30985120) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 286368474 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 495761933) ^ 123940483 = 76975014 := by
        calc
          (2 : ZMod 495761933) ^ 123940483 = (2 : ZMod 495761933) ^ (61970241 + 61970241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 61970241 * (2 : ZMod 495761933) ^ 61970241) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 76975014 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 495761933) ^ 247880966 = 495761932 := by
        calc
          (2 : ZMod 495761933) ^ 247880966 = (2 : ZMod 495761933) ^ (123940483 + 123940483) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 123940483 * (2 : ZMod 495761933) ^ 123940483 := by rw [pow_add]
          _ = 495761932 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 495761933) ^ 495761932 = 1 := by
        calc
          (2 : ZMod 495761933) ^ 495761932 = (2 : ZMod 495761933) ^ (247880966 + 247880966) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 247880966 * (2 : ZMod 495761933) ^ 247880966 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (123940483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (123940483, 1)] : List FactorBlock).map factorBlockValue).prod = 495761933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_123940483) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 495761933) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 495761933) ^ 3 = 8 := by
        calc
          (2 : ZMod 495761933) ^ 3 = (2 : ZMod 495761933) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 1 * (2 : ZMod 495761933) ^ 1) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 495761933) ^ 7 = 128 := by
        calc
          (2 : ZMod 495761933) ^ 7 = (2 : ZMod 495761933) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 3 * (2 : ZMod 495761933) ^ 3) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 495761933) ^ 14 = 16384 := by
        calc
          (2 : ZMod 495761933) ^ 14 = (2 : ZMod 495761933) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 7 * (2 : ZMod 495761933) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 495761933) ^ 29 = 41108979 := by
        calc
          (2 : ZMod 495761933) ^ 29 = (2 : ZMod 495761933) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 14 * (2 : ZMod 495761933) ^ 14) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 41108979 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 495761933) ^ 59 = 165424675 := by
        calc
          (2 : ZMod 495761933) ^ 59 = (2 : ZMod 495761933) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 29 * (2 : ZMod 495761933) ^ 29) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 165424675 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 495761933) ^ 118 = 107964197 := by
        calc
          (2 : ZMod 495761933) ^ 118 = (2 : ZMod 495761933) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 59 * (2 : ZMod 495761933) ^ 59 := by rw [pow_add]
          _ = 107964197 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 495761933) ^ 236 = 23497084 := by
        calc
          (2 : ZMod 495761933) ^ 236 = (2 : ZMod 495761933) ^ (118 + 118) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 118 * (2 : ZMod 495761933) ^ 118 := by rw [pow_add]
          _ = 23497084 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 495761933) ^ 472 = 243388611 := by
        calc
          (2 : ZMod 495761933) ^ 472 = (2 : ZMod 495761933) ^ (236 + 236) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 236 * (2 : ZMod 495761933) ^ 236 := by rw [pow_add]
          _ = 243388611 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 495761933) ^ 945 = 305982532 := by
        calc
          (2 : ZMod 495761933) ^ 945 = (2 : ZMod 495761933) ^ (472 + 472 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 472 * (2 : ZMod 495761933) ^ 472) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 305982532 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 495761933) ^ 1891 = 118466814 := by
        calc
          (2 : ZMod 495761933) ^ 1891 = (2 : ZMod 495761933) ^ (945 + 945 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 945 * (2 : ZMod 495761933) ^ 945) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 118466814 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 495761933) ^ 3782 = 271354836 := by
        calc
          (2 : ZMod 495761933) ^ 3782 = (2 : ZMod 495761933) ^ (1891 + 1891) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 1891 * (2 : ZMod 495761933) ^ 1891 := by rw [pow_add]
          _ = 271354836 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 495761933) ^ 7564 = 388500702 := by
        calc
          (2 : ZMod 495761933) ^ 7564 = (2 : ZMod 495761933) ^ (3782 + 3782) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 3782 * (2 : ZMod 495761933) ^ 3782 := by rw [pow_add]
          _ = 388500702 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 495761933) ^ 15129 = 488219219 := by
        calc
          (2 : ZMod 495761933) ^ 15129 = (2 : ZMod 495761933) ^ (7564 + 7564 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 7564 * (2 : ZMod 495761933) ^ 7564) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 488219219 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 495761933) ^ 30258 = 382340515 := by
        calc
          (2 : ZMod 495761933) ^ 30258 = (2 : ZMod 495761933) ^ (15129 + 15129) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 15129 * (2 : ZMod 495761933) ^ 15129 := by rw [pow_add]
          _ = 382340515 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 495761933) ^ 60517 = 467154102 := by
        calc
          (2 : ZMod 495761933) ^ 60517 = (2 : ZMod 495761933) ^ (30258 + 30258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 30258 * (2 : ZMod 495761933) ^ 30258) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 467154102 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 495761933) ^ 121035 = 458865394 := by
        calc
          (2 : ZMod 495761933) ^ 121035 = (2 : ZMod 495761933) ^ (60517 + 60517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 60517 * (2 : ZMod 495761933) ^ 60517) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 458865394 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 495761933) ^ 242071 = 12940965 := by
        calc
          (2 : ZMod 495761933) ^ 242071 = (2 : ZMod 495761933) ^ (121035 + 121035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 121035 * (2 : ZMod 495761933) ^ 121035) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 12940965 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 495761933) ^ 484142 = 194163825 := by
        calc
          (2 : ZMod 495761933) ^ 484142 = (2 : ZMod 495761933) ^ (242071 + 242071) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 242071 * (2 : ZMod 495761933) ^ 242071 := by rw [pow_add]
          _ = 194163825 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 495761933) ^ 968285 = 294648209 := by
        calc
          (2 : ZMod 495761933) ^ 968285 = (2 : ZMod 495761933) ^ (484142 + 484142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 484142 * (2 : ZMod 495761933) ^ 484142) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 294648209 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 495761933) ^ 1936570 = 113772171 := by
        calc
          (2 : ZMod 495761933) ^ 1936570 = (2 : ZMod 495761933) ^ (968285 + 968285) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 968285 * (2 : ZMod 495761933) ^ 968285 := by rw [pow_add]
          _ = 113772171 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 495761933) ^ 3873140 = 293389148 := by
        calc
          (2 : ZMod 495761933) ^ 3873140 = (2 : ZMod 495761933) ^ (1936570 + 1936570) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 1936570 * (2 : ZMod 495761933) ^ 1936570 := by rw [pow_add]
          _ = 293389148 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 495761933) ^ 7746280 = 47868058 := by
        calc
          (2 : ZMod 495761933) ^ 7746280 = (2 : ZMod 495761933) ^ (3873140 + 3873140) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 3873140 * (2 : ZMod 495761933) ^ 3873140 := by rw [pow_add]
          _ = 47868058 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 495761933) ^ 15492560 = 301083123 := by
        calc
          (2 : ZMod 495761933) ^ 15492560 = (2 : ZMod 495761933) ^ (7746280 + 7746280) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 7746280 * (2 : ZMod 495761933) ^ 7746280 := by rw [pow_add]
          _ = 301083123 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 495761933) ^ 30985120 = 359613186 := by
        calc
          (2 : ZMod 495761933) ^ 30985120 = (2 : ZMod 495761933) ^ (15492560 + 15492560) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 15492560 * (2 : ZMod 495761933) ^ 15492560 := by rw [pow_add]
          _ = 359613186 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 495761933) ^ 61970241 = 286368474 := by
        calc
          (2 : ZMod 495761933) ^ 61970241 = (2 : ZMod 495761933) ^ (30985120 + 30985120 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 30985120 * (2 : ZMod 495761933) ^ 30985120) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 286368474 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 495761933) ^ 123940483 = 76975014 := by
        calc
          (2 : ZMod 495761933) ^ 123940483 = (2 : ZMod 495761933) ^ (61970241 + 61970241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = ((2 : ZMod 495761933) ^ 61970241 * (2 : ZMod 495761933) ^ 61970241) * (2 : ZMod 495761933) := by rw [pow_succ, pow_add]
          _ = 76975014 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 495761933) ^ 247880966 = 495761932 := by
        calc
          (2 : ZMod 495761933) ^ 247880966 = (2 : ZMod 495761933) ^ (123940483 + 123940483) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 123940483 * (2 : ZMod 495761933) ^ 123940483 := by rw [pow_add]
          _ = 495761932 := by rw [factor_0_26]; decide
      change (2 : ZMod 495761933) ^ 247880966 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (2 : ZMod 495761933) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 495761933) ^ 2 = 4 := by
        calc
          (2 : ZMod 495761933) ^ 2 = (2 : ZMod 495761933) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 1 * (2 : ZMod 495761933) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 495761933) ^ 4 = 16 := by
        calc
          (2 : ZMod 495761933) ^ 4 = (2 : ZMod 495761933) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 495761933) ^ n) (by norm_num)
          _ = (2 : ZMod 495761933) ^ 2 * (2 : ZMod 495761933) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      change (2 : ZMod 495761933) ^ 4 ≠ 1
      rw [factor_1_2]
      decide

#print axioms prime_lucas_495761933

end TotientTailPeriodKiller
end Erdos249257
