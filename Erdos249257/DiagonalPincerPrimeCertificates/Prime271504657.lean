import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_271504657 : Nat.Prime 271504657 := by
  apply lucas_primality 271504657 (5 : ZMod 271504657)
  ·
      have fermat_0 : (5 : ZMod 271504657) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 271504657) ^ 2 = 25 := by
        calc
          (5 : ZMod 271504657) ^ 2 = (5 : ZMod 271504657) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1 * (5 : ZMod 271504657) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 271504657) ^ 4 = 625 := by
        calc
          (5 : ZMod 271504657) ^ 4 = (5 : ZMod 271504657) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2 * (5 : ZMod 271504657) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 271504657) ^ 8 = 390625 := by
        calc
          (5 : ZMod 271504657) ^ 8 = (5 : ZMod 271504657) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 4 * (5 : ZMod 271504657) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 271504657) ^ 16 = 2273391 := by
        calc
          (5 : ZMod 271504657) ^ 16 = (5 : ZMod 271504657) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 8 * (5 : ZMod 271504657) ^ 8 := by rw [pow_add]
          _ = 2273391 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 271504657) ^ 32 = 215492886 := by
        calc
          (5 : ZMod 271504657) ^ 32 = (5 : ZMod 271504657) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 16 * (5 : ZMod 271504657) ^ 16 := by rw [pow_add]
          _ = 215492886 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 271504657) ^ 64 = 184515027 := by
        calc
          (5 : ZMod 271504657) ^ 64 = (5 : ZMod 271504657) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 32 * (5 : ZMod 271504657) ^ 32 := by rw [pow_add]
          _ = 184515027 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 271504657) ^ 129 = 264784078 := by
        calc
          (5 : ZMod 271504657) ^ 129 = (5 : ZMod 271504657) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 64 * (5 : ZMod 271504657) ^ 64) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 264784078 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 271504657) ^ 258 = 24880006 := by
        calc
          (5 : ZMod 271504657) ^ 258 = (5 : ZMod 271504657) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 129 * (5 : ZMod 271504657) ^ 129 := by rw [pow_add]
          _ = 24880006 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 271504657) ^ 517 = 225369338 := by
        calc
          (5 : ZMod 271504657) ^ 517 = (5 : ZMod 271504657) ^ (258 + 258 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 258 * (5 : ZMod 271504657) ^ 258) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 225369338 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 271504657) ^ 1035 = 22309866 := by
        calc
          (5 : ZMod 271504657) ^ 1035 = (5 : ZMod 271504657) ^ (517 + 517 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 517 * (5 : ZMod 271504657) ^ 517) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 22309866 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 271504657) ^ 2071 = 93461829 := by
        calc
          (5 : ZMod 271504657) ^ 2071 = (5 : ZMod 271504657) ^ (1035 + 1035 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 1035 * (5 : ZMod 271504657) ^ 1035) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 93461829 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 271504657) ^ 4142 = 123466695 := by
        calc
          (5 : ZMod 271504657) ^ 4142 = (5 : ZMod 271504657) ^ (2071 + 2071) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2071 * (5 : ZMod 271504657) ^ 2071 := by rw [pow_add]
          _ = 123466695 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 271504657) ^ 8285 = 37345252 := by
        calc
          (5 : ZMod 271504657) ^ 8285 = (5 : ZMod 271504657) ^ (4142 + 4142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 4142 * (5 : ZMod 271504657) ^ 4142) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 37345252 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 271504657) ^ 16571 = 49096670 := by
        calc
          (5 : ZMod 271504657) ^ 16571 = (5 : ZMod 271504657) ^ (8285 + 8285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 8285 * (5 : ZMod 271504657) ^ 8285) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 49096670 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 271504657) ^ 33142 = 42134534 := by
        calc
          (5 : ZMod 271504657) ^ 33142 = (5 : ZMod 271504657) ^ (16571 + 16571) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 16571 * (5 : ZMod 271504657) ^ 16571 := by rw [pow_add]
          _ = 42134534 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 271504657) ^ 66285 = 72159877 := by
        calc
          (5 : ZMod 271504657) ^ 66285 = (5 : ZMod 271504657) ^ (33142 + 33142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 33142 * (5 : ZMod 271504657) ^ 33142) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 72159877 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 271504657) ^ 132570 = 128455141 := by
        calc
          (5 : ZMod 271504657) ^ 132570 = (5 : ZMod 271504657) ^ (66285 + 66285) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 66285 * (5 : ZMod 271504657) ^ 66285 := by rw [pow_add]
          _ = 128455141 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 271504657) ^ 265141 = 133399335 := by
        calc
          (5 : ZMod 271504657) ^ 265141 = (5 : ZMod 271504657) ^ (132570 + 132570 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 132570 * (5 : ZMod 271504657) ^ 132570) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 133399335 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 271504657) ^ 530282 = 259073991 := by
        calc
          (5 : ZMod 271504657) ^ 530282 = (5 : ZMod 271504657) ^ (265141 + 265141) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 265141 * (5 : ZMod 271504657) ^ 265141 := by rw [pow_add]
          _ = 259073991 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 271504657) ^ 1060565 = 58825730 := by
        calc
          (5 : ZMod 271504657) ^ 1060565 = (5 : ZMod 271504657) ^ (530282 + 530282 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 530282 * (5 : ZMod 271504657) ^ 530282) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 58825730 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 271504657) ^ 2121130 = 103174202 := by
        calc
          (5 : ZMod 271504657) ^ 2121130 = (5 : ZMod 271504657) ^ (1060565 + 1060565) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1060565 * (5 : ZMod 271504657) ^ 1060565 := by rw [pow_add]
          _ = 103174202 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 271504657) ^ 4242260 = 19274307 := by
        calc
          (5 : ZMod 271504657) ^ 4242260 = (5 : ZMod 271504657) ^ (2121130 + 2121130) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2121130 * (5 : ZMod 271504657) ^ 2121130 := by rw [pow_add]
          _ = 19274307 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 271504657) ^ 8484520 = 174175777 := by
        calc
          (5 : ZMod 271504657) ^ 8484520 = (5 : ZMod 271504657) ^ (4242260 + 4242260) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 4242260 * (5 : ZMod 271504657) ^ 4242260 := by rw [pow_add]
          _ = 174175777 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 271504657) ^ 16969041 = 94898184 := by
        calc
          (5 : ZMod 271504657) ^ 16969041 = (5 : ZMod 271504657) ^ (8484520 + 8484520 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 8484520 * (5 : ZMod 271504657) ^ 8484520) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 94898184 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 271504657) ^ 33938082 = 22780723 := by
        calc
          (5 : ZMod 271504657) ^ 33938082 = (5 : ZMod 271504657) ^ (16969041 + 16969041) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 16969041 * (5 : ZMod 271504657) ^ 16969041 := by rw [pow_add]
          _ = 22780723 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 271504657) ^ 67876164 = 8387190 := by
        calc
          (5 : ZMod 271504657) ^ 67876164 = (5 : ZMod 271504657) ^ (33938082 + 33938082) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 33938082 * (5 : ZMod 271504657) ^ 33938082 := by rw [pow_add]
          _ = 8387190 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 271504657) ^ 135752328 = 271504656 := by
        calc
          (5 : ZMod 271504657) ^ 135752328 = (5 : ZMod 271504657) ^ (67876164 + 67876164) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 67876164 * (5 : ZMod 271504657) ^ 67876164 := by rw [pow_add]
          _ = 271504656 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 271504657) ^ 271504656 = 1 := by
        calc
          (5 : ZMod 271504657) ^ 271504656 = (5 : ZMod 271504657) ^ (135752328 + 135752328) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 135752328 * (5 : ZMod 271504657) ^ 135752328 := by rw [pow_add]
          _ = 1 := by rw [fermat_27]; decide
      simpa using fermat_28
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (61, 1), (10303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (61, 1), (10303, 1)] : List FactorBlock).map factorBlockValue).prod = 271504657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 271504657) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 271504657) ^ 2 = 25 := by
        calc
          (5 : ZMod 271504657) ^ 2 = (5 : ZMod 271504657) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1 * (5 : ZMod 271504657) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 271504657) ^ 4 = 625 := by
        calc
          (5 : ZMod 271504657) ^ 4 = (5 : ZMod 271504657) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2 * (5 : ZMod 271504657) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 271504657) ^ 8 = 390625 := by
        calc
          (5 : ZMod 271504657) ^ 8 = (5 : ZMod 271504657) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 4 * (5 : ZMod 271504657) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 271504657) ^ 16 = 2273391 := by
        calc
          (5 : ZMod 271504657) ^ 16 = (5 : ZMod 271504657) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 8 * (5 : ZMod 271504657) ^ 8 := by rw [pow_add]
          _ = 2273391 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 271504657) ^ 32 = 215492886 := by
        calc
          (5 : ZMod 271504657) ^ 32 = (5 : ZMod 271504657) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 16 * (5 : ZMod 271504657) ^ 16 := by rw [pow_add]
          _ = 215492886 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 271504657) ^ 64 = 184515027 := by
        calc
          (5 : ZMod 271504657) ^ 64 = (5 : ZMod 271504657) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 32 * (5 : ZMod 271504657) ^ 32 := by rw [pow_add]
          _ = 184515027 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 271504657) ^ 129 = 264784078 := by
        calc
          (5 : ZMod 271504657) ^ 129 = (5 : ZMod 271504657) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 64 * (5 : ZMod 271504657) ^ 64) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 264784078 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 271504657) ^ 258 = 24880006 := by
        calc
          (5 : ZMod 271504657) ^ 258 = (5 : ZMod 271504657) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 129 * (5 : ZMod 271504657) ^ 129 := by rw [pow_add]
          _ = 24880006 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 271504657) ^ 517 = 225369338 := by
        calc
          (5 : ZMod 271504657) ^ 517 = (5 : ZMod 271504657) ^ (258 + 258 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 258 * (5 : ZMod 271504657) ^ 258) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 225369338 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 271504657) ^ 1035 = 22309866 := by
        calc
          (5 : ZMod 271504657) ^ 1035 = (5 : ZMod 271504657) ^ (517 + 517 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 517 * (5 : ZMod 271504657) ^ 517) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 22309866 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 271504657) ^ 2071 = 93461829 := by
        calc
          (5 : ZMod 271504657) ^ 2071 = (5 : ZMod 271504657) ^ (1035 + 1035 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 1035 * (5 : ZMod 271504657) ^ 1035) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 93461829 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 271504657) ^ 4142 = 123466695 := by
        calc
          (5 : ZMod 271504657) ^ 4142 = (5 : ZMod 271504657) ^ (2071 + 2071) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2071 * (5 : ZMod 271504657) ^ 2071 := by rw [pow_add]
          _ = 123466695 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 271504657) ^ 8285 = 37345252 := by
        calc
          (5 : ZMod 271504657) ^ 8285 = (5 : ZMod 271504657) ^ (4142 + 4142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 4142 * (5 : ZMod 271504657) ^ 4142) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 37345252 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 271504657) ^ 16571 = 49096670 := by
        calc
          (5 : ZMod 271504657) ^ 16571 = (5 : ZMod 271504657) ^ (8285 + 8285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 8285 * (5 : ZMod 271504657) ^ 8285) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 49096670 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 271504657) ^ 33142 = 42134534 := by
        calc
          (5 : ZMod 271504657) ^ 33142 = (5 : ZMod 271504657) ^ (16571 + 16571) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 16571 * (5 : ZMod 271504657) ^ 16571 := by rw [pow_add]
          _ = 42134534 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 271504657) ^ 66285 = 72159877 := by
        calc
          (5 : ZMod 271504657) ^ 66285 = (5 : ZMod 271504657) ^ (33142 + 33142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 33142 * (5 : ZMod 271504657) ^ 33142) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 72159877 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 271504657) ^ 132570 = 128455141 := by
        calc
          (5 : ZMod 271504657) ^ 132570 = (5 : ZMod 271504657) ^ (66285 + 66285) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 66285 * (5 : ZMod 271504657) ^ 66285 := by rw [pow_add]
          _ = 128455141 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 271504657) ^ 265141 = 133399335 := by
        calc
          (5 : ZMod 271504657) ^ 265141 = (5 : ZMod 271504657) ^ (132570 + 132570 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 132570 * (5 : ZMod 271504657) ^ 132570) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 133399335 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 271504657) ^ 530282 = 259073991 := by
        calc
          (5 : ZMod 271504657) ^ 530282 = (5 : ZMod 271504657) ^ (265141 + 265141) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 265141 * (5 : ZMod 271504657) ^ 265141 := by rw [pow_add]
          _ = 259073991 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 271504657) ^ 1060565 = 58825730 := by
        calc
          (5 : ZMod 271504657) ^ 1060565 = (5 : ZMod 271504657) ^ (530282 + 530282 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 530282 * (5 : ZMod 271504657) ^ 530282) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 58825730 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 271504657) ^ 2121130 = 103174202 := by
        calc
          (5 : ZMod 271504657) ^ 2121130 = (5 : ZMod 271504657) ^ (1060565 + 1060565) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1060565 * (5 : ZMod 271504657) ^ 1060565 := by rw [pow_add]
          _ = 103174202 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 271504657) ^ 4242260 = 19274307 := by
        calc
          (5 : ZMod 271504657) ^ 4242260 = (5 : ZMod 271504657) ^ (2121130 + 2121130) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2121130 * (5 : ZMod 271504657) ^ 2121130 := by rw [pow_add]
          _ = 19274307 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 271504657) ^ 8484520 = 174175777 := by
        calc
          (5 : ZMod 271504657) ^ 8484520 = (5 : ZMod 271504657) ^ (4242260 + 4242260) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 4242260 * (5 : ZMod 271504657) ^ 4242260 := by rw [pow_add]
          _ = 174175777 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 271504657) ^ 16969041 = 94898184 := by
        calc
          (5 : ZMod 271504657) ^ 16969041 = (5 : ZMod 271504657) ^ (8484520 + 8484520 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 8484520 * (5 : ZMod 271504657) ^ 8484520) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 94898184 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 271504657) ^ 33938082 = 22780723 := by
        calc
          (5 : ZMod 271504657) ^ 33938082 = (5 : ZMod 271504657) ^ (16969041 + 16969041) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 16969041 * (5 : ZMod 271504657) ^ 16969041 := by rw [pow_add]
          _ = 22780723 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 271504657) ^ 67876164 = 8387190 := by
        calc
          (5 : ZMod 271504657) ^ 67876164 = (5 : ZMod 271504657) ^ (33938082 + 33938082) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 33938082 * (5 : ZMod 271504657) ^ 33938082 := by rw [pow_add]
          _ = 8387190 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 271504657) ^ 135752328 = 271504656 := by
        calc
          (5 : ZMod 271504657) ^ 135752328 = (5 : ZMod 271504657) ^ (67876164 + 67876164) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 67876164 * (5 : ZMod 271504657) ^ 67876164 := by rw [pow_add]
          _ = 271504656 := by rw [factor_0_26]; decide
      change (5 : ZMod 271504657) ^ 135752328 ≠ 1
      rw [factor_0_27]
      decide
    ·
      have factor_1_0 : (5 : ZMod 271504657) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 271504657) ^ 2 = 25 := by
        calc
          (5 : ZMod 271504657) ^ 2 = (5 : ZMod 271504657) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1 * (5 : ZMod 271504657) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 271504657) ^ 5 = 3125 := by
        calc
          (5 : ZMod 271504657) ^ 5 = (5 : ZMod 271504657) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 2 * (5 : ZMod 271504657) ^ 2) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 271504657) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 271504657) ^ 10 = (5 : ZMod 271504657) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 5 * (5 : ZMod 271504657) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 271504657) ^ 21 = 45225793 := by
        calc
          (5 : ZMod 271504657) ^ 21 = (5 : ZMod 271504657) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 10 * (5 : ZMod 271504657) ^ 10) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 45225793 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 271504657) ^ 43 = 6031324 := by
        calc
          (5 : ZMod 271504657) ^ 43 = (5 : ZMod 271504657) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 21 * (5 : ZMod 271504657) ^ 21) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 6031324 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 271504657) ^ 86 = 132238802 := by
        calc
          (5 : ZMod 271504657) ^ 86 = (5 : ZMod 271504657) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 43 * (5 : ZMod 271504657) ^ 43 := by rw [pow_add]
          _ = 132238802 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 271504657) ^ 172 = 26845562 := by
        calc
          (5 : ZMod 271504657) ^ 172 = (5 : ZMod 271504657) ^ (86 + 86) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 86 * (5 : ZMod 271504657) ^ 86 := by rw [pow_add]
          _ = 26845562 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 271504657) ^ 345 = 56084283 := by
        calc
          (5 : ZMod 271504657) ^ 345 = (5 : ZMod 271504657) ^ (172 + 172 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 172 * (5 : ZMod 271504657) ^ 172) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 56084283 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 271504657) ^ 690 = 187161409 := by
        calc
          (5 : ZMod 271504657) ^ 690 = (5 : ZMod 271504657) ^ (345 + 345) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 345 * (5 : ZMod 271504657) ^ 345 := by rw [pow_add]
          _ = 187161409 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 271504657) ^ 1380 = 97091037 := by
        calc
          (5 : ZMod 271504657) ^ 1380 = (5 : ZMod 271504657) ^ (690 + 690) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 690 * (5 : ZMod 271504657) ^ 690 := by rw [pow_add]
          _ = 97091037 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 271504657) ^ 2761 = 134597118 := by
        calc
          (5 : ZMod 271504657) ^ 2761 = (5 : ZMod 271504657) ^ (1380 + 1380 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 1380 * (5 : ZMod 271504657) ^ 1380) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 134597118 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 271504657) ^ 5523 = 261674612 := by
        calc
          (5 : ZMod 271504657) ^ 5523 = (5 : ZMod 271504657) ^ (2761 + 2761 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 2761 * (5 : ZMod 271504657) ^ 2761) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 261674612 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 271504657) ^ 11047 = 141771514 := by
        calc
          (5 : ZMod 271504657) ^ 11047 = (5 : ZMod 271504657) ^ (5523 + 5523 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 5523 * (5 : ZMod 271504657) ^ 5523) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 141771514 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 271504657) ^ 22095 = 108306661 := by
        calc
          (5 : ZMod 271504657) ^ 22095 = (5 : ZMod 271504657) ^ (11047 + 11047 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 11047 * (5 : ZMod 271504657) ^ 11047) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 108306661 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 271504657) ^ 44190 = 175730993 := by
        calc
          (5 : ZMod 271504657) ^ 44190 = (5 : ZMod 271504657) ^ (22095 + 22095) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 22095 * (5 : ZMod 271504657) ^ 22095 := by rw [pow_add]
          _ = 175730993 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 271504657) ^ 88380 = 204004453 := by
        calc
          (5 : ZMod 271504657) ^ 88380 = (5 : ZMod 271504657) ^ (44190 + 44190) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 44190 * (5 : ZMod 271504657) ^ 44190 := by rw [pow_add]
          _ = 204004453 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 271504657) ^ 176760 = 146718899 := by
        calc
          (5 : ZMod 271504657) ^ 176760 = (5 : ZMod 271504657) ^ (88380 + 88380) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 88380 * (5 : ZMod 271504657) ^ 88380 := by rw [pow_add]
          _ = 146718899 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 271504657) ^ 353521 = 31962244 := by
        calc
          (5 : ZMod 271504657) ^ 353521 = (5 : ZMod 271504657) ^ (176760 + 176760 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 176760 * (5 : ZMod 271504657) ^ 176760) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 31962244 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 271504657) ^ 707043 = 36583194 := by
        calc
          (5 : ZMod 271504657) ^ 707043 = (5 : ZMod 271504657) ^ (353521 + 353521 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 353521 * (5 : ZMod 271504657) ^ 353521) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 36583194 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 271504657) ^ 1414086 = 5454280 := by
        calc
          (5 : ZMod 271504657) ^ 1414086 = (5 : ZMod 271504657) ^ (707043 + 707043) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 707043 * (5 : ZMod 271504657) ^ 707043 := by rw [pow_add]
          _ = 5454280 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 271504657) ^ 2828173 = 124721951 := by
        calc
          (5 : ZMod 271504657) ^ 2828173 = (5 : ZMod 271504657) ^ (1414086 + 1414086 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 1414086 * (5 : ZMod 271504657) ^ 1414086) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 124721951 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 271504657) ^ 5656347 = 247397945 := by
        calc
          (5 : ZMod 271504657) ^ 5656347 = (5 : ZMod 271504657) ^ (2828173 + 2828173 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 2828173 * (5 : ZMod 271504657) ^ 2828173) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 247397945 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 271504657) ^ 11312694 = 108524318 := by
        calc
          (5 : ZMod 271504657) ^ 11312694 = (5 : ZMod 271504657) ^ (5656347 + 5656347) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 5656347 * (5 : ZMod 271504657) ^ 5656347 := by rw [pow_add]
          _ = 108524318 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 271504657) ^ 22625388 = 116114857 := by
        calc
          (5 : ZMod 271504657) ^ 22625388 = (5 : ZMod 271504657) ^ (11312694 + 11312694) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 11312694 * (5 : ZMod 271504657) ^ 11312694 := by rw [pow_add]
          _ = 116114857 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 271504657) ^ 45250776 = 208495140 := by
        calc
          (5 : ZMod 271504657) ^ 45250776 = (5 : ZMod 271504657) ^ (22625388 + 22625388) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 22625388 * (5 : ZMod 271504657) ^ 22625388 := by rw [pow_add]
          _ = 208495140 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 271504657) ^ 90501552 = 208495139 := by
        calc
          (5 : ZMod 271504657) ^ 90501552 = (5 : ZMod 271504657) ^ (45250776 + 45250776) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 45250776 * (5 : ZMod 271504657) ^ 45250776 := by rw [pow_add]
          _ = 208495139 := by rw [factor_1_25]; decide
      change (5 : ZMod 271504657) ^ 90501552 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (5 : ZMod 271504657) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 271504657) ^ 2 = 25 := by
        calc
          (5 : ZMod 271504657) ^ 2 = (5 : ZMod 271504657) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1 * (5 : ZMod 271504657) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 271504657) ^ 4 = 625 := by
        calc
          (5 : ZMod 271504657) ^ 4 = (5 : ZMod 271504657) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2 * (5 : ZMod 271504657) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 271504657) ^ 8 = 390625 := by
        calc
          (5 : ZMod 271504657) ^ 8 = (5 : ZMod 271504657) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 4 * (5 : ZMod 271504657) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 271504657) ^ 16 = 2273391 := by
        calc
          (5 : ZMod 271504657) ^ 16 = (5 : ZMod 271504657) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 8 * (5 : ZMod 271504657) ^ 8 := by rw [pow_add]
          _ = 2273391 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 271504657) ^ 33 = 262950459 := by
        calc
          (5 : ZMod 271504657) ^ 33 = (5 : ZMod 271504657) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 16 * (5 : ZMod 271504657) ^ 16) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 262950459 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 271504657) ^ 67 = 257987187 := by
        calc
          (5 : ZMod 271504657) ^ 67 = (5 : ZMod 271504657) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 33 * (5 : ZMod 271504657) ^ 33) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 257987187 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 271504657) ^ 135 = 63255384 := by
        calc
          (5 : ZMod 271504657) ^ 135 = (5 : ZMod 271504657) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 67 * (5 : ZMod 271504657) ^ 67) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 63255384 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 271504657) ^ 271 = 162579089 := by
        calc
          (5 : ZMod 271504657) ^ 271 = (5 : ZMod 271504657) ^ (135 + 135 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 135 * (5 : ZMod 271504657) ^ 135) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 162579089 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 271504657) ^ 543 = 29896388 := by
        calc
          (5 : ZMod 271504657) ^ 543 = (5 : ZMod 271504657) ^ (271 + 271 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 271 * (5 : ZMod 271504657) ^ 271) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 29896388 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 271504657) ^ 1086 = 141593230 := by
        calc
          (5 : ZMod 271504657) ^ 1086 = (5 : ZMod 271504657) ^ (543 + 543) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 543 * (5 : ZMod 271504657) ^ 543 := by rw [pow_add]
          _ = 141593230 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 271504657) ^ 2173 = 180896701 := by
        calc
          (5 : ZMod 271504657) ^ 2173 = (5 : ZMod 271504657) ^ (1086 + 1086 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 1086 * (5 : ZMod 271504657) ^ 1086) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 180896701 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 271504657) ^ 4346 = 159882159 := by
        calc
          (5 : ZMod 271504657) ^ 4346 = (5 : ZMod 271504657) ^ (2173 + 2173) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2173 * (5 : ZMod 271504657) ^ 2173 := by rw [pow_add]
          _ = 159882159 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 271504657) ^ 8693 = 94638891 := by
        calc
          (5 : ZMod 271504657) ^ 8693 = (5 : ZMod 271504657) ^ (4346 + 4346 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 4346 * (5 : ZMod 271504657) ^ 4346) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 94638891 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 271504657) ^ 17386 = 258470289 := by
        calc
          (5 : ZMod 271504657) ^ 17386 = (5 : ZMod 271504657) ^ (8693 + 8693) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 8693 * (5 : ZMod 271504657) ^ 8693 := by rw [pow_add]
          _ = 258470289 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 271504657) ^ 34772 = 167032360 := by
        calc
          (5 : ZMod 271504657) ^ 34772 = (5 : ZMod 271504657) ^ (17386 + 17386) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 17386 * (5 : ZMod 271504657) ^ 17386 := by rw [pow_add]
          _ = 167032360 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 271504657) ^ 69545 = 96544347 := by
        calc
          (5 : ZMod 271504657) ^ 69545 = (5 : ZMod 271504657) ^ (34772 + 34772 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 34772 * (5 : ZMod 271504657) ^ 34772) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 96544347 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 271504657) ^ 139090 = 132887067 := by
        calc
          (5 : ZMod 271504657) ^ 139090 = (5 : ZMod 271504657) ^ (69545 + 69545) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 69545 * (5 : ZMod 271504657) ^ 69545 := by rw [pow_add]
          _ = 132887067 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 271504657) ^ 278181 = 31853574 := by
        calc
          (5 : ZMod 271504657) ^ 278181 = (5 : ZMod 271504657) ^ (139090 + 139090 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 139090 * (5 : ZMod 271504657) ^ 139090) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 31853574 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 271504657) ^ 556362 = 77226467 := by
        calc
          (5 : ZMod 271504657) ^ 556362 = (5 : ZMod 271504657) ^ (278181 + 278181) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 278181 * (5 : ZMod 271504657) ^ 278181 := by rw [pow_add]
          _ = 77226467 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 271504657) ^ 1112724 = 251185404 := by
        calc
          (5 : ZMod 271504657) ^ 1112724 = (5 : ZMod 271504657) ^ (556362 + 556362) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 556362 * (5 : ZMod 271504657) ^ 556362 := by rw [pow_add]
          _ = 251185404 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 271504657) ^ 2225448 = 69166592 := by
        calc
          (5 : ZMod 271504657) ^ 2225448 = (5 : ZMod 271504657) ^ (1112724 + 1112724) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1112724 * (5 : ZMod 271504657) ^ 1112724 := by rw [pow_add]
          _ = 69166592 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 271504657) ^ 4450896 = 48747548 := by
        calc
          (5 : ZMod 271504657) ^ 4450896 = (5 : ZMod 271504657) ^ (2225448 + 2225448) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 2225448 * (5 : ZMod 271504657) ^ 2225448 := by rw [pow_add]
          _ = 48747548 := by rw [factor_2_21]; decide
      change (5 : ZMod 271504657) ^ 4450896 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (5 : ZMod 271504657) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 271504657) ^ 3 = 125 := by
        calc
          (5 : ZMod 271504657) ^ 3 = (5 : ZMod 271504657) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 1 * (5 : ZMod 271504657) ^ 1) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 271504657) ^ 6 = 15625 := by
        calc
          (5 : ZMod 271504657) ^ 6 = (5 : ZMod 271504657) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 3 * (5 : ZMod 271504657) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 271504657) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 271504657) ^ 12 = (5 : ZMod 271504657) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 6 * (5 : ZMod 271504657) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 271504657) ^ 25 = 29636297 := by
        calc
          (5 : ZMod 271504657) ^ 25 = (5 : ZMod 271504657) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 12 * (5 : ZMod 271504657) ^ 12) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 29636297 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 271504657) ^ 51 = 140028711 := by
        calc
          (5 : ZMod 271504657) ^ 51 = (5 : ZMod 271504657) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 25 * (5 : ZMod 271504657) ^ 25) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 140028711 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 271504657) ^ 102 = 183237907 := by
        calc
          (5 : ZMod 271504657) ^ 102 = (5 : ZMod 271504657) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 51 * (5 : ZMod 271504657) ^ 51 := by rw [pow_add]
          _ = 183237907 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 271504657) ^ 205 = 187186522 := by
        calc
          (5 : ZMod 271504657) ^ 205 = (5 : ZMod 271504657) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 102 * (5 : ZMod 271504657) ^ 102) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 187186522 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 271504657) ^ 411 = 153649447 := by
        calc
          (5 : ZMod 271504657) ^ 411 = (5 : ZMod 271504657) ^ (205 + 205 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 205 * (5 : ZMod 271504657) ^ 205) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 153649447 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 271504657) ^ 823 = 162230152 := by
        calc
          (5 : ZMod 271504657) ^ 823 = (5 : ZMod 271504657) ^ (411 + 411 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 411 * (5 : ZMod 271504657) ^ 411) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 162230152 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 271504657) ^ 1647 = 169445843 := by
        calc
          (5 : ZMod 271504657) ^ 1647 = (5 : ZMod 271504657) ^ (823 + 823 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = ((5 : ZMod 271504657) ^ 823 * (5 : ZMod 271504657) ^ 823) * (5 : ZMod 271504657) := by rw [pow_succ, pow_add]
          _ = 169445843 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 271504657) ^ 3294 = 111994480 := by
        calc
          (5 : ZMod 271504657) ^ 3294 = (5 : ZMod 271504657) ^ (1647 + 1647) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 1647 * (5 : ZMod 271504657) ^ 1647 := by rw [pow_add]
          _ = 111994480 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 271504657) ^ 6588 = 193465633 := by
        calc
          (5 : ZMod 271504657) ^ 6588 = (5 : ZMod 271504657) ^ (3294 + 3294) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 3294 * (5 : ZMod 271504657) ^ 3294 := by rw [pow_add]
          _ = 193465633 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 271504657) ^ 13176 = 71750445 := by
        calc
          (5 : ZMod 271504657) ^ 13176 = (5 : ZMod 271504657) ^ (6588 + 6588) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 6588 * (5 : ZMod 271504657) ^ 6588 := by rw [pow_add]
          _ = 71750445 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 271504657) ^ 26352 = 35150863 := by
        calc
          (5 : ZMod 271504657) ^ 26352 = (5 : ZMod 271504657) ^ (13176 + 13176) :=
            congrArg (fun n : ℕ => (5 : ZMod 271504657) ^ n) (by norm_num)
          _ = (5 : ZMod 271504657) ^ 13176 * (5 : ZMod 271504657) ^ 13176 := by rw [pow_add]
          _ = 35150863 := by rw [factor_3_13]; decide
      change (5 : ZMod 271504657) ^ 26352 ≠ 1
      rw [factor_3_14]
      decide

#print axioms prime_lucas_271504657

end TotientTailPeriodKiller
end Erdos249257
