import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_69787961743 : Nat.Prime 69787961743 := by
  apply lucas_primality 69787961743 (3 : ZMod 69787961743)
  ·
      have fermat_0 : (3 : ZMod 69787961743) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 69787961743) ^ 2 = 9 := by
        calc
          (3 : ZMod 69787961743) ^ 2 = (3 : ZMod 69787961743) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1 * (3 : ZMod 69787961743) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 69787961743) ^ 4 = 81 := by
        calc
          (3 : ZMod 69787961743) ^ 4 = (3 : ZMod 69787961743) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2 * (3 : ZMod 69787961743) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 69787961743) ^ 8 = 6561 := by
        calc
          (3 : ZMod 69787961743) ^ 8 = (3 : ZMod 69787961743) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 4 * (3 : ZMod 69787961743) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 69787961743) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 69787961743) ^ 16 = (3 : ZMod 69787961743) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 8 * (3 : ZMod 69787961743) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 69787961743) ^ 32 = 10228651705 := by
        calc
          (3 : ZMod 69787961743) ^ 32 = (3 : ZMod 69787961743) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 16 * (3 : ZMod 69787961743) ^ 16 := by rw [pow_add]
          _ = 10228651705 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 69787961743) ^ 64 = 16889141627 := by
        calc
          (3 : ZMod 69787961743) ^ 64 = (3 : ZMod 69787961743) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 32 * (3 : ZMod 69787961743) ^ 32 := by rw [pow_add]
          _ = 16889141627 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 69787961743) ^ 129 = 52188207919 := by
        calc
          (3 : ZMod 69787961743) ^ 129 = (3 : ZMod 69787961743) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 64 * (3 : ZMod 69787961743) ^ 64) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 52188207919 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 69787961743) ^ 259 = 14204799058 := by
        calc
          (3 : ZMod 69787961743) ^ 259 = (3 : ZMod 69787961743) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 129 * (3 : ZMod 69787961743) ^ 129) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 14204799058 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 69787961743) ^ 519 = 38209238111 := by
        calc
          (3 : ZMod 69787961743) ^ 519 = (3 : ZMod 69787961743) ^ (259 + 259 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 259 * (3 : ZMod 69787961743) ^ 259) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 38209238111 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 69787961743) ^ 1039 = 42861488752 := by
        calc
          (3 : ZMod 69787961743) ^ 1039 = (3 : ZMod 69787961743) ^ (519 + 519 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 519 * (3 : ZMod 69787961743) ^ 519) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 42861488752 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 69787961743) ^ 2079 = 17941760319 := by
        calc
          (3 : ZMod 69787961743) ^ 2079 = (3 : ZMod 69787961743) ^ (1039 + 1039 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1039 * (3 : ZMod 69787961743) ^ 1039) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 17941760319 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 69787961743) ^ 4159 = 58110406392 := by
        calc
          (3 : ZMod 69787961743) ^ 4159 = (3 : ZMod 69787961743) ^ (2079 + 2079 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 2079 * (3 : ZMod 69787961743) ^ 2079) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 58110406392 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 69787961743) ^ 8319 = 11586102526 := by
        calc
          (3 : ZMod 69787961743) ^ 8319 = (3 : ZMod 69787961743) ^ (4159 + 4159 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 4159 * (3 : ZMod 69787961743) ^ 4159) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 11586102526 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 69787961743) ^ 16638 = 6334972849 := by
        calc
          (3 : ZMod 69787961743) ^ 16638 = (3 : ZMod 69787961743) ^ (8319 + 8319) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 8319 * (3 : ZMod 69787961743) ^ 8319 := by rw [pow_add]
          _ = 6334972849 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 69787961743) ^ 33277 = 50040784763 := by
        calc
          (3 : ZMod 69787961743) ^ 33277 = (3 : ZMod 69787961743) ^ (16638 + 16638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 16638 * (3 : ZMod 69787961743) ^ 16638) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 50040784763 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 69787961743) ^ 66554 = 20121261912 := by
        calc
          (3 : ZMod 69787961743) ^ 66554 = (3 : ZMod 69787961743) ^ (33277 + 33277) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 33277 * (3 : ZMod 69787961743) ^ 33277 := by rw [pow_add]
          _ = 20121261912 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 69787961743) ^ 133109 = 12984214672 := by
        calc
          (3 : ZMod 69787961743) ^ 133109 = (3 : ZMod 69787961743) ^ (66554 + 66554 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 66554 * (3 : ZMod 69787961743) ^ 66554) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 12984214672 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 69787961743) ^ 266219 = 31951226470 := by
        calc
          (3 : ZMod 69787961743) ^ 266219 = (3 : ZMod 69787961743) ^ (133109 + 133109 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 133109 * (3 : ZMod 69787961743) ^ 133109) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 31951226470 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 69787961743) ^ 532439 = 53333470334 := by
        calc
          (3 : ZMod 69787961743) ^ 532439 = (3 : ZMod 69787961743) ^ (266219 + 266219 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 266219 * (3 : ZMod 69787961743) ^ 266219) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 53333470334 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 69787961743) ^ 1064879 = 67038427762 := by
        calc
          (3 : ZMod 69787961743) ^ 1064879 = (3 : ZMod 69787961743) ^ (532439 + 532439 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 532439 * (3 : ZMod 69787961743) ^ 532439) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 67038427762 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 69787961743) ^ 2129759 = 53790481067 := by
        calc
          (3 : ZMod 69787961743) ^ 2129759 = (3 : ZMod 69787961743) ^ (1064879 + 1064879 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1064879 * (3 : ZMod 69787961743) ^ 1064879) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 53790481067 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 69787961743) ^ 4259519 = 59425798671 := by
        calc
          (3 : ZMod 69787961743) ^ 4259519 = (3 : ZMod 69787961743) ^ (2129759 + 2129759 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 2129759 * (3 : ZMod 69787961743) ^ 2129759) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 59425798671 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 69787961743) ^ 8519038 = 8557165087 := by
        calc
          (3 : ZMod 69787961743) ^ 8519038 = (3 : ZMod 69787961743) ^ (4259519 + 4259519) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 4259519 * (3 : ZMod 69787961743) ^ 4259519 := by rw [pow_add]
          _ = 8557165087 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 69787961743) ^ 17038076 = 55687343627 := by
        calc
          (3 : ZMod 69787961743) ^ 17038076 = (3 : ZMod 69787961743) ^ (8519038 + 8519038) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 8519038 * (3 : ZMod 69787961743) ^ 8519038 := by rw [pow_add]
          _ = 55687343627 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 69787961743) ^ 34076153 = 22234461983 := by
        calc
          (3 : ZMod 69787961743) ^ 34076153 = (3 : ZMod 69787961743) ^ (17038076 + 17038076 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 17038076 * (3 : ZMod 69787961743) ^ 17038076) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 22234461983 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 69787961743) ^ 68152306 = 28294544643 := by
        calc
          (3 : ZMod 69787961743) ^ 68152306 = (3 : ZMod 69787961743) ^ (34076153 + 34076153) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 34076153 * (3 : ZMod 69787961743) ^ 34076153 := by rw [pow_add]
          _ = 28294544643 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 69787961743) ^ 136304612 = 61579174164 := by
        calc
          (3 : ZMod 69787961743) ^ 136304612 = (3 : ZMod 69787961743) ^ (68152306 + 68152306) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 68152306 * (3 : ZMod 69787961743) ^ 68152306 := by rw [pow_add]
          _ = 61579174164 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 69787961743) ^ 272609225 = 1171415729 := by
        calc
          (3 : ZMod 69787961743) ^ 272609225 = (3 : ZMod 69787961743) ^ (136304612 + 136304612 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 136304612 * (3 : ZMod 69787961743) ^ 136304612) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 1171415729 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 69787961743) ^ 545218451 = 29189397282 := by
        calc
          (3 : ZMod 69787961743) ^ 545218451 = (3 : ZMod 69787961743) ^ (272609225 + 272609225 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 272609225 * (3 : ZMod 69787961743) ^ 272609225) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 29189397282 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 69787961743) ^ 1090436902 = 63891555473 := by
        calc
          (3 : ZMod 69787961743) ^ 1090436902 = (3 : ZMod 69787961743) ^ (545218451 + 545218451) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 545218451 * (3 : ZMod 69787961743) ^ 545218451 := by rw [pow_add]
          _ = 63891555473 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 69787961743) ^ 2180873804 = 24582466104 := by
        calc
          (3 : ZMod 69787961743) ^ 2180873804 = (3 : ZMod 69787961743) ^ (1090436902 + 1090436902) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1090436902 * (3 : ZMod 69787961743) ^ 1090436902 := by rw [pow_add]
          _ = 24582466104 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 69787961743) ^ 4361747608 = 9692733085 := by
        calc
          (3 : ZMod 69787961743) ^ 4361747608 = (3 : ZMod 69787961743) ^ (2180873804 + 2180873804) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2180873804 * (3 : ZMod 69787961743) ^ 2180873804 := by rw [pow_add]
          _ = 9692733085 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 69787961743) ^ 8723495217 = 30661128564 := by
        calc
          (3 : ZMod 69787961743) ^ 8723495217 = (3 : ZMod 69787961743) ^ (4361747608 + 4361747608 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 4361747608 * (3 : ZMod 69787961743) ^ 4361747608) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 30661128564 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 69787961743) ^ 17446990435 = 19213148643 := by
        calc
          (3 : ZMod 69787961743) ^ 17446990435 = (3 : ZMod 69787961743) ^ (8723495217 + 8723495217 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 8723495217 * (3 : ZMod 69787961743) ^ 8723495217) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 19213148643 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 69787961743) ^ 34893980871 = 69787961742 := by
        calc
          (3 : ZMod 69787961743) ^ 34893980871 = (3 : ZMod 69787961743) ^ (17446990435 + 17446990435 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 17446990435 * (3 : ZMod 69787961743) ^ 17446990435) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 69787961742 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 69787961743) ^ 69787961742 = 1 := by
        calc
          (3 : ZMod 69787961743) ^ 69787961742 = (3 : ZMod 69787961743) ^ (34893980871 + 34893980871) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 34893980871 * (3 : ZMod 69787961743) ^ 34893980871 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (313, 1), (1955831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (313, 1), (1955831, 1)] : List FactorBlock).map factorBlockValue).prod = 69787961743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 69787961743) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 69787961743) ^ 2 = 9 := by
        calc
          (3 : ZMod 69787961743) ^ 2 = (3 : ZMod 69787961743) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1 * (3 : ZMod 69787961743) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 69787961743) ^ 4 = 81 := by
        calc
          (3 : ZMod 69787961743) ^ 4 = (3 : ZMod 69787961743) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2 * (3 : ZMod 69787961743) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 69787961743) ^ 8 = 6561 := by
        calc
          (3 : ZMod 69787961743) ^ 8 = (3 : ZMod 69787961743) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 4 * (3 : ZMod 69787961743) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 69787961743) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 69787961743) ^ 16 = (3 : ZMod 69787961743) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 8 * (3 : ZMod 69787961743) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 69787961743) ^ 32 = 10228651705 := by
        calc
          (3 : ZMod 69787961743) ^ 32 = (3 : ZMod 69787961743) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 16 * (3 : ZMod 69787961743) ^ 16 := by rw [pow_add]
          _ = 10228651705 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 69787961743) ^ 64 = 16889141627 := by
        calc
          (3 : ZMod 69787961743) ^ 64 = (3 : ZMod 69787961743) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 32 * (3 : ZMod 69787961743) ^ 32 := by rw [pow_add]
          _ = 16889141627 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 69787961743) ^ 129 = 52188207919 := by
        calc
          (3 : ZMod 69787961743) ^ 129 = (3 : ZMod 69787961743) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 64 * (3 : ZMod 69787961743) ^ 64) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 52188207919 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 69787961743) ^ 259 = 14204799058 := by
        calc
          (3 : ZMod 69787961743) ^ 259 = (3 : ZMod 69787961743) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 129 * (3 : ZMod 69787961743) ^ 129) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 14204799058 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 69787961743) ^ 519 = 38209238111 := by
        calc
          (3 : ZMod 69787961743) ^ 519 = (3 : ZMod 69787961743) ^ (259 + 259 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 259 * (3 : ZMod 69787961743) ^ 259) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 38209238111 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 69787961743) ^ 1039 = 42861488752 := by
        calc
          (3 : ZMod 69787961743) ^ 1039 = (3 : ZMod 69787961743) ^ (519 + 519 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 519 * (3 : ZMod 69787961743) ^ 519) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 42861488752 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 69787961743) ^ 2079 = 17941760319 := by
        calc
          (3 : ZMod 69787961743) ^ 2079 = (3 : ZMod 69787961743) ^ (1039 + 1039 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1039 * (3 : ZMod 69787961743) ^ 1039) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 17941760319 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 69787961743) ^ 4159 = 58110406392 := by
        calc
          (3 : ZMod 69787961743) ^ 4159 = (3 : ZMod 69787961743) ^ (2079 + 2079 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 2079 * (3 : ZMod 69787961743) ^ 2079) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 58110406392 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 69787961743) ^ 8319 = 11586102526 := by
        calc
          (3 : ZMod 69787961743) ^ 8319 = (3 : ZMod 69787961743) ^ (4159 + 4159 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 4159 * (3 : ZMod 69787961743) ^ 4159) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 11586102526 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 69787961743) ^ 16638 = 6334972849 := by
        calc
          (3 : ZMod 69787961743) ^ 16638 = (3 : ZMod 69787961743) ^ (8319 + 8319) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 8319 * (3 : ZMod 69787961743) ^ 8319 := by rw [pow_add]
          _ = 6334972849 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 69787961743) ^ 33277 = 50040784763 := by
        calc
          (3 : ZMod 69787961743) ^ 33277 = (3 : ZMod 69787961743) ^ (16638 + 16638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 16638 * (3 : ZMod 69787961743) ^ 16638) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 50040784763 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 69787961743) ^ 66554 = 20121261912 := by
        calc
          (3 : ZMod 69787961743) ^ 66554 = (3 : ZMod 69787961743) ^ (33277 + 33277) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 33277 * (3 : ZMod 69787961743) ^ 33277 := by rw [pow_add]
          _ = 20121261912 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 69787961743) ^ 133109 = 12984214672 := by
        calc
          (3 : ZMod 69787961743) ^ 133109 = (3 : ZMod 69787961743) ^ (66554 + 66554 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 66554 * (3 : ZMod 69787961743) ^ 66554) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 12984214672 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 69787961743) ^ 266219 = 31951226470 := by
        calc
          (3 : ZMod 69787961743) ^ 266219 = (3 : ZMod 69787961743) ^ (133109 + 133109 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 133109 * (3 : ZMod 69787961743) ^ 133109) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 31951226470 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 69787961743) ^ 532439 = 53333470334 := by
        calc
          (3 : ZMod 69787961743) ^ 532439 = (3 : ZMod 69787961743) ^ (266219 + 266219 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 266219 * (3 : ZMod 69787961743) ^ 266219) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 53333470334 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 69787961743) ^ 1064879 = 67038427762 := by
        calc
          (3 : ZMod 69787961743) ^ 1064879 = (3 : ZMod 69787961743) ^ (532439 + 532439 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 532439 * (3 : ZMod 69787961743) ^ 532439) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 67038427762 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 69787961743) ^ 2129759 = 53790481067 := by
        calc
          (3 : ZMod 69787961743) ^ 2129759 = (3 : ZMod 69787961743) ^ (1064879 + 1064879 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1064879 * (3 : ZMod 69787961743) ^ 1064879) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 53790481067 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 69787961743) ^ 4259519 = 59425798671 := by
        calc
          (3 : ZMod 69787961743) ^ 4259519 = (3 : ZMod 69787961743) ^ (2129759 + 2129759 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 2129759 * (3 : ZMod 69787961743) ^ 2129759) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 59425798671 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 69787961743) ^ 8519038 = 8557165087 := by
        calc
          (3 : ZMod 69787961743) ^ 8519038 = (3 : ZMod 69787961743) ^ (4259519 + 4259519) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 4259519 * (3 : ZMod 69787961743) ^ 4259519 := by rw [pow_add]
          _ = 8557165087 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 69787961743) ^ 17038076 = 55687343627 := by
        calc
          (3 : ZMod 69787961743) ^ 17038076 = (3 : ZMod 69787961743) ^ (8519038 + 8519038) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 8519038 * (3 : ZMod 69787961743) ^ 8519038 := by rw [pow_add]
          _ = 55687343627 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 69787961743) ^ 34076153 = 22234461983 := by
        calc
          (3 : ZMod 69787961743) ^ 34076153 = (3 : ZMod 69787961743) ^ (17038076 + 17038076 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 17038076 * (3 : ZMod 69787961743) ^ 17038076) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 22234461983 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 69787961743) ^ 68152306 = 28294544643 := by
        calc
          (3 : ZMod 69787961743) ^ 68152306 = (3 : ZMod 69787961743) ^ (34076153 + 34076153) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 34076153 * (3 : ZMod 69787961743) ^ 34076153 := by rw [pow_add]
          _ = 28294544643 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 69787961743) ^ 136304612 = 61579174164 := by
        calc
          (3 : ZMod 69787961743) ^ 136304612 = (3 : ZMod 69787961743) ^ (68152306 + 68152306) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 68152306 * (3 : ZMod 69787961743) ^ 68152306 := by rw [pow_add]
          _ = 61579174164 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 69787961743) ^ 272609225 = 1171415729 := by
        calc
          (3 : ZMod 69787961743) ^ 272609225 = (3 : ZMod 69787961743) ^ (136304612 + 136304612 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 136304612 * (3 : ZMod 69787961743) ^ 136304612) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 1171415729 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 69787961743) ^ 545218451 = 29189397282 := by
        calc
          (3 : ZMod 69787961743) ^ 545218451 = (3 : ZMod 69787961743) ^ (272609225 + 272609225 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 272609225 * (3 : ZMod 69787961743) ^ 272609225) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 29189397282 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 69787961743) ^ 1090436902 = 63891555473 := by
        calc
          (3 : ZMod 69787961743) ^ 1090436902 = (3 : ZMod 69787961743) ^ (545218451 + 545218451) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 545218451 * (3 : ZMod 69787961743) ^ 545218451 := by rw [pow_add]
          _ = 63891555473 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 69787961743) ^ 2180873804 = 24582466104 := by
        calc
          (3 : ZMod 69787961743) ^ 2180873804 = (3 : ZMod 69787961743) ^ (1090436902 + 1090436902) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1090436902 * (3 : ZMod 69787961743) ^ 1090436902 := by rw [pow_add]
          _ = 24582466104 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 69787961743) ^ 4361747608 = 9692733085 := by
        calc
          (3 : ZMod 69787961743) ^ 4361747608 = (3 : ZMod 69787961743) ^ (2180873804 + 2180873804) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2180873804 * (3 : ZMod 69787961743) ^ 2180873804 := by rw [pow_add]
          _ = 9692733085 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 69787961743) ^ 8723495217 = 30661128564 := by
        calc
          (3 : ZMod 69787961743) ^ 8723495217 = (3 : ZMod 69787961743) ^ (4361747608 + 4361747608 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 4361747608 * (3 : ZMod 69787961743) ^ 4361747608) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 30661128564 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 69787961743) ^ 17446990435 = 19213148643 := by
        calc
          (3 : ZMod 69787961743) ^ 17446990435 = (3 : ZMod 69787961743) ^ (8723495217 + 8723495217 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 8723495217 * (3 : ZMod 69787961743) ^ 8723495217) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 19213148643 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 69787961743) ^ 34893980871 = 69787961742 := by
        calc
          (3 : ZMod 69787961743) ^ 34893980871 = (3 : ZMod 69787961743) ^ (17446990435 + 17446990435 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 17446990435 * (3 : ZMod 69787961743) ^ 17446990435) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 69787961742 := by rw [factor_0_34]; decide
      change (3 : ZMod 69787961743) ^ 34893980871 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (3 : ZMod 69787961743) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 69787961743) ^ 2 = 9 := by
        calc
          (3 : ZMod 69787961743) ^ 2 = (3 : ZMod 69787961743) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1 * (3 : ZMod 69787961743) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 69787961743) ^ 5 = 243 := by
        calc
          (3 : ZMod 69787961743) ^ 5 = (3 : ZMod 69787961743) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 2 * (3 : ZMod 69787961743) ^ 2) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 69787961743) ^ 10 = 59049 := by
        calc
          (3 : ZMod 69787961743) ^ 10 = (3 : ZMod 69787961743) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 5 * (3 : ZMod 69787961743) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 69787961743) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 69787961743) ^ 21 = (3 : ZMod 69787961743) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 10 * (3 : ZMod 69787961743) ^ 10) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 69787961743) ^ 43 = 324890383 := by
        calc
          (3 : ZMod 69787961743) ^ 43 = (3 : ZMod 69787961743) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 21 * (3 : ZMod 69787961743) ^ 21) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 324890383 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 69787961743) ^ 86 = 27133293133 := by
        calc
          (3 : ZMod 69787961743) ^ 86 = (3 : ZMod 69787961743) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 43 * (3 : ZMod 69787961743) ^ 43 := by rw [pow_add]
          _ = 27133293133 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 69787961743) ^ 173 = 67116097811 := by
        calc
          (3 : ZMod 69787961743) ^ 173 = (3 : ZMod 69787961743) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 86 * (3 : ZMod 69787961743) ^ 86) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 67116097811 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 69787961743) ^ 346 = 52502001320 := by
        calc
          (3 : ZMod 69787961743) ^ 346 = (3 : ZMod 69787961743) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 173 * (3 : ZMod 69787961743) ^ 173 := by rw [pow_add]
          _ = 52502001320 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 69787961743) ^ 693 = 30134752773 := by
        calc
          (3 : ZMod 69787961743) ^ 693 = (3 : ZMod 69787961743) ^ (346 + 346 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 346 * (3 : ZMod 69787961743) ^ 346) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 30134752773 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 69787961743) ^ 1386 = 6480251973 := by
        calc
          (3 : ZMod 69787961743) ^ 1386 = (3 : ZMod 69787961743) ^ (693 + 693) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 693 * (3 : ZMod 69787961743) ^ 693 := by rw [pow_add]
          _ = 6480251973 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 69787961743) ^ 2773 = 58280564947 := by
        calc
          (3 : ZMod 69787961743) ^ 2773 = (3 : ZMod 69787961743) ^ (1386 + 1386 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1386 * (3 : ZMod 69787961743) ^ 1386) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 58280564947 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 69787961743) ^ 5546 = 39071015971 := by
        calc
          (3 : ZMod 69787961743) ^ 5546 = (3 : ZMod 69787961743) ^ (2773 + 2773) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2773 * (3 : ZMod 69787961743) ^ 2773 := by rw [pow_add]
          _ = 39071015971 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 69787961743) ^ 11092 = 13734305957 := by
        calc
          (3 : ZMod 69787961743) ^ 11092 = (3 : ZMod 69787961743) ^ (5546 + 5546) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 5546 * (3 : ZMod 69787961743) ^ 5546 := by rw [pow_add]
          _ = 13734305957 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 69787961743) ^ 22184 = 19235739318 := by
        calc
          (3 : ZMod 69787961743) ^ 22184 = (3 : ZMod 69787961743) ^ (11092 + 11092) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 11092 * (3 : ZMod 69787961743) ^ 11092 := by rw [pow_add]
          _ = 19235739318 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 69787961743) ^ 44369 = 29323756134 := by
        calc
          (3 : ZMod 69787961743) ^ 44369 = (3 : ZMod 69787961743) ^ (22184 + 22184 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 22184 * (3 : ZMod 69787961743) ^ 22184) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 29323756134 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 69787961743) ^ 88739 = 53545291731 := by
        calc
          (3 : ZMod 69787961743) ^ 88739 = (3 : ZMod 69787961743) ^ (44369 + 44369 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 44369 * (3 : ZMod 69787961743) ^ 44369) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 53545291731 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 69787961743) ^ 177479 = 53913518843 := by
        calc
          (3 : ZMod 69787961743) ^ 177479 = (3 : ZMod 69787961743) ^ (88739 + 88739 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 88739 * (3 : ZMod 69787961743) ^ 88739) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 53913518843 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 69787961743) ^ 354959 = 46897359428 := by
        calc
          (3 : ZMod 69787961743) ^ 354959 = (3 : ZMod 69787961743) ^ (177479 + 177479 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 177479 * (3 : ZMod 69787961743) ^ 177479) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 46897359428 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 69787961743) ^ 709919 = 29425731571 := by
        calc
          (3 : ZMod 69787961743) ^ 709919 = (3 : ZMod 69787961743) ^ (354959 + 354959 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 354959 * (3 : ZMod 69787961743) ^ 354959) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 29425731571 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 69787961743) ^ 1419839 = 43346213921 := by
        calc
          (3 : ZMod 69787961743) ^ 1419839 = (3 : ZMod 69787961743) ^ (709919 + 709919 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 709919 * (3 : ZMod 69787961743) ^ 709919) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 43346213921 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 69787961743) ^ 2839679 = 61721764740 := by
        calc
          (3 : ZMod 69787961743) ^ 2839679 = (3 : ZMod 69787961743) ^ (1419839 + 1419839 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1419839 * (3 : ZMod 69787961743) ^ 1419839) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 61721764740 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 69787961743) ^ 5679358 = 38494414307 := by
        calc
          (3 : ZMod 69787961743) ^ 5679358 = (3 : ZMod 69787961743) ^ (2839679 + 2839679) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2839679 * (3 : ZMod 69787961743) ^ 2839679 := by rw [pow_add]
          _ = 38494414307 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 69787961743) ^ 11358717 = 65488772902 := by
        calc
          (3 : ZMod 69787961743) ^ 11358717 = (3 : ZMod 69787961743) ^ (5679358 + 5679358 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 5679358 * (3 : ZMod 69787961743) ^ 5679358) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 65488772902 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 69787961743) ^ 22717435 = 69390791704 := by
        calc
          (3 : ZMod 69787961743) ^ 22717435 = (3 : ZMod 69787961743) ^ (11358717 + 11358717 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 11358717 * (3 : ZMod 69787961743) ^ 11358717) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 69390791704 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 69787961743) ^ 45434870 = 6948821102 := by
        calc
          (3 : ZMod 69787961743) ^ 45434870 = (3 : ZMod 69787961743) ^ (22717435 + 22717435) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 22717435 * (3 : ZMod 69787961743) ^ 22717435 := by rw [pow_add]
          _ = 6948821102 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 69787961743) ^ 90869741 = 18362892493 := by
        calc
          (3 : ZMod 69787961743) ^ 90869741 = (3 : ZMod 69787961743) ^ (45434870 + 45434870 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 45434870 * (3 : ZMod 69787961743) ^ 45434870) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 18362892493 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 69787961743) ^ 181739483 = 23436575890 := by
        calc
          (3 : ZMod 69787961743) ^ 181739483 = (3 : ZMod 69787961743) ^ (90869741 + 90869741 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 90869741 * (3 : ZMod 69787961743) ^ 90869741) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 23436575890 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 69787961743) ^ 363478967 = 64546963331 := by
        calc
          (3 : ZMod 69787961743) ^ 363478967 = (3 : ZMod 69787961743) ^ (181739483 + 181739483 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 181739483 * (3 : ZMod 69787961743) ^ 181739483) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 64546963331 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 69787961743) ^ 726957934 = 31988005607 := by
        calc
          (3 : ZMod 69787961743) ^ 726957934 = (3 : ZMod 69787961743) ^ (363478967 + 363478967) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 363478967 * (3 : ZMod 69787961743) ^ 363478967 := by rw [pow_add]
          _ = 31988005607 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 69787961743) ^ 1453915869 = 43227246417 := by
        calc
          (3 : ZMod 69787961743) ^ 1453915869 = (3 : ZMod 69787961743) ^ (726957934 + 726957934 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 726957934 * (3 : ZMod 69787961743) ^ 726957934) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 43227246417 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 69787961743) ^ 2907831739 = 22993887999 := by
        calc
          (3 : ZMod 69787961743) ^ 2907831739 = (3 : ZMod 69787961743) ^ (1453915869 + 1453915869 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1453915869 * (3 : ZMod 69787961743) ^ 1453915869) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 22993887999 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 69787961743) ^ 5815663478 = 9606574321 := by
        calc
          (3 : ZMod 69787961743) ^ 5815663478 = (3 : ZMod 69787961743) ^ (2907831739 + 2907831739) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2907831739 * (3 : ZMod 69787961743) ^ 2907831739 := by rw [pow_add]
          _ = 9606574321 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 69787961743) ^ 11631326957 = 40968238779 := by
        calc
          (3 : ZMod 69787961743) ^ 11631326957 = (3 : ZMod 69787961743) ^ (5815663478 + 5815663478 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 5815663478 * (3 : ZMod 69787961743) ^ 5815663478) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 40968238779 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 69787961743) ^ 23262653914 = 40968238778 := by
        calc
          (3 : ZMod 69787961743) ^ 23262653914 = (3 : ZMod 69787961743) ^ (11631326957 + 11631326957) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 11631326957 * (3 : ZMod 69787961743) ^ 11631326957 := by rw [pow_add]
          _ = 40968238778 := by rw [factor_1_33]; decide
      change (3 : ZMod 69787961743) ^ 23262653914 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (3 : ZMod 69787961743) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 69787961743) ^ 3 = 27 := by
        calc
          (3 : ZMod 69787961743) ^ 3 = (3 : ZMod 69787961743) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1 * (3 : ZMod 69787961743) ^ 1) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 69787961743) ^ 6 = 729 := by
        calc
          (3 : ZMod 69787961743) ^ 6 = (3 : ZMod 69787961743) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 3 * (3 : ZMod 69787961743) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 69787961743) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 69787961743) ^ 13 = (3 : ZMod 69787961743) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 6 * (3 : ZMod 69787961743) ^ 6) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 69787961743) ^ 27 = 18709655000 := by
        calc
          (3 : ZMod 69787961743) ^ 27 = (3 : ZMod 69787961743) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 13 * (3 : ZMod 69787961743) ^ 13) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 18709655000 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 69787961743) ^ 54 = 48076201069 := by
        calc
          (3 : ZMod 69787961743) ^ 54 = (3 : ZMod 69787961743) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 27 * (3 : ZMod 69787961743) ^ 27 := by rw [pow_add]
          _ = 48076201069 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 69787961743) ^ 109 = 13804342710 := by
        calc
          (3 : ZMod 69787961743) ^ 109 = (3 : ZMod 69787961743) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 54 * (3 : ZMod 69787961743) ^ 54) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 13804342710 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 69787961743) ^ 218 = 7658135080 := by
        calc
          (3 : ZMod 69787961743) ^ 218 = (3 : ZMod 69787961743) ^ (109 + 109) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 109 * (3 : ZMod 69787961743) ^ 109 := by rw [pow_add]
          _ = 7658135080 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 69787961743) ^ 437 = 54188499126 := by
        calc
          (3 : ZMod 69787961743) ^ 437 = (3 : ZMod 69787961743) ^ (218 + 218 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 218 * (3 : ZMod 69787961743) ^ 218) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 54188499126 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 69787961743) ^ 875 = 6639315984 := by
        calc
          (3 : ZMod 69787961743) ^ 875 = (3 : ZMod 69787961743) ^ (437 + 437 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 437 * (3 : ZMod 69787961743) ^ 437) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 6639315984 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 69787961743) ^ 1751 = 26886156269 := by
        calc
          (3 : ZMod 69787961743) ^ 1751 = (3 : ZMod 69787961743) ^ (875 + 875 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 875 * (3 : ZMod 69787961743) ^ 875) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 26886156269 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 69787961743) ^ 3502 = 15417082242 := by
        calc
          (3 : ZMod 69787961743) ^ 3502 = (3 : ZMod 69787961743) ^ (1751 + 1751) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1751 * (3 : ZMod 69787961743) ^ 1751 := by rw [pow_add]
          _ = 15417082242 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 69787961743) ^ 7005 = 46629813219 := by
        calc
          (3 : ZMod 69787961743) ^ 7005 = (3 : ZMod 69787961743) ^ (3502 + 3502 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 3502 * (3 : ZMod 69787961743) ^ 3502) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 46629813219 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 69787961743) ^ 14011 = 54284409526 := by
        calc
          (3 : ZMod 69787961743) ^ 14011 = (3 : ZMod 69787961743) ^ (7005 + 7005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 7005 * (3 : ZMod 69787961743) ^ 7005) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 54284409526 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 69787961743) ^ 28023 = 1581711569 := by
        calc
          (3 : ZMod 69787961743) ^ 28023 = (3 : ZMod 69787961743) ^ (14011 + 14011 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 14011 * (3 : ZMod 69787961743) ^ 14011) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 1581711569 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 69787961743) ^ 56046 = 14822223539 := by
        calc
          (3 : ZMod 69787961743) ^ 56046 = (3 : ZMod 69787961743) ^ (28023 + 28023) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 28023 * (3 : ZMod 69787961743) ^ 28023 := by rw [pow_add]
          _ = 14822223539 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 69787961743) ^ 112092 = 16825049491 := by
        calc
          (3 : ZMod 69787961743) ^ 112092 = (3 : ZMod 69787961743) ^ (56046 + 56046) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 56046 * (3 : ZMod 69787961743) ^ 56046 := by rw [pow_add]
          _ = 16825049491 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 69787961743) ^ 224185 = 18540771847 := by
        calc
          (3 : ZMod 69787961743) ^ 224185 = (3 : ZMod 69787961743) ^ (112092 + 112092 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 112092 * (3 : ZMod 69787961743) ^ 112092) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 18540771847 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 69787961743) ^ 448370 = 24318071628 := by
        calc
          (3 : ZMod 69787961743) ^ 448370 = (3 : ZMod 69787961743) ^ (224185 + 224185) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 224185 * (3 : ZMod 69787961743) ^ 224185 := by rw [pow_add]
          _ = 24318071628 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 69787961743) ^ 896740 = 65111879687 := by
        calc
          (3 : ZMod 69787961743) ^ 896740 = (3 : ZMod 69787961743) ^ (448370 + 448370) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 448370 * (3 : ZMod 69787961743) ^ 448370 := by rw [pow_add]
          _ = 65111879687 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 69787961743) ^ 1793481 = 20930184221 := by
        calc
          (3 : ZMod 69787961743) ^ 1793481 = (3 : ZMod 69787961743) ^ (896740 + 896740 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 896740 * (3 : ZMod 69787961743) ^ 896740) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 20930184221 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 69787961743) ^ 3586963 = 64057188840 := by
        calc
          (3 : ZMod 69787961743) ^ 3586963 = (3 : ZMod 69787961743) ^ (1793481 + 1793481 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1793481 * (3 : ZMod 69787961743) ^ 1793481) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 64057188840 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 69787961743) ^ 7173926 = 31712855344 := by
        calc
          (3 : ZMod 69787961743) ^ 7173926 = (3 : ZMod 69787961743) ^ (3586963 + 3586963) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 3586963 * (3 : ZMod 69787961743) ^ 3586963 := by rw [pow_add]
          _ = 31712855344 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 69787961743) ^ 14347853 = 11002324659 := by
        calc
          (3 : ZMod 69787961743) ^ 14347853 = (3 : ZMod 69787961743) ^ (7173926 + 7173926 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 7173926 * (3 : ZMod 69787961743) ^ 7173926) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 11002324659 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 69787961743) ^ 28695707 = 32258167148 := by
        calc
          (3 : ZMod 69787961743) ^ 28695707 = (3 : ZMod 69787961743) ^ (14347853 + 14347853 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 14347853 * (3 : ZMod 69787961743) ^ 14347853) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 32258167148 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 69787961743) ^ 57391415 = 8512132998 := by
        calc
          (3 : ZMod 69787961743) ^ 57391415 = (3 : ZMod 69787961743) ^ (28695707 + 28695707 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 28695707 * (3 : ZMod 69787961743) ^ 28695707) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 8512132998 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 69787961743) ^ 114782831 = 31457138718 := by
        calc
          (3 : ZMod 69787961743) ^ 114782831 = (3 : ZMod 69787961743) ^ (57391415 + 57391415 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 57391415 * (3 : ZMod 69787961743) ^ 57391415) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 31457138718 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 69787961743) ^ 229565663 = 16042733184 := by
        calc
          (3 : ZMod 69787961743) ^ 229565663 = (3 : ZMod 69787961743) ^ (114782831 + 114782831 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 114782831 * (3 : ZMod 69787961743) ^ 114782831) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 16042733184 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 69787961743) ^ 459131327 = 48388075401 := by
        calc
          (3 : ZMod 69787961743) ^ 459131327 = (3 : ZMod 69787961743) ^ (229565663 + 229565663 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 229565663 * (3 : ZMod 69787961743) ^ 229565663) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 48388075401 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 69787961743) ^ 918262654 = 14644077996 := by
        calc
          (3 : ZMod 69787961743) ^ 918262654 = (3 : ZMod 69787961743) ^ (459131327 + 459131327) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 459131327 * (3 : ZMod 69787961743) ^ 459131327 := by rw [pow_add]
          _ = 14644077996 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 69787961743) ^ 1836525309 = 6245078917 := by
        calc
          (3 : ZMod 69787961743) ^ 1836525309 = (3 : ZMod 69787961743) ^ (918262654 + 918262654 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 918262654 * (3 : ZMod 69787961743) ^ 918262654) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 6245078917 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 69787961743) ^ 3673050618 = 24502857215 := by
        calc
          (3 : ZMod 69787961743) ^ 3673050618 = (3 : ZMod 69787961743) ^ (1836525309 + 1836525309) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1836525309 * (3 : ZMod 69787961743) ^ 1836525309 := by rw [pow_add]
          _ = 24502857215 := by rw [factor_2_30]; decide
      change (3 : ZMod 69787961743) ^ 3673050618 ≠ 1
      rw [factor_2_31]
      decide
    ·
      have factor_3_0 : (3 : ZMod 69787961743) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 69787961743) ^ 3 = 27 := by
        calc
          (3 : ZMod 69787961743) ^ 3 = (3 : ZMod 69787961743) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1 * (3 : ZMod 69787961743) ^ 1) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 69787961743) ^ 6 = 729 := by
        calc
          (3 : ZMod 69787961743) ^ 6 = (3 : ZMod 69787961743) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 3 * (3 : ZMod 69787961743) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 69787961743) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 69787961743) ^ 13 = (3 : ZMod 69787961743) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 6 * (3 : ZMod 69787961743) ^ 6) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 69787961743) ^ 26 = 29499205581 := by
        calc
          (3 : ZMod 69787961743) ^ 26 = (3 : ZMod 69787961743) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 13 * (3 : ZMod 69787961743) ^ 13 := by rw [pow_add]
          _ = 29499205581 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 69787961743) ^ 53 = 62550708185 := by
        calc
          (3 : ZMod 69787961743) ^ 53 = (3 : ZMod 69787961743) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 26 * (3 : ZMod 69787961743) ^ 26) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 62550708185 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 69787961743) ^ 106 = 31528143838 := by
        calc
          (3 : ZMod 69787961743) ^ 106 = (3 : ZMod 69787961743) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 53 * (3 : ZMod 69787961743) ^ 53 := by rw [pow_add]
          _ = 31528143838 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 69787961743) ^ 212 = 47876048020 := by
        calc
          (3 : ZMod 69787961743) ^ 212 = (3 : ZMod 69787961743) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 106 * (3 : ZMod 69787961743) ^ 106 := by rw [pow_add]
          _ = 47876048020 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 69787961743) ^ 425 = 43590444398 := by
        calc
          (3 : ZMod 69787961743) ^ 425 = (3 : ZMod 69787961743) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 212 * (3 : ZMod 69787961743) ^ 212) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 43590444398 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 69787961743) ^ 850 = 7299095288 := by
        calc
          (3 : ZMod 69787961743) ^ 850 = (3 : ZMod 69787961743) ^ (425 + 425) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 425 * (3 : ZMod 69787961743) ^ 425 := by rw [pow_add]
          _ = 7299095288 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 69787961743) ^ 1701 = 60277526538 := by
        calc
          (3 : ZMod 69787961743) ^ 1701 = (3 : ZMod 69787961743) ^ (850 + 850 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 850 * (3 : ZMod 69787961743) ^ 850) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 60277526538 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 69787961743) ^ 3402 = 39402266174 := by
        calc
          (3 : ZMod 69787961743) ^ 3402 = (3 : ZMod 69787961743) ^ (1701 + 1701) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1701 * (3 : ZMod 69787961743) ^ 1701 := by rw [pow_add]
          _ = 39402266174 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 69787961743) ^ 6804 = 63488618352 := by
        calc
          (3 : ZMod 69787961743) ^ 6804 = (3 : ZMod 69787961743) ^ (3402 + 3402) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 3402 * (3 : ZMod 69787961743) ^ 3402 := by rw [pow_add]
          _ = 63488618352 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 69787961743) ^ 13608 = 48045684426 := by
        calc
          (3 : ZMod 69787961743) ^ 13608 = (3 : ZMod 69787961743) ^ (6804 + 6804) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 6804 * (3 : ZMod 69787961743) ^ 6804 := by rw [pow_add]
          _ = 48045684426 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 69787961743) ^ 27217 = 59481276963 := by
        calc
          (3 : ZMod 69787961743) ^ 27217 = (3 : ZMod 69787961743) ^ (13608 + 13608 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 13608 * (3 : ZMod 69787961743) ^ 13608) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 59481276963 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 69787961743) ^ 54434 = 22867029418 := by
        calc
          (3 : ZMod 69787961743) ^ 54434 = (3 : ZMod 69787961743) ^ (27217 + 27217) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 27217 * (3 : ZMod 69787961743) ^ 27217 := by rw [pow_add]
          _ = 22867029418 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 69787961743) ^ 108869 = 45551924908 := by
        calc
          (3 : ZMod 69787961743) ^ 108869 = (3 : ZMod 69787961743) ^ (54434 + 54434 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 54434 * (3 : ZMod 69787961743) ^ 54434) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 45551924908 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 69787961743) ^ 217738 = 40475749455 := by
        calc
          (3 : ZMod 69787961743) ^ 217738 = (3 : ZMod 69787961743) ^ (108869 + 108869) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 108869 * (3 : ZMod 69787961743) ^ 108869 := by rw [pow_add]
          _ = 40475749455 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 69787961743) ^ 435477 = 36241744592 := by
        calc
          (3 : ZMod 69787961743) ^ 435477 = (3 : ZMod 69787961743) ^ (217738 + 217738 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 217738 * (3 : ZMod 69787961743) ^ 217738) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 36241744592 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 69787961743) ^ 870955 = 33335298737 := by
        calc
          (3 : ZMod 69787961743) ^ 870955 = (3 : ZMod 69787961743) ^ (435477 + 435477 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 435477 * (3 : ZMod 69787961743) ^ 435477) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 33335298737 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 69787961743) ^ 1741911 = 45865213299 := by
        calc
          (3 : ZMod 69787961743) ^ 1741911 = (3 : ZMod 69787961743) ^ (870955 + 870955 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 870955 * (3 : ZMod 69787961743) ^ 870955) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 45865213299 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 69787961743) ^ 3483823 = 36675626318 := by
        calc
          (3 : ZMod 69787961743) ^ 3483823 = (3 : ZMod 69787961743) ^ (1741911 + 1741911 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 1741911 * (3 : ZMod 69787961743) ^ 1741911) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 36675626318 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 69787961743) ^ 6967647 = 54144546870 := by
        calc
          (3 : ZMod 69787961743) ^ 6967647 = (3 : ZMod 69787961743) ^ (3483823 + 3483823 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 3483823 * (3 : ZMod 69787961743) ^ 3483823) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 54144546870 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 69787961743) ^ 13935295 = 8254181701 := by
        calc
          (3 : ZMod 69787961743) ^ 13935295 = (3 : ZMod 69787961743) ^ (6967647 + 6967647 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 6967647 * (3 : ZMod 69787961743) ^ 6967647) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 8254181701 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 69787961743) ^ 27870591 = 62504483495 := by
        calc
          (3 : ZMod 69787961743) ^ 27870591 = (3 : ZMod 69787961743) ^ (13935295 + 13935295 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 13935295 * (3 : ZMod 69787961743) ^ 13935295) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 62504483495 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 69787961743) ^ 55741183 = 66353340646 := by
        calc
          (3 : ZMod 69787961743) ^ 55741183 = (3 : ZMod 69787961743) ^ (27870591 + 27870591 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 27870591 * (3 : ZMod 69787961743) ^ 27870591) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 66353340646 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 69787961743) ^ 111482367 = 27411389427 := by
        calc
          (3 : ZMod 69787961743) ^ 111482367 = (3 : ZMod 69787961743) ^ (55741183 + 55741183 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 55741183 * (3 : ZMod 69787961743) ^ 55741183) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 27411389427 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 69787961743) ^ 222964734 = 49886920796 := by
        calc
          (3 : ZMod 69787961743) ^ 222964734 = (3 : ZMod 69787961743) ^ (111482367 + 111482367) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 111482367 * (3 : ZMod 69787961743) ^ 111482367 := by rw [pow_add]
          _ = 49886920796 := by rw [factor_3_26]; decide
      change (3 : ZMod 69787961743) ^ 222964734 ≠ 1
      rw [factor_3_27]
      decide
    ·
      have factor_4_0 : (3 : ZMod 69787961743) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 69787961743) ^ 2 = 9 := by
        calc
          (3 : ZMod 69787961743) ^ 2 = (3 : ZMod 69787961743) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1 * (3 : ZMod 69787961743) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 69787961743) ^ 4 = 81 := by
        calc
          (3 : ZMod 69787961743) ^ 4 = (3 : ZMod 69787961743) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2 * (3 : ZMod 69787961743) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 69787961743) ^ 8 = 6561 := by
        calc
          (3 : ZMod 69787961743) ^ 8 = (3 : ZMod 69787961743) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 4 * (3 : ZMod 69787961743) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 69787961743) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 69787961743) ^ 17 = (3 : ZMod 69787961743) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 8 * (3 : ZMod 69787961743) ^ 8) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 69787961743) ^ 34 = 22269903602 := by
        calc
          (3 : ZMod 69787961743) ^ 34 = (3 : ZMod 69787961743) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 17 * (3 : ZMod 69787961743) ^ 17 := by rw [pow_add]
          _ = 22269903602 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 69787961743) ^ 69 = 56359634267 := by
        calc
          (3 : ZMod 69787961743) ^ 69 = (3 : ZMod 69787961743) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 34 * (3 : ZMod 69787961743) ^ 34) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 56359634267 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 69787961743) ^ 139 = 34462723380 := by
        calc
          (3 : ZMod 69787961743) ^ 139 = (3 : ZMod 69787961743) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 69 * (3 : ZMod 69787961743) ^ 69) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 34462723380 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 69787961743) ^ 278 = 7651735069 := by
        calc
          (3 : ZMod 69787961743) ^ 278 = (3 : ZMod 69787961743) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 139 * (3 : ZMod 69787961743) ^ 139 := by rw [pow_add]
          _ = 7651735069 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 69787961743) ^ 557 = 7633816901 := by
        calc
          (3 : ZMod 69787961743) ^ 557 = (3 : ZMod 69787961743) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 278 * (3 : ZMod 69787961743) ^ 278) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 7633816901 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 69787961743) ^ 1115 = 13875201645 := by
        calc
          (3 : ZMod 69787961743) ^ 1115 = (3 : ZMod 69787961743) ^ (557 + 557 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 557 * (3 : ZMod 69787961743) ^ 557) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 13875201645 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 69787961743) ^ 2230 = 42329552474 := by
        calc
          (3 : ZMod 69787961743) ^ 2230 = (3 : ZMod 69787961743) ^ (1115 + 1115) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 1115 * (3 : ZMod 69787961743) ^ 1115 := by rw [pow_add]
          _ = 42329552474 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 69787961743) ^ 4460 = 1099705387 := by
        calc
          (3 : ZMod 69787961743) ^ 4460 = (3 : ZMod 69787961743) ^ (2230 + 2230) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 2230 * (3 : ZMod 69787961743) ^ 2230 := by rw [pow_add]
          _ = 1099705387 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 69787961743) ^ 8920 = 47914345148 := by
        calc
          (3 : ZMod 69787961743) ^ 8920 = (3 : ZMod 69787961743) ^ (4460 + 4460) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 4460 * (3 : ZMod 69787961743) ^ 4460 := by rw [pow_add]
          _ = 47914345148 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 69787961743) ^ 17841 = 16900254569 := by
        calc
          (3 : ZMod 69787961743) ^ 17841 = (3 : ZMod 69787961743) ^ (8920 + 8920 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = ((3 : ZMod 69787961743) ^ 8920 * (3 : ZMod 69787961743) ^ 8920) * (3 : ZMod 69787961743) := by rw [pow_succ, pow_add]
          _ = 16900254569 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 69787961743) ^ 35682 = 22655356570 := by
        calc
          (3 : ZMod 69787961743) ^ 35682 = (3 : ZMod 69787961743) ^ (17841 + 17841) :=
            congrArg (fun n : ℕ => (3 : ZMod 69787961743) ^ n) (by norm_num)
          _ = (3 : ZMod 69787961743) ^ 17841 * (3 : ZMod 69787961743) ^ 17841 := by rw [pow_add]
          _ = 22655356570 := by rw [factor_4_14]; decide
      change (3 : ZMod 69787961743) ^ 35682 ≠ 1
      rw [factor_4_15]
      decide

#print axioms prime_lucas_69787961743

end TotientTailPeriodKiller
end Erdos249257
