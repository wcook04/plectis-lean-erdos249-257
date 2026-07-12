import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1519301737 : Nat.Prime 1519301737 := by
  apply lucas_primality 1519301737 (5 : ZMod 1519301737)
  ·
      have fermat_0 : (5 : ZMod 1519301737) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 1519301737) ^ 2 = 25 := by
        calc
          (5 : ZMod 1519301737) ^ 2 = (5 : ZMod 1519301737) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1 * (5 : ZMod 1519301737) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 1519301737) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1519301737) ^ 5 = (5 : ZMod 1519301737) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 2 * (5 : ZMod 1519301737) ^ 2) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 1519301737) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1519301737) ^ 11 = (5 : ZMod 1519301737) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 5 * (5 : ZMod 1519301737) ^ 5) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 1519301737) ^ 22 = 270004057 := by
        calc
          (5 : ZMod 1519301737) ^ 22 = (5 : ZMod 1519301737) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 11 * (5 : ZMod 1519301737) ^ 11 := by rw [pow_add]
          _ = 270004057 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 1519301737) ^ 45 = 718264184 := by
        calc
          (5 : ZMod 1519301737) ^ 45 = (5 : ZMod 1519301737) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 22 * (5 : ZMod 1519301737) ^ 22) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 718264184 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 1519301737) ^ 90 = 1053688517 := by
        calc
          (5 : ZMod 1519301737) ^ 90 = (5 : ZMod 1519301737) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 45 * (5 : ZMod 1519301737) ^ 45 := by rw [pow_add]
          _ = 1053688517 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 1519301737) ^ 181 = 681002830 := by
        calc
          (5 : ZMod 1519301737) ^ 181 = (5 : ZMod 1519301737) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 90 * (5 : ZMod 1519301737) ^ 90) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 681002830 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 1519301737) ^ 362 = 169146529 := by
        calc
          (5 : ZMod 1519301737) ^ 362 = (5 : ZMod 1519301737) ^ (181 + 181) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 181 * (5 : ZMod 1519301737) ^ 181 := by rw [pow_add]
          _ = 169146529 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 1519301737) ^ 724 = 1447942518 := by
        calc
          (5 : ZMod 1519301737) ^ 724 = (5 : ZMod 1519301737) ^ (362 + 362) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 362 * (5 : ZMod 1519301737) ^ 362 := by rw [pow_add]
          _ = 1447942518 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 1519301737) ^ 1448 = 855508651 := by
        calc
          (5 : ZMod 1519301737) ^ 1448 = (5 : ZMod 1519301737) ^ (724 + 724) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 724 * (5 : ZMod 1519301737) ^ 724 := by rw [pow_add]
          _ = 855508651 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 1519301737) ^ 2897 = 1370011372 := by
        calc
          (5 : ZMod 1519301737) ^ 2897 = (5 : ZMod 1519301737) ^ (1448 + 1448 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1448 * (5 : ZMod 1519301737) ^ 1448) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1370011372 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 1519301737) ^ 5795 = 1031023618 := by
        calc
          (5 : ZMod 1519301737) ^ 5795 = (5 : ZMod 1519301737) ^ (2897 + 2897 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 2897 * (5 : ZMod 1519301737) ^ 2897) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1031023618 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 1519301737) ^ 11591 = 480631643 := by
        calc
          (5 : ZMod 1519301737) ^ 11591 = (5 : ZMod 1519301737) ^ (5795 + 5795 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 5795 * (5 : ZMod 1519301737) ^ 5795) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 480631643 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 1519301737) ^ 23182 = 938520819 := by
        calc
          (5 : ZMod 1519301737) ^ 23182 = (5 : ZMod 1519301737) ^ (11591 + 11591) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 11591 * (5 : ZMod 1519301737) ^ 11591 := by rw [pow_add]
          _ = 938520819 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 1519301737) ^ 46365 = 475772980 := by
        calc
          (5 : ZMod 1519301737) ^ 46365 = (5 : ZMod 1519301737) ^ (23182 + 23182 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 23182 * (5 : ZMod 1519301737) ^ 23182) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 475772980 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 1519301737) ^ 92730 = 1357009224 := by
        calc
          (5 : ZMod 1519301737) ^ 92730 = (5 : ZMod 1519301737) ^ (46365 + 46365) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 46365 * (5 : ZMod 1519301737) ^ 46365 := by rw [pow_add]
          _ = 1357009224 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 1519301737) ^ 185461 = 1278217560 := by
        calc
          (5 : ZMod 1519301737) ^ 185461 = (5 : ZMod 1519301737) ^ (92730 + 92730 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 92730 * (5 : ZMod 1519301737) ^ 92730) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1278217560 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 1519301737) ^ 370923 = 1284804759 := by
        calc
          (5 : ZMod 1519301737) ^ 370923 = (5 : ZMod 1519301737) ^ (185461 + 185461 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 185461 * (5 : ZMod 1519301737) ^ 185461) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1284804759 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 1519301737) ^ 741846 = 466040354 := by
        calc
          (5 : ZMod 1519301737) ^ 741846 = (5 : ZMod 1519301737) ^ (370923 + 370923) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 370923 * (5 : ZMod 1519301737) ^ 370923 := by rw [pow_add]
          _ = 466040354 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 1519301737) ^ 1483693 = 367180944 := by
        calc
          (5 : ZMod 1519301737) ^ 1483693 = (5 : ZMod 1519301737) ^ (741846 + 741846 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 741846 * (5 : ZMod 1519301737) ^ 741846) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 367180944 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 1519301737) ^ 2967386 = 80083660 := by
        calc
          (5 : ZMod 1519301737) ^ 2967386 = (5 : ZMod 1519301737) ^ (1483693 + 1483693) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1483693 * (5 : ZMod 1519301737) ^ 1483693 := by rw [pow_add]
          _ = 80083660 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 1519301737) ^ 5934772 = 639839188 := by
        calc
          (5 : ZMod 1519301737) ^ 5934772 = (5 : ZMod 1519301737) ^ (2967386 + 2967386) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 2967386 * (5 : ZMod 1519301737) ^ 2967386 := by rw [pow_add]
          _ = 639839188 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 1519301737) ^ 11869544 = 51788965 := by
        calc
          (5 : ZMod 1519301737) ^ 11869544 = (5 : ZMod 1519301737) ^ (5934772 + 5934772) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 5934772 * (5 : ZMod 1519301737) ^ 5934772 := by rw [pow_add]
          _ = 51788965 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 1519301737) ^ 23739089 = 26205271 := by
        calc
          (5 : ZMod 1519301737) ^ 23739089 = (5 : ZMod 1519301737) ^ (11869544 + 11869544 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 11869544 * (5 : ZMod 1519301737) ^ 11869544) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 26205271 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 1519301737) ^ 47478179 = 236444104 := by
        calc
          (5 : ZMod 1519301737) ^ 47478179 = (5 : ZMod 1519301737) ^ (23739089 + 23739089 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 23739089 * (5 : ZMod 1519301737) ^ 23739089) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 236444104 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 1519301737) ^ 94956358 = 1450697388 := by
        calc
          (5 : ZMod 1519301737) ^ 94956358 = (5 : ZMod 1519301737) ^ (47478179 + 47478179) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 47478179 * (5 : ZMod 1519301737) ^ 47478179 := by rw [pow_add]
          _ = 1450697388 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 1519301737) ^ 189912717 = 1370112972 := by
        calc
          (5 : ZMod 1519301737) ^ 189912717 = (5 : ZMod 1519301737) ^ (94956358 + 94956358 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 94956358 * (5 : ZMod 1519301737) ^ 94956358) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1370112972 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 1519301737) ^ 379825434 = 293127591 := by
        calc
          (5 : ZMod 1519301737) ^ 379825434 = (5 : ZMod 1519301737) ^ (189912717 + 189912717) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 189912717 * (5 : ZMod 1519301737) ^ 189912717 := by rw [pow_add]
          _ = 293127591 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 1519301737) ^ 759650868 = 1519301736 := by
        calc
          (5 : ZMod 1519301737) ^ 759650868 = (5 : ZMod 1519301737) ^ (379825434 + 379825434) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 379825434 * (5 : ZMod 1519301737) ^ 379825434 := by rw [pow_add]
          _ = 1519301736 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 1519301737) ^ 1519301736 = 1 := by
        calc
          (5 : ZMod 1519301737) ^ 1519301736 = (5 : ZMod 1519301737) ^ (759650868 + 759650868) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 759650868 * (5 : ZMod 1519301737) ^ 759650868 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (71, 1), (439, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (71, 1), (439, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod = 1519301737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 1519301737) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 1519301737) ^ 2 = 25 := by
        calc
          (5 : ZMod 1519301737) ^ 2 = (5 : ZMod 1519301737) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1 * (5 : ZMod 1519301737) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 1519301737) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1519301737) ^ 5 = (5 : ZMod 1519301737) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 2 * (5 : ZMod 1519301737) ^ 2) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 1519301737) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 1519301737) ^ 11 = (5 : ZMod 1519301737) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 5 * (5 : ZMod 1519301737) ^ 5) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 1519301737) ^ 22 = 270004057 := by
        calc
          (5 : ZMod 1519301737) ^ 22 = (5 : ZMod 1519301737) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 11 * (5 : ZMod 1519301737) ^ 11 := by rw [pow_add]
          _ = 270004057 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 1519301737) ^ 45 = 718264184 := by
        calc
          (5 : ZMod 1519301737) ^ 45 = (5 : ZMod 1519301737) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 22 * (5 : ZMod 1519301737) ^ 22) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 718264184 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 1519301737) ^ 90 = 1053688517 := by
        calc
          (5 : ZMod 1519301737) ^ 90 = (5 : ZMod 1519301737) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 45 * (5 : ZMod 1519301737) ^ 45 := by rw [pow_add]
          _ = 1053688517 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 1519301737) ^ 181 = 681002830 := by
        calc
          (5 : ZMod 1519301737) ^ 181 = (5 : ZMod 1519301737) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 90 * (5 : ZMod 1519301737) ^ 90) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 681002830 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 1519301737) ^ 362 = 169146529 := by
        calc
          (5 : ZMod 1519301737) ^ 362 = (5 : ZMod 1519301737) ^ (181 + 181) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 181 * (5 : ZMod 1519301737) ^ 181 := by rw [pow_add]
          _ = 169146529 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 1519301737) ^ 724 = 1447942518 := by
        calc
          (5 : ZMod 1519301737) ^ 724 = (5 : ZMod 1519301737) ^ (362 + 362) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 362 * (5 : ZMod 1519301737) ^ 362 := by rw [pow_add]
          _ = 1447942518 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 1519301737) ^ 1448 = 855508651 := by
        calc
          (5 : ZMod 1519301737) ^ 1448 = (5 : ZMod 1519301737) ^ (724 + 724) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 724 * (5 : ZMod 1519301737) ^ 724 := by rw [pow_add]
          _ = 855508651 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 1519301737) ^ 2897 = 1370011372 := by
        calc
          (5 : ZMod 1519301737) ^ 2897 = (5 : ZMod 1519301737) ^ (1448 + 1448 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1448 * (5 : ZMod 1519301737) ^ 1448) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1370011372 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 1519301737) ^ 5795 = 1031023618 := by
        calc
          (5 : ZMod 1519301737) ^ 5795 = (5 : ZMod 1519301737) ^ (2897 + 2897 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 2897 * (5 : ZMod 1519301737) ^ 2897) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1031023618 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 1519301737) ^ 11591 = 480631643 := by
        calc
          (5 : ZMod 1519301737) ^ 11591 = (5 : ZMod 1519301737) ^ (5795 + 5795 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 5795 * (5 : ZMod 1519301737) ^ 5795) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 480631643 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 1519301737) ^ 23182 = 938520819 := by
        calc
          (5 : ZMod 1519301737) ^ 23182 = (5 : ZMod 1519301737) ^ (11591 + 11591) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 11591 * (5 : ZMod 1519301737) ^ 11591 := by rw [pow_add]
          _ = 938520819 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 1519301737) ^ 46365 = 475772980 := by
        calc
          (5 : ZMod 1519301737) ^ 46365 = (5 : ZMod 1519301737) ^ (23182 + 23182 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 23182 * (5 : ZMod 1519301737) ^ 23182) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 475772980 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 1519301737) ^ 92730 = 1357009224 := by
        calc
          (5 : ZMod 1519301737) ^ 92730 = (5 : ZMod 1519301737) ^ (46365 + 46365) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 46365 * (5 : ZMod 1519301737) ^ 46365 := by rw [pow_add]
          _ = 1357009224 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 1519301737) ^ 185461 = 1278217560 := by
        calc
          (5 : ZMod 1519301737) ^ 185461 = (5 : ZMod 1519301737) ^ (92730 + 92730 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 92730 * (5 : ZMod 1519301737) ^ 92730) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1278217560 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 1519301737) ^ 370923 = 1284804759 := by
        calc
          (5 : ZMod 1519301737) ^ 370923 = (5 : ZMod 1519301737) ^ (185461 + 185461 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 185461 * (5 : ZMod 1519301737) ^ 185461) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1284804759 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 1519301737) ^ 741846 = 466040354 := by
        calc
          (5 : ZMod 1519301737) ^ 741846 = (5 : ZMod 1519301737) ^ (370923 + 370923) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 370923 * (5 : ZMod 1519301737) ^ 370923 := by rw [pow_add]
          _ = 466040354 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 1519301737) ^ 1483693 = 367180944 := by
        calc
          (5 : ZMod 1519301737) ^ 1483693 = (5 : ZMod 1519301737) ^ (741846 + 741846 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 741846 * (5 : ZMod 1519301737) ^ 741846) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 367180944 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 1519301737) ^ 2967386 = 80083660 := by
        calc
          (5 : ZMod 1519301737) ^ 2967386 = (5 : ZMod 1519301737) ^ (1483693 + 1483693) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1483693 * (5 : ZMod 1519301737) ^ 1483693 := by rw [pow_add]
          _ = 80083660 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 1519301737) ^ 5934772 = 639839188 := by
        calc
          (5 : ZMod 1519301737) ^ 5934772 = (5 : ZMod 1519301737) ^ (2967386 + 2967386) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 2967386 * (5 : ZMod 1519301737) ^ 2967386 := by rw [pow_add]
          _ = 639839188 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 1519301737) ^ 11869544 = 51788965 := by
        calc
          (5 : ZMod 1519301737) ^ 11869544 = (5 : ZMod 1519301737) ^ (5934772 + 5934772) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 5934772 * (5 : ZMod 1519301737) ^ 5934772 := by rw [pow_add]
          _ = 51788965 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 1519301737) ^ 23739089 = 26205271 := by
        calc
          (5 : ZMod 1519301737) ^ 23739089 = (5 : ZMod 1519301737) ^ (11869544 + 11869544 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 11869544 * (5 : ZMod 1519301737) ^ 11869544) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 26205271 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 1519301737) ^ 47478179 = 236444104 := by
        calc
          (5 : ZMod 1519301737) ^ 47478179 = (5 : ZMod 1519301737) ^ (23739089 + 23739089 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 23739089 * (5 : ZMod 1519301737) ^ 23739089) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 236444104 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 1519301737) ^ 94956358 = 1450697388 := by
        calc
          (5 : ZMod 1519301737) ^ 94956358 = (5 : ZMod 1519301737) ^ (47478179 + 47478179) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 47478179 * (5 : ZMod 1519301737) ^ 47478179 := by rw [pow_add]
          _ = 1450697388 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 1519301737) ^ 189912717 = 1370112972 := by
        calc
          (5 : ZMod 1519301737) ^ 189912717 = (5 : ZMod 1519301737) ^ (94956358 + 94956358 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 94956358 * (5 : ZMod 1519301737) ^ 94956358) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1370112972 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 1519301737) ^ 379825434 = 293127591 := by
        calc
          (5 : ZMod 1519301737) ^ 379825434 = (5 : ZMod 1519301737) ^ (189912717 + 189912717) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 189912717 * (5 : ZMod 1519301737) ^ 189912717 := by rw [pow_add]
          _ = 293127591 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 1519301737) ^ 759650868 = 1519301736 := by
        calc
          (5 : ZMod 1519301737) ^ 759650868 = (5 : ZMod 1519301737) ^ (379825434 + 379825434) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 379825434 * (5 : ZMod 1519301737) ^ 379825434 := by rw [pow_add]
          _ = 1519301736 := by rw [factor_0_28]; decide
      change (5 : ZMod 1519301737) ^ 759650868 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (5 : ZMod 1519301737) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 1519301737) ^ 3 = 125 := by
        calc
          (5 : ZMod 1519301737) ^ 3 = (5 : ZMod 1519301737) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1 * (5 : ZMod 1519301737) ^ 1) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 1519301737) ^ 7 = 78125 := by
        calc
          (5 : ZMod 1519301737) ^ 7 = (5 : ZMod 1519301737) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 3 * (5 : ZMod 1519301737) ^ 3) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 1519301737) ^ 15 = 131543385 := by
        calc
          (5 : ZMod 1519301737) ^ 15 = (5 : ZMod 1519301737) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 7 * (5 : ZMod 1519301737) ^ 7) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 131543385 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 1519301737) ^ 30 = 408183085 := by
        calc
          (5 : ZMod 1519301737) ^ 30 = (5 : ZMod 1519301737) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 15 * (5 : ZMod 1519301737) ^ 15 := by rw [pow_add]
          _ = 408183085 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 1519301737) ^ 60 = 486820676 := by
        calc
          (5 : ZMod 1519301737) ^ 60 = (5 : ZMod 1519301737) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 30 * (5 : ZMod 1519301737) ^ 30 := by rw [pow_add]
          _ = 486820676 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 1519301737) ^ 120 = 1293091817 := by
        calc
          (5 : ZMod 1519301737) ^ 120 = (5 : ZMod 1519301737) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 60 * (5 : ZMod 1519301737) ^ 60 := by rw [pow_add]
          _ = 1293091817 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 1519301737) ^ 241 = 323799666 := by
        calc
          (5 : ZMod 1519301737) ^ 241 = (5 : ZMod 1519301737) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 120 * (5 : ZMod 1519301737) ^ 120) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 323799666 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 1519301737) ^ 482 = 868244796 := by
        calc
          (5 : ZMod 1519301737) ^ 482 = (5 : ZMod 1519301737) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 241 * (5 : ZMod 1519301737) ^ 241 := by rw [pow_add]
          _ = 868244796 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 1519301737) ^ 965 = 1044605677 := by
        calc
          (5 : ZMod 1519301737) ^ 965 = (5 : ZMod 1519301737) ^ (482 + 482 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 482 * (5 : ZMod 1519301737) ^ 482) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1044605677 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 1519301737) ^ 1931 = 637485580 := by
        calc
          (5 : ZMod 1519301737) ^ 1931 = (5 : ZMod 1519301737) ^ (965 + 965 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 965 * (5 : ZMod 1519301737) ^ 965) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 637485580 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 1519301737) ^ 3863 = 1088194699 := by
        calc
          (5 : ZMod 1519301737) ^ 3863 = (5 : ZMod 1519301737) ^ (1931 + 1931 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1931 * (5 : ZMod 1519301737) ^ 1931) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1088194699 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 1519301737) ^ 7727 = 557714255 := by
        calc
          (5 : ZMod 1519301737) ^ 7727 = (5 : ZMod 1519301737) ^ (3863 + 3863 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 3863 * (5 : ZMod 1519301737) ^ 3863) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 557714255 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 1519301737) ^ 15455 = 968390144 := by
        calc
          (5 : ZMod 1519301737) ^ 15455 = (5 : ZMod 1519301737) ^ (7727 + 7727 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 7727 * (5 : ZMod 1519301737) ^ 7727) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 968390144 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 1519301737) ^ 30910 = 1374283463 := by
        calc
          (5 : ZMod 1519301737) ^ 30910 = (5 : ZMod 1519301737) ^ (15455 + 15455) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 15455 * (5 : ZMod 1519301737) ^ 15455 := by rw [pow_add]
          _ = 1374283463 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 1519301737) ^ 61820 = 567642642 := by
        calc
          (5 : ZMod 1519301737) ^ 61820 = (5 : ZMod 1519301737) ^ (30910 + 30910) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 30910 * (5 : ZMod 1519301737) ^ 30910 := by rw [pow_add]
          _ = 567642642 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 1519301737) ^ 123641 = 1389083032 := by
        calc
          (5 : ZMod 1519301737) ^ 123641 = (5 : ZMod 1519301737) ^ (61820 + 61820 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 61820 * (5 : ZMod 1519301737) ^ 61820) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1389083032 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 1519301737) ^ 247282 = 1157539132 := by
        calc
          (5 : ZMod 1519301737) ^ 247282 = (5 : ZMod 1519301737) ^ (123641 + 123641) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 123641 * (5 : ZMod 1519301737) ^ 123641 := by rw [pow_add]
          _ = 1157539132 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 1519301737) ^ 494564 = 215442758 := by
        calc
          (5 : ZMod 1519301737) ^ 494564 = (5 : ZMod 1519301737) ^ (247282 + 247282) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 247282 * (5 : ZMod 1519301737) ^ 247282 := by rw [pow_add]
          _ = 215442758 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 1519301737) ^ 989128 = 808952627 := by
        calc
          (5 : ZMod 1519301737) ^ 989128 = (5 : ZMod 1519301737) ^ (494564 + 494564) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 494564 * (5 : ZMod 1519301737) ^ 494564 := by rw [pow_add]
          _ = 808952627 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 1519301737) ^ 1978257 = 1135292028 := by
        calc
          (5 : ZMod 1519301737) ^ 1978257 = (5 : ZMod 1519301737) ^ (989128 + 989128 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 989128 * (5 : ZMod 1519301737) ^ 989128) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1135292028 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 1519301737) ^ 3956514 = 1146311678 := by
        calc
          (5 : ZMod 1519301737) ^ 3956514 = (5 : ZMod 1519301737) ^ (1978257 + 1978257) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1978257 * (5 : ZMod 1519301737) ^ 1978257 := by rw [pow_add]
          _ = 1146311678 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 1519301737) ^ 7913029 = 425575176 := by
        calc
          (5 : ZMod 1519301737) ^ 7913029 = (5 : ZMod 1519301737) ^ (3956514 + 3956514 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 3956514 * (5 : ZMod 1519301737) ^ 3956514) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 425575176 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 1519301737) ^ 15826059 = 1183093621 := by
        calc
          (5 : ZMod 1519301737) ^ 15826059 = (5 : ZMod 1519301737) ^ (7913029 + 7913029 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 7913029 * (5 : ZMod 1519301737) ^ 7913029) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1183093621 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 1519301737) ^ 31652119 = 1327517517 := by
        calc
          (5 : ZMod 1519301737) ^ 31652119 = (5 : ZMod 1519301737) ^ (15826059 + 15826059 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 15826059 * (5 : ZMod 1519301737) ^ 15826059) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1327517517 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 1519301737) ^ 63304239 = 834626839 := by
        calc
          (5 : ZMod 1519301737) ^ 63304239 = (5 : ZMod 1519301737) ^ (31652119 + 31652119 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 31652119 * (5 : ZMod 1519301737) ^ 31652119) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 834626839 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 1519301737) ^ 126608478 = 615915754 := by
        calc
          (5 : ZMod 1519301737) ^ 126608478 = (5 : ZMod 1519301737) ^ (63304239 + 63304239) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 63304239 * (5 : ZMod 1519301737) ^ 63304239 := by rw [pow_add]
          _ = 615915754 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 1519301737) ^ 253216956 = 206713643 := by
        calc
          (5 : ZMod 1519301737) ^ 253216956 = (5 : ZMod 1519301737) ^ (126608478 + 126608478) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 126608478 * (5 : ZMod 1519301737) ^ 126608478 := by rw [pow_add]
          _ = 206713643 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 1519301737) ^ 506433912 = 206713642 := by
        calc
          (5 : ZMod 1519301737) ^ 506433912 = (5 : ZMod 1519301737) ^ (253216956 + 253216956) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 253216956 * (5 : ZMod 1519301737) ^ 253216956 := by rw [pow_add]
          _ = 206713642 := by rw [factor_1_27]; decide
      change (5 : ZMod 1519301737) ^ 506433912 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (5 : ZMod 1519301737) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 1519301737) ^ 2 = 25 := by
        calc
          (5 : ZMod 1519301737) ^ 2 = (5 : ZMod 1519301737) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1 * (5 : ZMod 1519301737) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 1519301737) ^ 5 = 3125 := by
        calc
          (5 : ZMod 1519301737) ^ 5 = (5 : ZMod 1519301737) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 2 * (5 : ZMod 1519301737) ^ 2) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 1519301737) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 1519301737) ^ 10 = (5 : ZMod 1519301737) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 5 * (5 : ZMod 1519301737) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 1519301737) ^ 20 = 861609135 := by
        calc
          (5 : ZMod 1519301737) ^ 20 = (5 : ZMod 1519301737) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 10 * (5 : ZMod 1519301737) ^ 10 := by rw [pow_add]
          _ = 861609135 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 1519301737) ^ 40 = 1358120965 := by
        calc
          (5 : ZMod 1519301737) ^ 40 = (5 : ZMod 1519301737) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 20 * (5 : ZMod 1519301737) ^ 20 := by rw [pow_add]
          _ = 1358120965 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 1519301737) ^ 81 = 797959398 := by
        calc
          (5 : ZMod 1519301737) ^ 81 = (5 : ZMod 1519301737) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 40 * (5 : ZMod 1519301737) ^ 40) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 797959398 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 1519301737) ^ 163 = 1397411786 := by
        calc
          (5 : ZMod 1519301737) ^ 163 = (5 : ZMod 1519301737) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 81 * (5 : ZMod 1519301737) ^ 81) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1397411786 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 1519301737) ^ 326 = 1146065358 := by
        calc
          (5 : ZMod 1519301737) ^ 326 = (5 : ZMod 1519301737) ^ (163 + 163) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 163 * (5 : ZMod 1519301737) ^ 163 := by rw [pow_add]
          _ = 1146065358 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 1519301737) ^ 653 = 1457775147 := by
        calc
          (5 : ZMod 1519301737) ^ 653 = (5 : ZMod 1519301737) ^ (326 + 326 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 326 * (5 : ZMod 1519301737) ^ 326) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1457775147 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 1519301737) ^ 1306 = 202385897 := by
        calc
          (5 : ZMod 1519301737) ^ 1306 = (5 : ZMod 1519301737) ^ (653 + 653) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 653 * (5 : ZMod 1519301737) ^ 653 := by rw [pow_add]
          _ = 202385897 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 1519301737) ^ 2612 = 86244590 := by
        calc
          (5 : ZMod 1519301737) ^ 2612 = (5 : ZMod 1519301737) ^ (1306 + 1306) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1306 * (5 : ZMod 1519301737) ^ 1306 := by rw [pow_add]
          _ = 86244590 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 1519301737) ^ 5224 = 228841665 := by
        calc
          (5 : ZMod 1519301737) ^ 5224 = (5 : ZMod 1519301737) ^ (2612 + 2612) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 2612 * (5 : ZMod 1519301737) ^ 2612 := by rw [pow_add]
          _ = 228841665 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 1519301737) ^ 10448 = 1446968362 := by
        calc
          (5 : ZMod 1519301737) ^ 10448 = (5 : ZMod 1519301737) ^ (5224 + 5224) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 5224 * (5 : ZMod 1519301737) ^ 5224 := by rw [pow_add]
          _ = 1446968362 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 1519301737) ^ 20897 = 1040061048 := by
        calc
          (5 : ZMod 1519301737) ^ 20897 = (5 : ZMod 1519301737) ^ (10448 + 10448 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 10448 * (5 : ZMod 1519301737) ^ 10448) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1040061048 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 1519301737) ^ 41794 = 736483899 := by
        calc
          (5 : ZMod 1519301737) ^ 41794 = (5 : ZMod 1519301737) ^ (20897 + 20897) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 20897 * (5 : ZMod 1519301737) ^ 20897 := by rw [pow_add]
          _ = 736483899 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 1519301737) ^ 83588 = 1083677613 := by
        calc
          (5 : ZMod 1519301737) ^ 83588 = (5 : ZMod 1519301737) ^ (41794 + 41794) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 41794 * (5 : ZMod 1519301737) ^ 41794 := by rw [pow_add]
          _ = 1083677613 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 1519301737) ^ 167176 = 27989324 := by
        calc
          (5 : ZMod 1519301737) ^ 167176 = (5 : ZMod 1519301737) ^ (83588 + 83588) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 83588 * (5 : ZMod 1519301737) ^ 83588 := by rw [pow_add]
          _ = 27989324 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 1519301737) ^ 334353 = 727112275 := by
        calc
          (5 : ZMod 1519301737) ^ 334353 = (5 : ZMod 1519301737) ^ (167176 + 167176 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 167176 * (5 : ZMod 1519301737) ^ 167176) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 727112275 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 1519301737) ^ 668706 = 847066144 := by
        calc
          (5 : ZMod 1519301737) ^ 668706 = (5 : ZMod 1519301737) ^ (334353 + 334353) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 334353 * (5 : ZMod 1519301737) ^ 334353 := by rw [pow_add]
          _ = 847066144 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 1519301737) ^ 1337413 = 657287935 := by
        calc
          (5 : ZMod 1519301737) ^ 1337413 = (5 : ZMod 1519301737) ^ (668706 + 668706 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 668706 * (5 : ZMod 1519301737) ^ 668706) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 657287935 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 1519301737) ^ 2674827 = 1349453492 := by
        calc
          (5 : ZMod 1519301737) ^ 2674827 = (5 : ZMod 1519301737) ^ (1337413 + 1337413 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1337413 * (5 : ZMod 1519301737) ^ 1337413) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1349453492 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 1519301737) ^ 5349654 = 912510875 := by
        calc
          (5 : ZMod 1519301737) ^ 5349654 = (5 : ZMod 1519301737) ^ (2674827 + 2674827) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 2674827 * (5 : ZMod 1519301737) ^ 2674827 := by rw [pow_add]
          _ = 912510875 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 1519301737) ^ 10699308 = 1139472784 := by
        calc
          (5 : ZMod 1519301737) ^ 10699308 = (5 : ZMod 1519301737) ^ (5349654 + 5349654) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 5349654 * (5 : ZMod 1519301737) ^ 5349654 := by rw [pow_add]
          _ = 1139472784 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 1519301737) ^ 21398616 = 1436726980 := by
        calc
          (5 : ZMod 1519301737) ^ 21398616 = (5 : ZMod 1519301737) ^ (10699308 + 10699308) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 10699308 * (5 : ZMod 1519301737) ^ 10699308 := by rw [pow_add]
          _ = 1436726980 := by rw [factor_2_23]; decide
      change (5 : ZMod 1519301737) ^ 21398616 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (5 : ZMod 1519301737) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 1519301737) ^ 3 = 125 := by
        calc
          (5 : ZMod 1519301737) ^ 3 = (5 : ZMod 1519301737) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1 * (5 : ZMod 1519301737) ^ 1) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 1519301737) ^ 6 = 15625 := by
        calc
          (5 : ZMod 1519301737) ^ 6 = (5 : ZMod 1519301737) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 3 * (5 : ZMod 1519301737) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 1519301737) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 1519301737) ^ 13 = (5 : ZMod 1519301737) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 6 * (5 : ZMod 1519301737) ^ 6) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 1519301737) ^ 26 = 110042818 := by
        calc
          (5 : ZMod 1519301737) ^ 26 = (5 : ZMod 1519301737) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 13 * (5 : ZMod 1519301737) ^ 13 := by rw [pow_add]
          _ = 110042818 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 1519301737) ^ 52 = 499020642 := by
        calc
          (5 : ZMod 1519301737) ^ 52 = (5 : ZMod 1519301737) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 26 * (5 : ZMod 1519301737) ^ 26 := by rw [pow_add]
          _ = 499020642 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 1519301737) ^ 105 = 1128965060 := by
        calc
          (5 : ZMod 1519301737) ^ 105 = (5 : ZMod 1519301737) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 52 * (5 : ZMod 1519301737) ^ 52) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1128965060 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 1519301737) ^ 211 = 379978249 := by
        calc
          (5 : ZMod 1519301737) ^ 211 = (5 : ZMod 1519301737) ^ (105 + 105 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 105 * (5 : ZMod 1519301737) ^ 105) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 379978249 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 1519301737) ^ 422 = 467865404 := by
        calc
          (5 : ZMod 1519301737) ^ 422 = (5 : ZMod 1519301737) ^ (211 + 211) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 211 * (5 : ZMod 1519301737) ^ 211 := by rw [pow_add]
          _ = 467865404 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 1519301737) ^ 844 = 73605155 := by
        calc
          (5 : ZMod 1519301737) ^ 844 = (5 : ZMod 1519301737) ^ (422 + 422) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 422 * (5 : ZMod 1519301737) ^ 422 := by rw [pow_add]
          _ = 73605155 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 1519301737) ^ 1689 = 306595867 := by
        calc
          (5 : ZMod 1519301737) ^ 1689 = (5 : ZMod 1519301737) ^ (844 + 844 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 844 * (5 : ZMod 1519301737) ^ 844) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 306595867 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 1519301737) ^ 3379 = 405113864 := by
        calc
          (5 : ZMod 1519301737) ^ 3379 = (5 : ZMod 1519301737) ^ (1689 + 1689 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1689 * (5 : ZMod 1519301737) ^ 1689) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 405113864 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 1519301737) ^ 6759 = 1245282301 := by
        calc
          (5 : ZMod 1519301737) ^ 6759 = (5 : ZMod 1519301737) ^ (3379 + 3379 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 3379 * (5 : ZMod 1519301737) ^ 3379) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1245282301 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 1519301737) ^ 13518 = 411263704 := by
        calc
          (5 : ZMod 1519301737) ^ 13518 = (5 : ZMod 1519301737) ^ (6759 + 6759) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 6759 * (5 : ZMod 1519301737) ^ 6759 := by rw [pow_add]
          _ = 411263704 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 1519301737) ^ 27037 = 665108423 := by
        calc
          (5 : ZMod 1519301737) ^ 27037 = (5 : ZMod 1519301737) ^ (13518 + 13518 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 13518 * (5 : ZMod 1519301737) ^ 13518) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 665108423 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 1519301737) ^ 54075 = 1460955644 := by
        calc
          (5 : ZMod 1519301737) ^ 54075 = (5 : ZMod 1519301737) ^ (27037 + 27037 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 27037 * (5 : ZMod 1519301737) ^ 27037) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1460955644 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 1519301737) ^ 108150 = 590906963 := by
        calc
          (5 : ZMod 1519301737) ^ 108150 = (5 : ZMod 1519301737) ^ (54075 + 54075) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 54075 * (5 : ZMod 1519301737) ^ 54075 := by rw [pow_add]
          _ = 590906963 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 1519301737) ^ 216301 = 293784872 := by
        calc
          (5 : ZMod 1519301737) ^ 216301 = (5 : ZMod 1519301737) ^ (108150 + 108150 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 108150 * (5 : ZMod 1519301737) ^ 108150) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 293784872 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 1519301737) ^ 432603 = 1013455423 := by
        calc
          (5 : ZMod 1519301737) ^ 432603 = (5 : ZMod 1519301737) ^ (216301 + 216301 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 216301 * (5 : ZMod 1519301737) ^ 216301) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1013455423 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 1519301737) ^ 865206 = 221495733 := by
        calc
          (5 : ZMod 1519301737) ^ 865206 = (5 : ZMod 1519301737) ^ (432603 + 432603) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 432603 * (5 : ZMod 1519301737) ^ 432603 := by rw [pow_add]
          _ = 221495733 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 1519301737) ^ 1730412 = 897269807 := by
        calc
          (5 : ZMod 1519301737) ^ 1730412 = (5 : ZMod 1519301737) ^ (865206 + 865206) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 865206 * (5 : ZMod 1519301737) ^ 865206 := by rw [pow_add]
          _ = 897269807 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 1519301737) ^ 3460824 = 584535836 := by
        calc
          (5 : ZMod 1519301737) ^ 3460824 = (5 : ZMod 1519301737) ^ (1730412 + 1730412) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1730412 * (5 : ZMod 1519301737) ^ 1730412 := by rw [pow_add]
          _ = 584535836 := by rw [factor_3_20]; decide
      change (5 : ZMod 1519301737) ^ 3460824 ≠ 1
      rw [factor_3_21]
      decide
    ·
      have factor_4_0 : (5 : ZMod 1519301737) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 1519301737) ^ 2 = 25 := by
        calc
          (5 : ZMod 1519301737) ^ 2 = (5 : ZMod 1519301737) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1 * (5 : ZMod 1519301737) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 1519301737) ^ 4 = 625 := by
        calc
          (5 : ZMod 1519301737) ^ 4 = (5 : ZMod 1519301737) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 2 * (5 : ZMod 1519301737) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 1519301737) ^ 8 = 390625 := by
        calc
          (5 : ZMod 1519301737) ^ 8 = (5 : ZMod 1519301737) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 4 * (5 : ZMod 1519301737) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 1519301737) ^ 17 = 249981151 := by
        calc
          (5 : ZMod 1519301737) ^ 17 = (5 : ZMod 1519301737) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 8 * (5 : ZMod 1519301737) ^ 8) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 249981151 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 1519301737) ^ 34 = 1391038046 := by
        calc
          (5 : ZMod 1519301737) ^ 34 = (5 : ZMod 1519301737) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 17 * (5 : ZMod 1519301737) ^ 17 := by rw [pow_add]
          _ = 1391038046 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 1519301737) ^ 68 = 924650895 := by
        calc
          (5 : ZMod 1519301737) ^ 68 = (5 : ZMod 1519301737) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 34 * (5 : ZMod 1519301737) ^ 34 := by rw [pow_add]
          _ = 924650895 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 1519301737) ^ 136 = 913840991 := by
        calc
          (5 : ZMod 1519301737) ^ 136 = (5 : ZMod 1519301737) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 68 * (5 : ZMod 1519301737) ^ 68 := by rw [pow_add]
          _ = 913840991 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 1519301737) ^ 273 = 1027018306 := by
        calc
          (5 : ZMod 1519301737) ^ 273 = (5 : ZMod 1519301737) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 136 * (5 : ZMod 1519301737) ^ 136) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 1027018306 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 1519301737) ^ 547 = 942232454 := by
        calc
          (5 : ZMod 1519301737) ^ 547 = (5 : ZMod 1519301737) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 273 * (5 : ZMod 1519301737) ^ 273) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 942232454 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 1519301737) ^ 1095 = 81437184 := by
        calc
          (5 : ZMod 1519301737) ^ 1095 = (5 : ZMod 1519301737) ^ (547 + 547 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 547 * (5 : ZMod 1519301737) ^ 547) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 81437184 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 1519301737) ^ 2191 = 83221775 := by
        calc
          (5 : ZMod 1519301737) ^ 2191 = (5 : ZMod 1519301737) ^ (1095 + 1095 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 1095 * (5 : ZMod 1519301737) ^ 1095) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 83221775 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 1519301737) ^ 4383 = 781356296 := by
        calc
          (5 : ZMod 1519301737) ^ 4383 = (5 : ZMod 1519301737) ^ (2191 + 2191 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 2191 * (5 : ZMod 1519301737) ^ 2191) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 781356296 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 1519301737) ^ 8766 = 369600781 := by
        calc
          (5 : ZMod 1519301737) ^ 8766 = (5 : ZMod 1519301737) ^ (4383 + 4383) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 4383 * (5 : ZMod 1519301737) ^ 4383 := by rw [pow_add]
          _ = 369600781 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 1519301737) ^ 17532 = 286603407 := by
        calc
          (5 : ZMod 1519301737) ^ 17532 = (5 : ZMod 1519301737) ^ (8766 + 8766) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 8766 * (5 : ZMod 1519301737) ^ 8766 := by rw [pow_add]
          _ = 286603407 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 1519301737) ^ 35065 = 972459109 := by
        calc
          (5 : ZMod 1519301737) ^ 35065 = (5 : ZMod 1519301737) ^ (17532 + 17532 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 17532 * (5 : ZMod 1519301737) ^ 17532) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 972459109 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 1519301737) ^ 70130 = 668384406 := by
        calc
          (5 : ZMod 1519301737) ^ 70130 = (5 : ZMod 1519301737) ^ (35065 + 35065) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 35065 * (5 : ZMod 1519301737) ^ 35065 := by rw [pow_add]
          _ = 668384406 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 1519301737) ^ 140260 = 1101542920 := by
        calc
          (5 : ZMod 1519301737) ^ 140260 = (5 : ZMod 1519301737) ^ (70130 + 70130) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 70130 * (5 : ZMod 1519301737) ^ 70130 := by rw [pow_add]
          _ = 1101542920 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 1519301737) ^ 280521 = 608383900 := by
        calc
          (5 : ZMod 1519301737) ^ 280521 = (5 : ZMod 1519301737) ^ (140260 + 140260 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = ((5 : ZMod 1519301737) ^ 140260 * (5 : ZMod 1519301737) ^ 140260) * (5 : ZMod 1519301737) := by rw [pow_succ, pow_add]
          _ = 608383900 := by rw [factor_4_17]; decide
      have factor_4_19 : (5 : ZMod 1519301737) ^ 561042 = 884479453 := by
        calc
          (5 : ZMod 1519301737) ^ 561042 = (5 : ZMod 1519301737) ^ (280521 + 280521) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 280521 * (5 : ZMod 1519301737) ^ 280521 := by rw [pow_add]
          _ = 884479453 := by rw [factor_4_18]; decide
      have factor_4_20 : (5 : ZMod 1519301737) ^ 1122084 = 772929552 := by
        calc
          (5 : ZMod 1519301737) ^ 1122084 = (5 : ZMod 1519301737) ^ (561042 + 561042) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 561042 * (5 : ZMod 1519301737) ^ 561042 := by rw [pow_add]
          _ = 772929552 := by rw [factor_4_19]; decide
      have factor_4_21 : (5 : ZMod 1519301737) ^ 2244168 = 492580203 := by
        calc
          (5 : ZMod 1519301737) ^ 2244168 = (5 : ZMod 1519301737) ^ (1122084 + 1122084) :=
            congrArg (fun n : ℕ => (5 : ZMod 1519301737) ^ n) (by norm_num)
          _ = (5 : ZMod 1519301737) ^ 1122084 * (5 : ZMod 1519301737) ^ 1122084 := by rw [pow_add]
          _ = 492580203 := by rw [factor_4_20]; decide
      change (5 : ZMod 1519301737) ^ 2244168 ≠ 1
      rw [factor_4_21]
      decide

#print axioms prime_lucas_1519301737

end TotientTailPeriodKiller
end Erdos249257
