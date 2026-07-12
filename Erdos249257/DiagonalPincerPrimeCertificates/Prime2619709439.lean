import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2619709439 : Nat.Prime 2619709439 := by
  apply lucas_primality 2619709439 (7 : ZMod 2619709439)
  ·
      have fermat_0 : (7 : ZMod 2619709439) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 2619709439) ^ 2 = 49 := by
        calc
          (7 : ZMod 2619709439) ^ 2 = (7 : ZMod 2619709439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 1 * (7 : ZMod 2619709439) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 2619709439) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2619709439) ^ 4 = (7 : ZMod 2619709439) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 2 * (7 : ZMod 2619709439) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 2619709439) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 2619709439) ^ 9 = (7 : ZMod 2619709439) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 4 * (7 : ZMod 2619709439) ^ 4) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 2619709439) ^ 19 = 2375849148 := by
        calc
          (7 : ZMod 2619709439) ^ 19 = (7 : ZMod 2619709439) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 9 * (7 : ZMod 2619709439) ^ 9) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2375849148 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 2619709439) ^ 39 = 1008508015 := by
        calc
          (7 : ZMod 2619709439) ^ 39 = (7 : ZMod 2619709439) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 19 * (7 : ZMod 2619709439) ^ 19) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1008508015 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 2619709439) ^ 78 = 1059720487 := by
        calc
          (7 : ZMod 2619709439) ^ 78 = (7 : ZMod 2619709439) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 39 * (7 : ZMod 2619709439) ^ 39 := by rw [pow_add]
          _ = 1059720487 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 2619709439) ^ 156 = 1379645690 := by
        calc
          (7 : ZMod 2619709439) ^ 156 = (7 : ZMod 2619709439) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 78 * (7 : ZMod 2619709439) ^ 78 := by rw [pow_add]
          _ = 1379645690 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 2619709439) ^ 312 = 1613096432 := by
        calc
          (7 : ZMod 2619709439) ^ 312 = (7 : ZMod 2619709439) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 156 * (7 : ZMod 2619709439) ^ 156 := by rw [pow_add]
          _ = 1613096432 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 2619709439) ^ 624 = 2460009441 := by
        calc
          (7 : ZMod 2619709439) ^ 624 = (7 : ZMod 2619709439) ^ (312 + 312) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 312 * (7 : ZMod 2619709439) ^ 312 := by rw [pow_add]
          _ = 2460009441 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 2619709439) ^ 1249 = 1273230522 := by
        calc
          (7 : ZMod 2619709439) ^ 1249 = (7 : ZMod 2619709439) ^ (624 + 624 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 624 * (7 : ZMod 2619709439) ^ 624) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1273230522 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 2619709439) ^ 2498 = 1969036781 := by
        calc
          (7 : ZMod 2619709439) ^ 2498 = (7 : ZMod 2619709439) ^ (1249 + 1249) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 1249 * (7 : ZMod 2619709439) ^ 1249 := by rw [pow_add]
          _ = 1969036781 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 2619709439) ^ 4996 = 458489803 := by
        calc
          (7 : ZMod 2619709439) ^ 4996 = (7 : ZMod 2619709439) ^ (2498 + 2498) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 2498 * (7 : ZMod 2619709439) ^ 2498 := by rw [pow_add]
          _ = 458489803 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 2619709439) ^ 9993 = 2043345073 := by
        calc
          (7 : ZMod 2619709439) ^ 9993 = (7 : ZMod 2619709439) ^ (4996 + 4996 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 4996 * (7 : ZMod 2619709439) ^ 4996) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2043345073 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 2619709439) ^ 19986 = 1304323380 := by
        calc
          (7 : ZMod 2619709439) ^ 19986 = (7 : ZMod 2619709439) ^ (9993 + 9993) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 9993 * (7 : ZMod 2619709439) ^ 9993 := by rw [pow_add]
          _ = 1304323380 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 2619709439) ^ 39973 = 255955895 := by
        calc
          (7 : ZMod 2619709439) ^ 39973 = (7 : ZMod 2619709439) ^ (19986 + 19986 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 19986 * (7 : ZMod 2619709439) ^ 19986) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 255955895 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 2619709439) ^ 79947 = 750773084 := by
        calc
          (7 : ZMod 2619709439) ^ 79947 = (7 : ZMod 2619709439) ^ (39973 + 39973 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 39973 * (7 : ZMod 2619709439) ^ 39973) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 750773084 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 2619709439) ^ 159894 = 1536178967 := by
        calc
          (7 : ZMod 2619709439) ^ 159894 = (7 : ZMod 2619709439) ^ (79947 + 79947) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 79947 * (7 : ZMod 2619709439) ^ 79947 := by rw [pow_add]
          _ = 1536178967 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 2619709439) ^ 319788 = 463651660 := by
        calc
          (7 : ZMod 2619709439) ^ 319788 = (7 : ZMod 2619709439) ^ (159894 + 159894) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 159894 * (7 : ZMod 2619709439) ^ 159894 := by rw [pow_add]
          _ = 463651660 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 2619709439) ^ 639577 = 50787558 := by
        calc
          (7 : ZMod 2619709439) ^ 639577 = (7 : ZMod 2619709439) ^ (319788 + 319788 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 319788 * (7 : ZMod 2619709439) ^ 319788) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 50787558 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 2619709439) ^ 1279154 = 2274835647 := by
        calc
          (7 : ZMod 2619709439) ^ 1279154 = (7 : ZMod 2619709439) ^ (639577 + 639577) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 639577 * (7 : ZMod 2619709439) ^ 639577 := by rw [pow_add]
          _ = 2274835647 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 2619709439) ^ 2558309 = 430327515 := by
        calc
          (7 : ZMod 2619709439) ^ 2558309 = (7 : ZMod 2619709439) ^ (1279154 + 1279154 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 1279154 * (7 : ZMod 2619709439) ^ 1279154) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 430327515 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 2619709439) ^ 5116619 = 599626705 := by
        calc
          (7 : ZMod 2619709439) ^ 5116619 = (7 : ZMod 2619709439) ^ (2558309 + 2558309 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 2558309 * (7 : ZMod 2619709439) ^ 2558309) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 599626705 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 2619709439) ^ 10233239 = 305979252 := by
        calc
          (7 : ZMod 2619709439) ^ 10233239 = (7 : ZMod 2619709439) ^ (5116619 + 5116619 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 5116619 * (7 : ZMod 2619709439) ^ 5116619) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 305979252 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 2619709439) ^ 20466479 = 1602692146 := by
        calc
          (7 : ZMod 2619709439) ^ 20466479 = (7 : ZMod 2619709439) ^ (10233239 + 10233239 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 10233239 * (7 : ZMod 2619709439) ^ 10233239) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1602692146 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 2619709439) ^ 40932959 = 852514822 := by
        calc
          (7 : ZMod 2619709439) ^ 40932959 = (7 : ZMod 2619709439) ^ (20466479 + 20466479 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 20466479 * (7 : ZMod 2619709439) ^ 20466479) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 852514822 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 2619709439) ^ 81865919 = 1186444009 := by
        calc
          (7 : ZMod 2619709439) ^ 81865919 = (7 : ZMod 2619709439) ^ (40932959 + 40932959 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 40932959 * (7 : ZMod 2619709439) ^ 40932959) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1186444009 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 2619709439) ^ 163731839 = 728113968 := by
        calc
          (7 : ZMod 2619709439) ^ 163731839 = (7 : ZMod 2619709439) ^ (81865919 + 81865919 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 81865919 * (7 : ZMod 2619709439) ^ 81865919) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 728113968 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 2619709439) ^ 327463679 = 1160092394 := by
        calc
          (7 : ZMod 2619709439) ^ 327463679 = (7 : ZMod 2619709439) ^ (163731839 + 163731839 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 163731839 * (7 : ZMod 2619709439) ^ 163731839) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1160092394 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 2619709439) ^ 654927359 = 1111845970 := by
        calc
          (7 : ZMod 2619709439) ^ 654927359 = (7 : ZMod 2619709439) ^ (327463679 + 327463679 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 327463679 * (7 : ZMod 2619709439) ^ 327463679) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1111845970 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 2619709439) ^ 1309854719 = 2619709438 := by
        calc
          (7 : ZMod 2619709439) ^ 1309854719 = (7 : ZMod 2619709439) ^ (654927359 + 654927359 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 654927359 * (7 : ZMod 2619709439) ^ 654927359) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2619709438 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 2619709439) ^ 2619709438 = 1 := by
        calc
          (7 : ZMod 2619709439) ^ 2619709438 = (7 : ZMod 2619709439) ^ (1309854719 + 1309854719) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 1309854719 * (7 : ZMod 2619709439) ^ 1309854719 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (479, 1), (2734561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (479, 1), (2734561, 1)] : List FactorBlock).map factorBlockValue).prod = 2619709439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 2619709439) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 2619709439) ^ 2 = 49 := by
        calc
          (7 : ZMod 2619709439) ^ 2 = (7 : ZMod 2619709439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 1 * (7 : ZMod 2619709439) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 2619709439) ^ 4 = 2401 := by
        calc
          (7 : ZMod 2619709439) ^ 4 = (7 : ZMod 2619709439) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 2 * (7 : ZMod 2619709439) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 2619709439) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 2619709439) ^ 9 = (7 : ZMod 2619709439) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 4 * (7 : ZMod 2619709439) ^ 4) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 2619709439) ^ 19 = 2375849148 := by
        calc
          (7 : ZMod 2619709439) ^ 19 = (7 : ZMod 2619709439) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 9 * (7 : ZMod 2619709439) ^ 9) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2375849148 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 2619709439) ^ 39 = 1008508015 := by
        calc
          (7 : ZMod 2619709439) ^ 39 = (7 : ZMod 2619709439) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 19 * (7 : ZMod 2619709439) ^ 19) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1008508015 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 2619709439) ^ 78 = 1059720487 := by
        calc
          (7 : ZMod 2619709439) ^ 78 = (7 : ZMod 2619709439) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 39 * (7 : ZMod 2619709439) ^ 39 := by rw [pow_add]
          _ = 1059720487 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 2619709439) ^ 156 = 1379645690 := by
        calc
          (7 : ZMod 2619709439) ^ 156 = (7 : ZMod 2619709439) ^ (78 + 78) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 78 * (7 : ZMod 2619709439) ^ 78 := by rw [pow_add]
          _ = 1379645690 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 2619709439) ^ 312 = 1613096432 := by
        calc
          (7 : ZMod 2619709439) ^ 312 = (7 : ZMod 2619709439) ^ (156 + 156) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 156 * (7 : ZMod 2619709439) ^ 156 := by rw [pow_add]
          _ = 1613096432 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 2619709439) ^ 624 = 2460009441 := by
        calc
          (7 : ZMod 2619709439) ^ 624 = (7 : ZMod 2619709439) ^ (312 + 312) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 312 * (7 : ZMod 2619709439) ^ 312 := by rw [pow_add]
          _ = 2460009441 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 2619709439) ^ 1249 = 1273230522 := by
        calc
          (7 : ZMod 2619709439) ^ 1249 = (7 : ZMod 2619709439) ^ (624 + 624 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 624 * (7 : ZMod 2619709439) ^ 624) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1273230522 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 2619709439) ^ 2498 = 1969036781 := by
        calc
          (7 : ZMod 2619709439) ^ 2498 = (7 : ZMod 2619709439) ^ (1249 + 1249) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 1249 * (7 : ZMod 2619709439) ^ 1249 := by rw [pow_add]
          _ = 1969036781 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 2619709439) ^ 4996 = 458489803 := by
        calc
          (7 : ZMod 2619709439) ^ 4996 = (7 : ZMod 2619709439) ^ (2498 + 2498) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 2498 * (7 : ZMod 2619709439) ^ 2498 := by rw [pow_add]
          _ = 458489803 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 2619709439) ^ 9993 = 2043345073 := by
        calc
          (7 : ZMod 2619709439) ^ 9993 = (7 : ZMod 2619709439) ^ (4996 + 4996 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 4996 * (7 : ZMod 2619709439) ^ 4996) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2043345073 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 2619709439) ^ 19986 = 1304323380 := by
        calc
          (7 : ZMod 2619709439) ^ 19986 = (7 : ZMod 2619709439) ^ (9993 + 9993) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 9993 * (7 : ZMod 2619709439) ^ 9993 := by rw [pow_add]
          _ = 1304323380 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 2619709439) ^ 39973 = 255955895 := by
        calc
          (7 : ZMod 2619709439) ^ 39973 = (7 : ZMod 2619709439) ^ (19986 + 19986 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 19986 * (7 : ZMod 2619709439) ^ 19986) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 255955895 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 2619709439) ^ 79947 = 750773084 := by
        calc
          (7 : ZMod 2619709439) ^ 79947 = (7 : ZMod 2619709439) ^ (39973 + 39973 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 39973 * (7 : ZMod 2619709439) ^ 39973) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 750773084 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 2619709439) ^ 159894 = 1536178967 := by
        calc
          (7 : ZMod 2619709439) ^ 159894 = (7 : ZMod 2619709439) ^ (79947 + 79947) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 79947 * (7 : ZMod 2619709439) ^ 79947 := by rw [pow_add]
          _ = 1536178967 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 2619709439) ^ 319788 = 463651660 := by
        calc
          (7 : ZMod 2619709439) ^ 319788 = (7 : ZMod 2619709439) ^ (159894 + 159894) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 159894 * (7 : ZMod 2619709439) ^ 159894 := by rw [pow_add]
          _ = 463651660 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 2619709439) ^ 639577 = 50787558 := by
        calc
          (7 : ZMod 2619709439) ^ 639577 = (7 : ZMod 2619709439) ^ (319788 + 319788 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 319788 * (7 : ZMod 2619709439) ^ 319788) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 50787558 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 2619709439) ^ 1279154 = 2274835647 := by
        calc
          (7 : ZMod 2619709439) ^ 1279154 = (7 : ZMod 2619709439) ^ (639577 + 639577) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 639577 * (7 : ZMod 2619709439) ^ 639577 := by rw [pow_add]
          _ = 2274835647 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 2619709439) ^ 2558309 = 430327515 := by
        calc
          (7 : ZMod 2619709439) ^ 2558309 = (7 : ZMod 2619709439) ^ (1279154 + 1279154 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 1279154 * (7 : ZMod 2619709439) ^ 1279154) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 430327515 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 2619709439) ^ 5116619 = 599626705 := by
        calc
          (7 : ZMod 2619709439) ^ 5116619 = (7 : ZMod 2619709439) ^ (2558309 + 2558309 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 2558309 * (7 : ZMod 2619709439) ^ 2558309) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 599626705 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 2619709439) ^ 10233239 = 305979252 := by
        calc
          (7 : ZMod 2619709439) ^ 10233239 = (7 : ZMod 2619709439) ^ (5116619 + 5116619 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 5116619 * (7 : ZMod 2619709439) ^ 5116619) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 305979252 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 2619709439) ^ 20466479 = 1602692146 := by
        calc
          (7 : ZMod 2619709439) ^ 20466479 = (7 : ZMod 2619709439) ^ (10233239 + 10233239 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 10233239 * (7 : ZMod 2619709439) ^ 10233239) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1602692146 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 2619709439) ^ 40932959 = 852514822 := by
        calc
          (7 : ZMod 2619709439) ^ 40932959 = (7 : ZMod 2619709439) ^ (20466479 + 20466479 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 20466479 * (7 : ZMod 2619709439) ^ 20466479) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 852514822 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 2619709439) ^ 81865919 = 1186444009 := by
        calc
          (7 : ZMod 2619709439) ^ 81865919 = (7 : ZMod 2619709439) ^ (40932959 + 40932959 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 40932959 * (7 : ZMod 2619709439) ^ 40932959) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1186444009 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 2619709439) ^ 163731839 = 728113968 := by
        calc
          (7 : ZMod 2619709439) ^ 163731839 = (7 : ZMod 2619709439) ^ (81865919 + 81865919 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 81865919 * (7 : ZMod 2619709439) ^ 81865919) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 728113968 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 2619709439) ^ 327463679 = 1160092394 := by
        calc
          (7 : ZMod 2619709439) ^ 327463679 = (7 : ZMod 2619709439) ^ (163731839 + 163731839 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 163731839 * (7 : ZMod 2619709439) ^ 163731839) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1160092394 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 2619709439) ^ 654927359 = 1111845970 := by
        calc
          (7 : ZMod 2619709439) ^ 654927359 = (7 : ZMod 2619709439) ^ (327463679 + 327463679 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 327463679 * (7 : ZMod 2619709439) ^ 327463679) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1111845970 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 2619709439) ^ 1309854719 = 2619709438 := by
        calc
          (7 : ZMod 2619709439) ^ 1309854719 = (7 : ZMod 2619709439) ^ (654927359 + 654927359 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 654927359 * (7 : ZMod 2619709439) ^ 654927359) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2619709438 := by rw [factor_0_29]; decide
      change (7 : ZMod 2619709439) ^ 1309854719 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (7 : ZMod 2619709439) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 2619709439) ^ 2 = 49 := by
        calc
          (7 : ZMod 2619709439) ^ 2 = (7 : ZMod 2619709439) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 1 * (7 : ZMod 2619709439) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 2619709439) ^ 5 = 16807 := by
        calc
          (7 : ZMod 2619709439) ^ 5 = (7 : ZMod 2619709439) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 2 * (7 : ZMod 2619709439) ^ 2) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 2619709439) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 2619709439) ^ 10 = (7 : ZMod 2619709439) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 5 * (7 : ZMod 2619709439) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 2619709439) ^ 20 = 912687402 := by
        calc
          (7 : ZMod 2619709439) ^ 20 = (7 : ZMod 2619709439) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 10 * (7 : ZMod 2619709439) ^ 10 := by rw [pow_add]
          _ = 912687402 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 2619709439) ^ 41 = 2262122833 := by
        calc
          (7 : ZMod 2619709439) ^ 41 = (7 : ZMod 2619709439) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 20 * (7 : ZMod 2619709439) ^ 20) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2262122833 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 2619709439) ^ 83 = 1937458687 := by
        calc
          (7 : ZMod 2619709439) ^ 83 = (7 : ZMod 2619709439) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 41 * (7 : ZMod 2619709439) ^ 41) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1937458687 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 2619709439) ^ 166 = 512143541 := by
        calc
          (7 : ZMod 2619709439) ^ 166 = (7 : ZMod 2619709439) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 83 * (7 : ZMod 2619709439) ^ 83 := by rw [pow_add]
          _ = 512143541 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 2619709439) ^ 333 = 430871431 := by
        calc
          (7 : ZMod 2619709439) ^ 333 = (7 : ZMod 2619709439) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 166 * (7 : ZMod 2619709439) ^ 166) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 430871431 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 2619709439) ^ 667 = 1439365619 := by
        calc
          (7 : ZMod 2619709439) ^ 667 = (7 : ZMod 2619709439) ^ (333 + 333 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 333 * (7 : ZMod 2619709439) ^ 333) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1439365619 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 2619709439) ^ 1335 = 605318306 := by
        calc
          (7 : ZMod 2619709439) ^ 1335 = (7 : ZMod 2619709439) ^ (667 + 667 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 667 * (7 : ZMod 2619709439) ^ 667) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 605318306 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 2619709439) ^ 2670 = 1162037508 := by
        calc
          (7 : ZMod 2619709439) ^ 2670 = (7 : ZMod 2619709439) ^ (1335 + 1335) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 1335 * (7 : ZMod 2619709439) ^ 1335 := by rw [pow_add]
          _ = 1162037508 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 2619709439) ^ 5340 = 1081315204 := by
        calc
          (7 : ZMod 2619709439) ^ 5340 = (7 : ZMod 2619709439) ^ (2670 + 2670) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 2670 * (7 : ZMod 2619709439) ^ 2670 := by rw [pow_add]
          _ = 1081315204 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 2619709439) ^ 10681 = 1325267849 := by
        calc
          (7 : ZMod 2619709439) ^ 10681 = (7 : ZMod 2619709439) ^ (5340 + 5340 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 5340 * (7 : ZMod 2619709439) ^ 5340) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1325267849 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 2619709439) ^ 21363 = 1635432856 := by
        calc
          (7 : ZMod 2619709439) ^ 21363 = (7 : ZMod 2619709439) ^ (10681 + 10681 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 10681 * (7 : ZMod 2619709439) ^ 10681) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1635432856 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 2619709439) ^ 42727 = 1600911664 := by
        calc
          (7 : ZMod 2619709439) ^ 42727 = (7 : ZMod 2619709439) ^ (21363 + 21363 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 21363 * (7 : ZMod 2619709439) ^ 21363) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 1600911664 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 2619709439) ^ 85455 = 400554607 := by
        calc
          (7 : ZMod 2619709439) ^ 85455 = (7 : ZMod 2619709439) ^ (42727 + 42727 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 42727 * (7 : ZMod 2619709439) ^ 42727) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 400554607 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 2619709439) ^ 170910 = 1244875326 := by
        calc
          (7 : ZMod 2619709439) ^ 170910 = (7 : ZMod 2619709439) ^ (85455 + 85455) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 85455 * (7 : ZMod 2619709439) ^ 85455 := by rw [pow_add]
          _ = 1244875326 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 2619709439) ^ 341820 = 306828074 := by
        calc
          (7 : ZMod 2619709439) ^ 341820 = (7 : ZMod 2619709439) ^ (170910 + 170910) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 170910 * (7 : ZMod 2619709439) ^ 170910 := by rw [pow_add]
          _ = 306828074 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 2619709439) ^ 683640 = 1050725442 := by
        calc
          (7 : ZMod 2619709439) ^ 683640 = (7 : ZMod 2619709439) ^ (341820 + 341820) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 341820 * (7 : ZMod 2619709439) ^ 341820 := by rw [pow_add]
          _ = 1050725442 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 2619709439) ^ 1367280 = 2066533289 := by
        calc
          (7 : ZMod 2619709439) ^ 1367280 = (7 : ZMod 2619709439) ^ (683640 + 683640) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 683640 * (7 : ZMod 2619709439) ^ 683640 := by rw [pow_add]
          _ = 2066533289 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 2619709439) ^ 2734561 = 593271725 := by
        calc
          (7 : ZMod 2619709439) ^ 2734561 = (7 : ZMod 2619709439) ^ (1367280 + 1367280 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 1367280 * (7 : ZMod 2619709439) ^ 1367280) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 593271725 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 2619709439) ^ 5469122 = 318430091 := by
        calc
          (7 : ZMod 2619709439) ^ 5469122 = (7 : ZMod 2619709439) ^ (2734561 + 2734561) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 2734561 * (7 : ZMod 2619709439) ^ 2734561 := by rw [pow_add]
          _ = 318430091 := by rw [factor_1_21]; decide
      change (7 : ZMod 2619709439) ^ 5469122 ≠ 1
      rw [factor_1_22]
      decide
    ·
      have factor_2_0 : (7 : ZMod 2619709439) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 2619709439) ^ 3 = 343 := by
        calc
          (7 : ZMod 2619709439) ^ 3 = (7 : ZMod 2619709439) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 1 * (7 : ZMod 2619709439) ^ 1) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 2619709439) ^ 7 = 823543 := by
        calc
          (7 : ZMod 2619709439) ^ 7 = (7 : ZMod 2619709439) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 3 * (7 : ZMod 2619709439) ^ 3) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 2619709439) ^ 14 = 2338037587 := by
        calc
          (7 : ZMod 2619709439) ^ 14 = (7 : ZMod 2619709439) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 7 * (7 : ZMod 2619709439) ^ 7 := by rw [pow_add]
          _ = 2338037587 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 2619709439) ^ 29 = 941620792 := by
        calc
          (7 : ZMod 2619709439) ^ 29 = (7 : ZMod 2619709439) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 14 * (7 : ZMod 2619709439) ^ 14) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 941620792 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 2619709439) ^ 59 = 2351095926 := by
        calc
          (7 : ZMod 2619709439) ^ 59 = (7 : ZMod 2619709439) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 29 * (7 : ZMod 2619709439) ^ 29) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 2351095926 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 2619709439) ^ 119 = 938433821 := by
        calc
          (7 : ZMod 2619709439) ^ 119 = (7 : ZMod 2619709439) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 59 * (7 : ZMod 2619709439) ^ 59) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 938433821 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 2619709439) ^ 239 = 716201046 := by
        calc
          (7 : ZMod 2619709439) ^ 239 = (7 : ZMod 2619709439) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 119 * (7 : ZMod 2619709439) ^ 119) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 716201046 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 2619709439) ^ 479 = 977039078 := by
        calc
          (7 : ZMod 2619709439) ^ 479 = (7 : ZMod 2619709439) ^ (239 + 239 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = ((7 : ZMod 2619709439) ^ 239 * (7 : ZMod 2619709439) ^ 239) * (7 : ZMod 2619709439) := by rw [pow_succ, pow_add]
          _ = 977039078 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 2619709439) ^ 958 = 1268480806 := by
        calc
          (7 : ZMod 2619709439) ^ 958 = (7 : ZMod 2619709439) ^ (479 + 479) :=
            congrArg (fun n : ℕ => (7 : ZMod 2619709439) ^ n) (by norm_num)
          _ = (7 : ZMod 2619709439) ^ 479 * (7 : ZMod 2619709439) ^ 479 := by rw [pow_add]
          _ = 1268480806 := by rw [factor_2_8]; decide
      change (7 : ZMod 2619709439) ^ 958 ≠ 1
      rw [factor_2_9]
      decide

#print axioms prime_lucas_2619709439

end TotientTailPeriodKiller
end Erdos249257
