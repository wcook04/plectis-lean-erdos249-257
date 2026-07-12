import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_73034085791 : Nat.Prime 73034085791 := by
  apply lucas_primality 73034085791 (7 : ZMod 73034085791)
  ·
      have fermat_0 : (7 : ZMod 73034085791) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 73034085791) ^ 2 = 49 := by
        calc
          (7 : ZMod 73034085791) ^ 2 = (7 : ZMod 73034085791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1 * (7 : ZMod 73034085791) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 73034085791) ^ 4 = 2401 := by
        calc
          (7 : ZMod 73034085791) ^ 4 = (7 : ZMod 73034085791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 2 * (7 : ZMod 73034085791) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 73034085791) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 73034085791) ^ 8 = (7 : ZMod 73034085791) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 4 * (7 : ZMod 73034085791) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 73034085791) ^ 17 = 16950742872 := by
        calc
          (7 : ZMod 73034085791) ^ 17 = (7 : ZMod 73034085791) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 8 * (7 : ZMod 73034085791) ^ 8) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 16950742872 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 73034085791) ^ 34 = 47517948266 := by
        calc
          (7 : ZMod 73034085791) ^ 34 = (7 : ZMod 73034085791) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 17 * (7 : ZMod 73034085791) ^ 17 := by rw [pow_add]
          _ = 47517948266 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 73034085791) ^ 68 = 6040444855 := by
        calc
          (7 : ZMod 73034085791) ^ 68 = (7 : ZMod 73034085791) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 34 * (7 : ZMod 73034085791) ^ 34 := by rw [pow_add]
          _ = 6040444855 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 73034085791) ^ 136 = 14256983635 := by
        calc
          (7 : ZMod 73034085791) ^ 136 = (7 : ZMod 73034085791) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 68 * (7 : ZMod 73034085791) ^ 68 := by rw [pow_add]
          _ = 14256983635 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 73034085791) ^ 272 = 10550473959 := by
        calc
          (7 : ZMod 73034085791) ^ 272 = (7 : ZMod 73034085791) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 136 * (7 : ZMod 73034085791) ^ 136 := by rw [pow_add]
          _ = 10550473959 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 73034085791) ^ 544 = 42823034388 := by
        calc
          (7 : ZMod 73034085791) ^ 544 = (7 : ZMod 73034085791) ^ (272 + 272) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 272 * (7 : ZMod 73034085791) ^ 272 := by rw [pow_add]
          _ = 42823034388 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 73034085791) ^ 1088 = 22081835737 := by
        calc
          (7 : ZMod 73034085791) ^ 1088 = (7 : ZMod 73034085791) ^ (544 + 544) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 544 * (7 : ZMod 73034085791) ^ 544 := by rw [pow_add]
          _ = 22081835737 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 73034085791) ^ 2176 = 20109355182 := by
        calc
          (7 : ZMod 73034085791) ^ 2176 = (7 : ZMod 73034085791) ^ (1088 + 1088) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1088 * (7 : ZMod 73034085791) ^ 1088 := by rw [pow_add]
          _ = 20109355182 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 73034085791) ^ 4353 = 31374714768 := by
        calc
          (7 : ZMod 73034085791) ^ 4353 = (7 : ZMod 73034085791) ^ (2176 + 2176 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 2176 * (7 : ZMod 73034085791) ^ 2176) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 31374714768 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 73034085791) ^ 8706 = 17124459041 := by
        calc
          (7 : ZMod 73034085791) ^ 8706 = (7 : ZMod 73034085791) ^ (4353 + 4353) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 4353 * (7 : ZMod 73034085791) ^ 4353 := by rw [pow_add]
          _ = 17124459041 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 73034085791) ^ 17412 = 51976200071 := by
        calc
          (7 : ZMod 73034085791) ^ 17412 = (7 : ZMod 73034085791) ^ (8706 + 8706) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 8706 * (7 : ZMod 73034085791) ^ 8706 := by rw [pow_add]
          _ = 51976200071 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 73034085791) ^ 34825 = 11057378185 := by
        calc
          (7 : ZMod 73034085791) ^ 34825 = (7 : ZMod 73034085791) ^ (17412 + 17412 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 17412 * (7 : ZMod 73034085791) ^ 17412) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 11057378185 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 73034085791) ^ 69650 = 20768639914 := by
        calc
          (7 : ZMod 73034085791) ^ 69650 = (7 : ZMod 73034085791) ^ (34825 + 34825) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 34825 * (7 : ZMod 73034085791) ^ 34825 := by rw [pow_add]
          _ = 20768639914 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 73034085791) ^ 139301 = 31707293327 := by
        calc
          (7 : ZMod 73034085791) ^ 139301 = (7 : ZMod 73034085791) ^ (69650 + 69650 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 69650 * (7 : ZMod 73034085791) ^ 69650) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 31707293327 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 73034085791) ^ 278602 = 13325770415 := by
        calc
          (7 : ZMod 73034085791) ^ 278602 = (7 : ZMod 73034085791) ^ (139301 + 139301) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 139301 * (7 : ZMod 73034085791) ^ 139301 := by rw [pow_add]
          _ = 13325770415 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 73034085791) ^ 557205 = 30904729020 := by
        calc
          (7 : ZMod 73034085791) ^ 557205 = (7 : ZMod 73034085791) ^ (278602 + 278602 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 278602 * (7 : ZMod 73034085791) ^ 278602) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 30904729020 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 73034085791) ^ 1114411 = 54153236858 := by
        calc
          (7 : ZMod 73034085791) ^ 1114411 = (7 : ZMod 73034085791) ^ (557205 + 557205 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 557205 * (7 : ZMod 73034085791) ^ 557205) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 54153236858 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 73034085791) ^ 2228823 = 32066727883 := by
        calc
          (7 : ZMod 73034085791) ^ 2228823 = (7 : ZMod 73034085791) ^ (1114411 + 1114411 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 1114411 * (7 : ZMod 73034085791) ^ 1114411) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 32066727883 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 73034085791) ^ 4457646 = 24125614585 := by
        calc
          (7 : ZMod 73034085791) ^ 4457646 = (7 : ZMod 73034085791) ^ (2228823 + 2228823) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 2228823 * (7 : ZMod 73034085791) ^ 2228823 := by rw [pow_add]
          _ = 24125614585 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 73034085791) ^ 8915293 = 18616953576 := by
        calc
          (7 : ZMod 73034085791) ^ 8915293 = (7 : ZMod 73034085791) ^ (4457646 + 4457646 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 4457646 * (7 : ZMod 73034085791) ^ 4457646) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 18616953576 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 73034085791) ^ 17830587 = 17862037594 := by
        calc
          (7 : ZMod 73034085791) ^ 17830587 = (7 : ZMod 73034085791) ^ (8915293 + 8915293 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 8915293 * (7 : ZMod 73034085791) ^ 8915293) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 17862037594 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 73034085791) ^ 35661174 = 8183503859 := by
        calc
          (7 : ZMod 73034085791) ^ 35661174 = (7 : ZMod 73034085791) ^ (17830587 + 17830587) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 17830587 * (7 : ZMod 73034085791) ^ 17830587 := by rw [pow_add]
          _ = 8183503859 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 73034085791) ^ 71322349 = 12345809899 := by
        calc
          (7 : ZMod 73034085791) ^ 71322349 = (7 : ZMod 73034085791) ^ (35661174 + 35661174 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 35661174 * (7 : ZMod 73034085791) ^ 35661174) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 12345809899 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 73034085791) ^ 142644698 = 66256547933 := by
        calc
          (7 : ZMod 73034085791) ^ 142644698 = (7 : ZMod 73034085791) ^ (71322349 + 71322349) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 71322349 * (7 : ZMod 73034085791) ^ 71322349 := by rw [pow_add]
          _ = 66256547933 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 73034085791) ^ 285289397 = 38445747543 := by
        calc
          (7 : ZMod 73034085791) ^ 285289397 = (7 : ZMod 73034085791) ^ (142644698 + 142644698 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 142644698 * (7 : ZMod 73034085791) ^ 142644698) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 38445747543 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 73034085791) ^ 570578795 = 35964422499 := by
        calc
          (7 : ZMod 73034085791) ^ 570578795 = (7 : ZMod 73034085791) ^ (285289397 + 285289397 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 285289397 * (7 : ZMod 73034085791) ^ 285289397) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 35964422499 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 73034085791) ^ 1141157590 = 66446532218 := by
        calc
          (7 : ZMod 73034085791) ^ 1141157590 = (7 : ZMod 73034085791) ^ (570578795 + 570578795) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 570578795 * (7 : ZMod 73034085791) ^ 570578795 := by rw [pow_add]
          _ = 66446532218 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 73034085791) ^ 2282315180 = 29983822318 := by
        calc
          (7 : ZMod 73034085791) ^ 2282315180 = (7 : ZMod 73034085791) ^ (1141157590 + 1141157590) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1141157590 * (7 : ZMod 73034085791) ^ 1141157590 := by rw [pow_add]
          _ = 29983822318 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 73034085791) ^ 4564630361 = 21417443310 := by
        calc
          (7 : ZMod 73034085791) ^ 4564630361 = (7 : ZMod 73034085791) ^ (2282315180 + 2282315180 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 2282315180 * (7 : ZMod 73034085791) ^ 2282315180) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 21417443310 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 73034085791) ^ 9129260723 = 4178384692 := by
        calc
          (7 : ZMod 73034085791) ^ 9129260723 = (7 : ZMod 73034085791) ^ (4564630361 + 4564630361 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 4564630361 * (7 : ZMod 73034085791) ^ 4564630361) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 4178384692 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 73034085791) ^ 18258521447 = 28933955673 := by
        calc
          (7 : ZMod 73034085791) ^ 18258521447 = (7 : ZMod 73034085791) ^ (9129260723 + 9129260723 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 9129260723 * (7 : ZMod 73034085791) ^ 9129260723) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 28933955673 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 73034085791) ^ 36517042895 = 73034085790 := by
        calc
          (7 : ZMod 73034085791) ^ 36517042895 = (7 : ZMod 73034085791) ^ (18258521447 + 18258521447 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 18258521447 * (7 : ZMod 73034085791) ^ 18258521447) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 73034085790 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 73034085791) ^ 73034085790 = 1 := by
        calc
          (7 : ZMod 73034085791) ^ 73034085790 = (7 : ZMod 73034085791) ^ (36517042895 + 36517042895) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 36517042895 * (7 : ZMod 73034085791) ^ 36517042895 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (34141, 1), (213919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (34141, 1), (213919, 1)] : List FactorBlock).map factorBlockValue).prod = 73034085791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 73034085791) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 73034085791) ^ 2 = 49 := by
        calc
          (7 : ZMod 73034085791) ^ 2 = (7 : ZMod 73034085791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1 * (7 : ZMod 73034085791) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 73034085791) ^ 4 = 2401 := by
        calc
          (7 : ZMod 73034085791) ^ 4 = (7 : ZMod 73034085791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 2 * (7 : ZMod 73034085791) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 73034085791) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 73034085791) ^ 8 = (7 : ZMod 73034085791) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 4 * (7 : ZMod 73034085791) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 73034085791) ^ 17 = 16950742872 := by
        calc
          (7 : ZMod 73034085791) ^ 17 = (7 : ZMod 73034085791) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 8 * (7 : ZMod 73034085791) ^ 8) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 16950742872 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 73034085791) ^ 34 = 47517948266 := by
        calc
          (7 : ZMod 73034085791) ^ 34 = (7 : ZMod 73034085791) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 17 * (7 : ZMod 73034085791) ^ 17 := by rw [pow_add]
          _ = 47517948266 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 73034085791) ^ 68 = 6040444855 := by
        calc
          (7 : ZMod 73034085791) ^ 68 = (7 : ZMod 73034085791) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 34 * (7 : ZMod 73034085791) ^ 34 := by rw [pow_add]
          _ = 6040444855 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 73034085791) ^ 136 = 14256983635 := by
        calc
          (7 : ZMod 73034085791) ^ 136 = (7 : ZMod 73034085791) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 68 * (7 : ZMod 73034085791) ^ 68 := by rw [pow_add]
          _ = 14256983635 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 73034085791) ^ 272 = 10550473959 := by
        calc
          (7 : ZMod 73034085791) ^ 272 = (7 : ZMod 73034085791) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 136 * (7 : ZMod 73034085791) ^ 136 := by rw [pow_add]
          _ = 10550473959 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 73034085791) ^ 544 = 42823034388 := by
        calc
          (7 : ZMod 73034085791) ^ 544 = (7 : ZMod 73034085791) ^ (272 + 272) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 272 * (7 : ZMod 73034085791) ^ 272 := by rw [pow_add]
          _ = 42823034388 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 73034085791) ^ 1088 = 22081835737 := by
        calc
          (7 : ZMod 73034085791) ^ 1088 = (7 : ZMod 73034085791) ^ (544 + 544) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 544 * (7 : ZMod 73034085791) ^ 544 := by rw [pow_add]
          _ = 22081835737 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 73034085791) ^ 2176 = 20109355182 := by
        calc
          (7 : ZMod 73034085791) ^ 2176 = (7 : ZMod 73034085791) ^ (1088 + 1088) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1088 * (7 : ZMod 73034085791) ^ 1088 := by rw [pow_add]
          _ = 20109355182 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 73034085791) ^ 4353 = 31374714768 := by
        calc
          (7 : ZMod 73034085791) ^ 4353 = (7 : ZMod 73034085791) ^ (2176 + 2176 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 2176 * (7 : ZMod 73034085791) ^ 2176) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 31374714768 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 73034085791) ^ 8706 = 17124459041 := by
        calc
          (7 : ZMod 73034085791) ^ 8706 = (7 : ZMod 73034085791) ^ (4353 + 4353) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 4353 * (7 : ZMod 73034085791) ^ 4353 := by rw [pow_add]
          _ = 17124459041 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 73034085791) ^ 17412 = 51976200071 := by
        calc
          (7 : ZMod 73034085791) ^ 17412 = (7 : ZMod 73034085791) ^ (8706 + 8706) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 8706 * (7 : ZMod 73034085791) ^ 8706 := by rw [pow_add]
          _ = 51976200071 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 73034085791) ^ 34825 = 11057378185 := by
        calc
          (7 : ZMod 73034085791) ^ 34825 = (7 : ZMod 73034085791) ^ (17412 + 17412 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 17412 * (7 : ZMod 73034085791) ^ 17412) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 11057378185 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 73034085791) ^ 69650 = 20768639914 := by
        calc
          (7 : ZMod 73034085791) ^ 69650 = (7 : ZMod 73034085791) ^ (34825 + 34825) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 34825 * (7 : ZMod 73034085791) ^ 34825 := by rw [pow_add]
          _ = 20768639914 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 73034085791) ^ 139301 = 31707293327 := by
        calc
          (7 : ZMod 73034085791) ^ 139301 = (7 : ZMod 73034085791) ^ (69650 + 69650 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 69650 * (7 : ZMod 73034085791) ^ 69650) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 31707293327 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 73034085791) ^ 278602 = 13325770415 := by
        calc
          (7 : ZMod 73034085791) ^ 278602 = (7 : ZMod 73034085791) ^ (139301 + 139301) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 139301 * (7 : ZMod 73034085791) ^ 139301 := by rw [pow_add]
          _ = 13325770415 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 73034085791) ^ 557205 = 30904729020 := by
        calc
          (7 : ZMod 73034085791) ^ 557205 = (7 : ZMod 73034085791) ^ (278602 + 278602 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 278602 * (7 : ZMod 73034085791) ^ 278602) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 30904729020 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 73034085791) ^ 1114411 = 54153236858 := by
        calc
          (7 : ZMod 73034085791) ^ 1114411 = (7 : ZMod 73034085791) ^ (557205 + 557205 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 557205 * (7 : ZMod 73034085791) ^ 557205) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 54153236858 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 73034085791) ^ 2228823 = 32066727883 := by
        calc
          (7 : ZMod 73034085791) ^ 2228823 = (7 : ZMod 73034085791) ^ (1114411 + 1114411 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 1114411 * (7 : ZMod 73034085791) ^ 1114411) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 32066727883 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 73034085791) ^ 4457646 = 24125614585 := by
        calc
          (7 : ZMod 73034085791) ^ 4457646 = (7 : ZMod 73034085791) ^ (2228823 + 2228823) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 2228823 * (7 : ZMod 73034085791) ^ 2228823 := by rw [pow_add]
          _ = 24125614585 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 73034085791) ^ 8915293 = 18616953576 := by
        calc
          (7 : ZMod 73034085791) ^ 8915293 = (7 : ZMod 73034085791) ^ (4457646 + 4457646 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 4457646 * (7 : ZMod 73034085791) ^ 4457646) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 18616953576 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 73034085791) ^ 17830587 = 17862037594 := by
        calc
          (7 : ZMod 73034085791) ^ 17830587 = (7 : ZMod 73034085791) ^ (8915293 + 8915293 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 8915293 * (7 : ZMod 73034085791) ^ 8915293) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 17862037594 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 73034085791) ^ 35661174 = 8183503859 := by
        calc
          (7 : ZMod 73034085791) ^ 35661174 = (7 : ZMod 73034085791) ^ (17830587 + 17830587) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 17830587 * (7 : ZMod 73034085791) ^ 17830587 := by rw [pow_add]
          _ = 8183503859 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 73034085791) ^ 71322349 = 12345809899 := by
        calc
          (7 : ZMod 73034085791) ^ 71322349 = (7 : ZMod 73034085791) ^ (35661174 + 35661174 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 35661174 * (7 : ZMod 73034085791) ^ 35661174) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 12345809899 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 73034085791) ^ 142644698 = 66256547933 := by
        calc
          (7 : ZMod 73034085791) ^ 142644698 = (7 : ZMod 73034085791) ^ (71322349 + 71322349) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 71322349 * (7 : ZMod 73034085791) ^ 71322349 := by rw [pow_add]
          _ = 66256547933 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 73034085791) ^ 285289397 = 38445747543 := by
        calc
          (7 : ZMod 73034085791) ^ 285289397 = (7 : ZMod 73034085791) ^ (142644698 + 142644698 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 142644698 * (7 : ZMod 73034085791) ^ 142644698) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 38445747543 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 73034085791) ^ 570578795 = 35964422499 := by
        calc
          (7 : ZMod 73034085791) ^ 570578795 = (7 : ZMod 73034085791) ^ (285289397 + 285289397 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 285289397 * (7 : ZMod 73034085791) ^ 285289397) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 35964422499 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 73034085791) ^ 1141157590 = 66446532218 := by
        calc
          (7 : ZMod 73034085791) ^ 1141157590 = (7 : ZMod 73034085791) ^ (570578795 + 570578795) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 570578795 * (7 : ZMod 73034085791) ^ 570578795 := by rw [pow_add]
          _ = 66446532218 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 73034085791) ^ 2282315180 = 29983822318 := by
        calc
          (7 : ZMod 73034085791) ^ 2282315180 = (7 : ZMod 73034085791) ^ (1141157590 + 1141157590) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1141157590 * (7 : ZMod 73034085791) ^ 1141157590 := by rw [pow_add]
          _ = 29983822318 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 73034085791) ^ 4564630361 = 21417443310 := by
        calc
          (7 : ZMod 73034085791) ^ 4564630361 = (7 : ZMod 73034085791) ^ (2282315180 + 2282315180 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 2282315180 * (7 : ZMod 73034085791) ^ 2282315180) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 21417443310 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 73034085791) ^ 9129260723 = 4178384692 := by
        calc
          (7 : ZMod 73034085791) ^ 9129260723 = (7 : ZMod 73034085791) ^ (4564630361 + 4564630361 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 4564630361 * (7 : ZMod 73034085791) ^ 4564630361) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 4178384692 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 73034085791) ^ 18258521447 = 28933955673 := by
        calc
          (7 : ZMod 73034085791) ^ 18258521447 = (7 : ZMod 73034085791) ^ (9129260723 + 9129260723 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 9129260723 * (7 : ZMod 73034085791) ^ 9129260723) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 28933955673 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 73034085791) ^ 36517042895 = 73034085790 := by
        calc
          (7 : ZMod 73034085791) ^ 36517042895 = (7 : ZMod 73034085791) ^ (18258521447 + 18258521447 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 18258521447 * (7 : ZMod 73034085791) ^ 18258521447) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 73034085790 := by rw [factor_0_34]; decide
      change (7 : ZMod 73034085791) ^ 36517042895 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (7 : ZMod 73034085791) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 73034085791) ^ 3 = 343 := by
        calc
          (7 : ZMod 73034085791) ^ 3 = (7 : ZMod 73034085791) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 1 * (7 : ZMod 73034085791) ^ 1) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 73034085791) ^ 6 = 117649 := by
        calc
          (7 : ZMod 73034085791) ^ 6 = (7 : ZMod 73034085791) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 3 * (7 : ZMod 73034085791) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 73034085791) ^ 13 = 23854924616 := by
        calc
          (7 : ZMod 73034085791) ^ 13 = (7 : ZMod 73034085791) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 6 * (7 : ZMod 73034085791) ^ 6) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 23854924616 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 73034085791) ^ 27 = 36423761965 := by
        calc
          (7 : ZMod 73034085791) ^ 27 = (7 : ZMod 73034085791) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 13 * (7 : ZMod 73034085791) ^ 13) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 36423761965 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 73034085791) ^ 54 = 69272327538 := by
        calc
          (7 : ZMod 73034085791) ^ 54 = (7 : ZMod 73034085791) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 27 * (7 : ZMod 73034085791) ^ 27 := by rw [pow_add]
          _ = 69272327538 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 73034085791) ^ 108 = 35188095850 := by
        calc
          (7 : ZMod 73034085791) ^ 108 = (7 : ZMod 73034085791) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 54 * (7 : ZMod 73034085791) ^ 54 := by rw [pow_add]
          _ = 35188095850 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 73034085791) ^ 217 = 4480357404 := by
        calc
          (7 : ZMod 73034085791) ^ 217 = (7 : ZMod 73034085791) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 108 * (7 : ZMod 73034085791) ^ 108) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 4480357404 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 73034085791) ^ 435 = 32380046018 := by
        calc
          (7 : ZMod 73034085791) ^ 435 = (7 : ZMod 73034085791) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 217 * (7 : ZMod 73034085791) ^ 217) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 32380046018 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 73034085791) ^ 870 = 7538084907 := by
        calc
          (7 : ZMod 73034085791) ^ 870 = (7 : ZMod 73034085791) ^ (435 + 435) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 435 * (7 : ZMod 73034085791) ^ 435 := by rw [pow_add]
          _ = 7538084907 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 73034085791) ^ 1741 = 23488746873 := by
        calc
          (7 : ZMod 73034085791) ^ 1741 = (7 : ZMod 73034085791) ^ (870 + 870 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 870 * (7 : ZMod 73034085791) ^ 870) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 23488746873 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 73034085791) ^ 3482 = 64779436834 := by
        calc
          (7 : ZMod 73034085791) ^ 3482 = (7 : ZMod 73034085791) ^ (1741 + 1741) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1741 * (7 : ZMod 73034085791) ^ 1741 := by rw [pow_add]
          _ = 64779436834 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 73034085791) ^ 6965 = 22872678164 := by
        calc
          (7 : ZMod 73034085791) ^ 6965 = (7 : ZMod 73034085791) ^ (3482 + 3482 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 3482 * (7 : ZMod 73034085791) ^ 3482) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 22872678164 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 73034085791) ^ 13930 = 8003170769 := by
        calc
          (7 : ZMod 73034085791) ^ 13930 = (7 : ZMod 73034085791) ^ (6965 + 6965) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 6965 * (7 : ZMod 73034085791) ^ 6965 := by rw [pow_add]
          _ = 8003170769 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 73034085791) ^ 27860 = 7490295567 := by
        calc
          (7 : ZMod 73034085791) ^ 27860 = (7 : ZMod 73034085791) ^ (13930 + 13930) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 13930 * (7 : ZMod 73034085791) ^ 13930 := by rw [pow_add]
          _ = 7490295567 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 73034085791) ^ 55720 = 56355635809 := by
        calc
          (7 : ZMod 73034085791) ^ 55720 = (7 : ZMod 73034085791) ^ (27860 + 27860) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 27860 * (7 : ZMod 73034085791) ^ 27860 := by rw [pow_add]
          _ = 56355635809 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 73034085791) ^ 111441 = 17737496409 := by
        calc
          (7 : ZMod 73034085791) ^ 111441 = (7 : ZMod 73034085791) ^ (55720 + 55720 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 55720 * (7 : ZMod 73034085791) ^ 55720) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 17737496409 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 73034085791) ^ 222882 = 19473651587 := by
        calc
          (7 : ZMod 73034085791) ^ 222882 = (7 : ZMod 73034085791) ^ (111441 + 111441) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 111441 * (7 : ZMod 73034085791) ^ 111441 := by rw [pow_add]
          _ = 19473651587 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 73034085791) ^ 445764 = 9743624625 := by
        calc
          (7 : ZMod 73034085791) ^ 445764 = (7 : ZMod 73034085791) ^ (222882 + 222882) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 222882 * (7 : ZMod 73034085791) ^ 222882 := by rw [pow_add]
          _ = 9743624625 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 73034085791) ^ 891529 = 21404689072 := by
        calc
          (7 : ZMod 73034085791) ^ 891529 = (7 : ZMod 73034085791) ^ (445764 + 445764 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 445764 * (7 : ZMod 73034085791) ^ 445764) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 21404689072 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 73034085791) ^ 1783058 = 20693568274 := by
        calc
          (7 : ZMod 73034085791) ^ 1783058 = (7 : ZMod 73034085791) ^ (891529 + 891529) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 891529 * (7 : ZMod 73034085791) ^ 891529 := by rw [pow_add]
          _ = 20693568274 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 73034085791) ^ 3566117 = 34928864909 := by
        calc
          (7 : ZMod 73034085791) ^ 3566117 = (7 : ZMod 73034085791) ^ (1783058 + 1783058 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 1783058 * (7 : ZMod 73034085791) ^ 1783058) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 34928864909 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 73034085791) ^ 7132234 = 58274935334 := by
        calc
          (7 : ZMod 73034085791) ^ 7132234 = (7 : ZMod 73034085791) ^ (3566117 + 3566117) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 3566117 * (7 : ZMod 73034085791) ^ 3566117 := by rw [pow_add]
          _ = 58274935334 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 73034085791) ^ 14264469 = 14655926125 := by
        calc
          (7 : ZMod 73034085791) ^ 14264469 = (7 : ZMod 73034085791) ^ (7132234 + 7132234 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 7132234 * (7 : ZMod 73034085791) ^ 7132234) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 14655926125 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 73034085791) ^ 28528939 = 43388279477 := by
        calc
          (7 : ZMod 73034085791) ^ 28528939 = (7 : ZMod 73034085791) ^ (14264469 + 14264469 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 14264469 * (7 : ZMod 73034085791) ^ 14264469) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 43388279477 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 73034085791) ^ 57057879 = 44085007334 := by
        calc
          (7 : ZMod 73034085791) ^ 57057879 = (7 : ZMod 73034085791) ^ (28528939 + 28528939 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 28528939 * (7 : ZMod 73034085791) ^ 28528939) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 44085007334 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 73034085791) ^ 114115759 = 70732921562 := by
        calc
          (7 : ZMod 73034085791) ^ 114115759 = (7 : ZMod 73034085791) ^ (57057879 + 57057879 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 57057879 * (7 : ZMod 73034085791) ^ 57057879) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 70732921562 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 73034085791) ^ 228231518 = 42042773752 := by
        calc
          (7 : ZMod 73034085791) ^ 228231518 = (7 : ZMod 73034085791) ^ (114115759 + 114115759) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 114115759 * (7 : ZMod 73034085791) ^ 114115759 := by rw [pow_add]
          _ = 42042773752 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 73034085791) ^ 456463036 = 54842559488 := by
        calc
          (7 : ZMod 73034085791) ^ 456463036 = (7 : ZMod 73034085791) ^ (228231518 + 228231518) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 228231518 * (7 : ZMod 73034085791) ^ 228231518 := by rw [pow_add]
          _ = 54842559488 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 73034085791) ^ 912926072 = 7725375014 := by
        calc
          (7 : ZMod 73034085791) ^ 912926072 = (7 : ZMod 73034085791) ^ (456463036 + 456463036) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 456463036 * (7 : ZMod 73034085791) ^ 456463036 := by rw [pow_add]
          _ = 7725375014 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 73034085791) ^ 1825852144 = 23671724321 := by
        calc
          (7 : ZMod 73034085791) ^ 1825852144 = (7 : ZMod 73034085791) ^ (912926072 + 912926072) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 912926072 * (7 : ZMod 73034085791) ^ 912926072 := by rw [pow_add]
          _ = 23671724321 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 73034085791) ^ 3651704289 = 14524516395 := by
        calc
          (7 : ZMod 73034085791) ^ 3651704289 = (7 : ZMod 73034085791) ^ (1825852144 + 1825852144 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 1825852144 * (7 : ZMod 73034085791) ^ 1825852144) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 14524516395 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 73034085791) ^ 7303408579 = 72777153149 := by
        calc
          (7 : ZMod 73034085791) ^ 7303408579 = (7 : ZMod 73034085791) ^ (3651704289 + 3651704289 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 3651704289 * (7 : ZMod 73034085791) ^ 3651704289) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 72777153149 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 73034085791) ^ 14606817158 = 40923987920 := by
        calc
          (7 : ZMod 73034085791) ^ 14606817158 = (7 : ZMod 73034085791) ^ (7303408579 + 7303408579) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 7303408579 * (7 : ZMod 73034085791) ^ 7303408579 := by rw [pow_add]
          _ = 40923987920 := by rw [factor_1_32]; decide
      change (7 : ZMod 73034085791) ^ 14606817158 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (7 : ZMod 73034085791) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 73034085791) ^ 2 = 49 := by
        calc
          (7 : ZMod 73034085791) ^ 2 = (7 : ZMod 73034085791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1 * (7 : ZMod 73034085791) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 73034085791) ^ 4 = 2401 := by
        calc
          (7 : ZMod 73034085791) ^ 4 = (7 : ZMod 73034085791) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 2 * (7 : ZMod 73034085791) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 73034085791) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 73034085791) ^ 8 = (7 : ZMod 73034085791) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 4 * (7 : ZMod 73034085791) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 73034085791) ^ 16 = 2421534696 := by
        calc
          (7 : ZMod 73034085791) ^ 16 = (7 : ZMod 73034085791) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 8 * (7 : ZMod 73034085791) ^ 8 := by rw [pow_add]
          _ = 2421534696 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 73034085791) ^ 32 = 2460245593 := by
        calc
          (7 : ZMod 73034085791) ^ 32 = (7 : ZMod 73034085791) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 16 * (7 : ZMod 73034085791) ^ 16 := by rw [pow_add]
          _ = 2460245593 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 73034085791) ^ 65 = 71135350143 := by
        calc
          (7 : ZMod 73034085791) ^ 65 = (7 : ZMod 73034085791) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 32 * (7 : ZMod 73034085791) ^ 32) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 71135350143 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 73034085791) ^ 130 = 858659212 := by
        calc
          (7 : ZMod 73034085791) ^ 130 = (7 : ZMod 73034085791) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 65 * (7 : ZMod 73034085791) ^ 65 := by rw [pow_add]
          _ = 858659212 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 73034085791) ^ 261 = 65020232873 := by
        calc
          (7 : ZMod 73034085791) ^ 261 = (7 : ZMod 73034085791) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 130 * (7 : ZMod 73034085791) ^ 130) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 65020232873 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 73034085791) ^ 522 = 18609641140 := by
        calc
          (7 : ZMod 73034085791) ^ 522 = (7 : ZMod 73034085791) ^ (261 + 261) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 261 * (7 : ZMod 73034085791) ^ 261 := by rw [pow_add]
          _ = 18609641140 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 73034085791) ^ 1044 = 399039104 := by
        calc
          (7 : ZMod 73034085791) ^ 1044 = (7 : ZMod 73034085791) ^ (522 + 522) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 522 * (7 : ZMod 73034085791) ^ 522 := by rw [pow_add]
          _ = 399039104 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 73034085791) ^ 2089 = 43020068147 := by
        calc
          (7 : ZMod 73034085791) ^ 2089 = (7 : ZMod 73034085791) ^ (1044 + 1044 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 1044 * (7 : ZMod 73034085791) ^ 1044) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 43020068147 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 73034085791) ^ 4178 = 643941116 := by
        calc
          (7 : ZMod 73034085791) ^ 4178 = (7 : ZMod 73034085791) ^ (2089 + 2089) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 2089 * (7 : ZMod 73034085791) ^ 2089 := by rw [pow_add]
          _ = 643941116 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 73034085791) ^ 8356 = 9536199081 := by
        calc
          (7 : ZMod 73034085791) ^ 8356 = (7 : ZMod 73034085791) ^ (4178 + 4178) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 4178 * (7 : ZMod 73034085791) ^ 4178 := by rw [pow_add]
          _ = 9536199081 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 73034085791) ^ 16712 = 8646172543 := by
        calc
          (7 : ZMod 73034085791) ^ 16712 = (7 : ZMod 73034085791) ^ (8356 + 8356) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 8356 * (7 : ZMod 73034085791) ^ 8356 := by rw [pow_add]
          _ = 8646172543 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 73034085791) ^ 33424 = 69687033280 := by
        calc
          (7 : ZMod 73034085791) ^ 33424 = (7 : ZMod 73034085791) ^ (16712 + 16712) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 16712 * (7 : ZMod 73034085791) ^ 16712 := by rw [pow_add]
          _ = 69687033280 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 73034085791) ^ 66849 = 17524863606 := by
        calc
          (7 : ZMod 73034085791) ^ 66849 = (7 : ZMod 73034085791) ^ (33424 + 33424 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 33424 * (7 : ZMod 73034085791) ^ 33424) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 17524863606 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 73034085791) ^ 133699 = 55456338863 := by
        calc
          (7 : ZMod 73034085791) ^ 133699 = (7 : ZMod 73034085791) ^ (66849 + 66849 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 66849 * (7 : ZMod 73034085791) ^ 66849) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 55456338863 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 73034085791) ^ 267398 = 19385723191 := by
        calc
          (7 : ZMod 73034085791) ^ 267398 = (7 : ZMod 73034085791) ^ (133699 + 133699) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 133699 * (7 : ZMod 73034085791) ^ 133699 := by rw [pow_add]
          _ = 19385723191 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 73034085791) ^ 534797 = 18855666915 := by
        calc
          (7 : ZMod 73034085791) ^ 534797 = (7 : ZMod 73034085791) ^ (267398 + 267398 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 267398 * (7 : ZMod 73034085791) ^ 267398) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 18855666915 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 73034085791) ^ 1069595 = 20029144332 := by
        calc
          (7 : ZMod 73034085791) ^ 1069595 = (7 : ZMod 73034085791) ^ (534797 + 534797 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 534797 * (7 : ZMod 73034085791) ^ 534797) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 20029144332 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 73034085791) ^ 2139190 = 50508049705 := by
        calc
          (7 : ZMod 73034085791) ^ 2139190 = (7 : ZMod 73034085791) ^ (1069595 + 1069595) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1069595 * (7 : ZMod 73034085791) ^ 1069595 := by rw [pow_add]
          _ = 50508049705 := by rw [factor_2_20]; decide
      change (7 : ZMod 73034085791) ^ 2139190 ≠ 1
      rw [factor_2_21]
      decide
    ·
      have factor_3_0 : (7 : ZMod 73034085791) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 73034085791) ^ 2 = 49 := by
        calc
          (7 : ZMod 73034085791) ^ 2 = (7 : ZMod 73034085791) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 1 * (7 : ZMod 73034085791) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 73034085791) ^ 5 = 16807 := by
        calc
          (7 : ZMod 73034085791) ^ 5 = (7 : ZMod 73034085791) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 2 * (7 : ZMod 73034085791) ^ 2) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 73034085791) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 73034085791) ^ 10 = (7 : ZMod 73034085791) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 5 * (7 : ZMod 73034085791) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 73034085791) ^ 20 = 44412027607 := by
        calc
          (7 : ZMod 73034085791) ^ 20 = (7 : ZMod 73034085791) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 10 * (7 : ZMod 73034085791) ^ 10 := by rw [pow_add]
          _ = 44412027607 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 73034085791) ^ 41 = 22854378609 := by
        calc
          (7 : ZMod 73034085791) ^ 41 = (7 : ZMod 73034085791) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 20 * (7 : ZMod 73034085791) ^ 20) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 22854378609 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 73034085791) ^ 83 = 2200653986 := by
        calc
          (7 : ZMod 73034085791) ^ 83 = (7 : ZMod 73034085791) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 41 * (7 : ZMod 73034085791) ^ 41) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 2200653986 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 73034085791) ^ 166 = 7022891084 := by
        calc
          (7 : ZMod 73034085791) ^ 166 = (7 : ZMod 73034085791) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 83 * (7 : ZMod 73034085791) ^ 83 := by rw [pow_add]
          _ = 7022891084 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 73034085791) ^ 333 = 20719702509 := by
        calc
          (7 : ZMod 73034085791) ^ 333 = (7 : ZMod 73034085791) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 166 * (7 : ZMod 73034085791) ^ 166) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 20719702509 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 73034085791) ^ 666 = 19090731816 := by
        calc
          (7 : ZMod 73034085791) ^ 666 = (7 : ZMod 73034085791) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 333 * (7 : ZMod 73034085791) ^ 333 := by rw [pow_add]
          _ = 19090731816 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 73034085791) ^ 1333 = 28806562770 := by
        calc
          (7 : ZMod 73034085791) ^ 1333 = (7 : ZMod 73034085791) ^ (666 + 666 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 666 * (7 : ZMod 73034085791) ^ 666) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 28806562770 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 73034085791) ^ 2667 = 64656109005 := by
        calc
          (7 : ZMod 73034085791) ^ 2667 = (7 : ZMod 73034085791) ^ (1333 + 1333 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 1333 * (7 : ZMod 73034085791) ^ 1333) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 64656109005 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 73034085791) ^ 5334 = 57083683925 := by
        calc
          (7 : ZMod 73034085791) ^ 5334 = (7 : ZMod 73034085791) ^ (2667 + 2667) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 2667 * (7 : ZMod 73034085791) ^ 2667 := by rw [pow_add]
          _ = 57083683925 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 73034085791) ^ 10669 = 6312890693 := by
        calc
          (7 : ZMod 73034085791) ^ 10669 = (7 : ZMod 73034085791) ^ (5334 + 5334 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 5334 * (7 : ZMod 73034085791) ^ 5334) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 6312890693 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 73034085791) ^ 21338 = 66207967014 := by
        calc
          (7 : ZMod 73034085791) ^ 21338 = (7 : ZMod 73034085791) ^ (10669 + 10669) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 10669 * (7 : ZMod 73034085791) ^ 10669 := by rw [pow_add]
          _ = 66207967014 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 73034085791) ^ 42676 = 7666817314 := by
        calc
          (7 : ZMod 73034085791) ^ 42676 = (7 : ZMod 73034085791) ^ (21338 + 21338) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 21338 * (7 : ZMod 73034085791) ^ 21338 := by rw [pow_add]
          _ = 7666817314 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 73034085791) ^ 85352 = 43015976934 := by
        calc
          (7 : ZMod 73034085791) ^ 85352 = (7 : ZMod 73034085791) ^ (42676 + 42676) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 42676 * (7 : ZMod 73034085791) ^ 42676 := by rw [pow_add]
          _ = 43015976934 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 73034085791) ^ 170705 = 55190876076 := by
        calc
          (7 : ZMod 73034085791) ^ 170705 = (7 : ZMod 73034085791) ^ (85352 + 85352 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = ((7 : ZMod 73034085791) ^ 85352 * (7 : ZMod 73034085791) ^ 85352) * (7 : ZMod 73034085791) := by rw [pow_succ, pow_add]
          _ = 55190876076 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 73034085791) ^ 341410 = 6369733890 := by
        calc
          (7 : ZMod 73034085791) ^ 341410 = (7 : ZMod 73034085791) ^ (170705 + 170705) :=
            congrArg (fun n : ℕ => (7 : ZMod 73034085791) ^ n) (by norm_num)
          _ = (7 : ZMod 73034085791) ^ 170705 * (7 : ZMod 73034085791) ^ 170705 := by rw [pow_add]
          _ = 6369733890 := by rw [factor_3_17]; decide
      change (7 : ZMod 73034085791) ^ 341410 ≠ 1
      rw [factor_3_18]
      decide

#print axioms prime_lucas_73034085791

end TotientTailPeriodKiller
end Erdos249257
