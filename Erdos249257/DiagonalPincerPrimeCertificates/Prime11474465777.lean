import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_11474465777 : Nat.Prime 11474465777 := by
  apply lucas_primality 11474465777 (3 : ZMod 11474465777)
  ·
      have fermat_0 : (3 : ZMod 11474465777) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 11474465777) ^ 2 = 9 := by
        calc
          (3 : ZMod 11474465777) ^ 2 = (3 : ZMod 11474465777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1 * (3 : ZMod 11474465777) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 11474465777) ^ 5 = 243 := by
        calc
          (3 : ZMod 11474465777) ^ 5 = (3 : ZMod 11474465777) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 2 * (3 : ZMod 11474465777) ^ 2) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 11474465777) ^ 10 = 59049 := by
        calc
          (3 : ZMod 11474465777) ^ 10 = (3 : ZMod 11474465777) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 5 * (3 : ZMod 11474465777) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 11474465777) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 11474465777) ^ 21 = (3 : ZMod 11474465777) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 10 * (3 : ZMod 11474465777) ^ 10) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 11474465777) ^ 42 = 4809776414 := by
        calc
          (3 : ZMod 11474465777) ^ 42 = (3 : ZMod 11474465777) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 21 * (3 : ZMod 11474465777) ^ 21 := by rw [pow_add]
          _ = 4809776414 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 11474465777) ^ 85 = 559691306 := by
        calc
          (3 : ZMod 11474465777) ^ 85 = (3 : ZMod 11474465777) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 42 * (3 : ZMod 11474465777) ^ 42) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 559691306 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 11474465777) ^ 170 = 7991663511 := by
        calc
          (3 : ZMod 11474465777) ^ 170 = (3 : ZMod 11474465777) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 85 * (3 : ZMod 11474465777) ^ 85 := by rw [pow_add]
          _ = 7991663511 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 11474465777) ^ 341 = 4744950555 := by
        calc
          (3 : ZMod 11474465777) ^ 341 = (3 : ZMod 11474465777) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 170 * (3 : ZMod 11474465777) ^ 170) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 4744950555 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 11474465777) ^ 683 = 2168996843 := by
        calc
          (3 : ZMod 11474465777) ^ 683 = (3 : ZMod 11474465777) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 341 * (3 : ZMod 11474465777) ^ 341) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 2168996843 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 11474465777) ^ 1367 = 1678566380 := by
        calc
          (3 : ZMod 11474465777) ^ 1367 = (3 : ZMod 11474465777) ^ (683 + 683 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 683 * (3 : ZMod 11474465777) ^ 683) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 1678566380 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 11474465777) ^ 2735 = 9964445304 := by
        calc
          (3 : ZMod 11474465777) ^ 2735 = (3 : ZMod 11474465777) ^ (1367 + 1367 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 1367 * (3 : ZMod 11474465777) ^ 1367) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 9964445304 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 11474465777) ^ 5471 = 5698807126 := by
        calc
          (3 : ZMod 11474465777) ^ 5471 = (3 : ZMod 11474465777) ^ (2735 + 2735 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 2735 * (3 : ZMod 11474465777) ^ 2735) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 5698807126 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 11474465777) ^ 10942 = 2098905602 := by
        calc
          (3 : ZMod 11474465777) ^ 10942 = (3 : ZMod 11474465777) ^ (5471 + 5471) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 5471 * (3 : ZMod 11474465777) ^ 5471 := by rw [pow_add]
          _ = 2098905602 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 11474465777) ^ 21885 = 9831625649 := by
        calc
          (3 : ZMod 11474465777) ^ 21885 = (3 : ZMod 11474465777) ^ (10942 + 10942 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 10942 * (3 : ZMod 11474465777) ^ 10942) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 9831625649 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 11474465777) ^ 43771 = 8664185674 := by
        calc
          (3 : ZMod 11474465777) ^ 43771 = (3 : ZMod 11474465777) ^ (21885 + 21885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 21885 * (3 : ZMod 11474465777) ^ 21885) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 8664185674 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 11474465777) ^ 87543 = 6740925714 := by
        calc
          (3 : ZMod 11474465777) ^ 87543 = (3 : ZMod 11474465777) ^ (43771 + 43771 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 43771 * (3 : ZMod 11474465777) ^ 43771) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6740925714 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 11474465777) ^ 175086 = 7982529908 := by
        calc
          (3 : ZMod 11474465777) ^ 175086 = (3 : ZMod 11474465777) ^ (87543 + 87543) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 87543 * (3 : ZMod 11474465777) ^ 87543 := by rw [pow_add]
          _ = 7982529908 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 11474465777) ^ 350172 = 860594694 := by
        calc
          (3 : ZMod 11474465777) ^ 350172 = (3 : ZMod 11474465777) ^ (175086 + 175086) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 175086 * (3 : ZMod 11474465777) ^ 175086 := by rw [pow_add]
          _ = 860594694 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 11474465777) ^ 700345 = 3878757354 := by
        calc
          (3 : ZMod 11474465777) ^ 700345 = (3 : ZMod 11474465777) ^ (350172 + 350172 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 350172 * (3 : ZMod 11474465777) ^ 350172) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 3878757354 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 11474465777) ^ 1400691 = 6575172552 := by
        calc
          (3 : ZMod 11474465777) ^ 1400691 = (3 : ZMod 11474465777) ^ (700345 + 700345 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 700345 * (3 : ZMod 11474465777) ^ 700345) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6575172552 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 11474465777) ^ 2801383 = 6821998717 := by
        calc
          (3 : ZMod 11474465777) ^ 2801383 = (3 : ZMod 11474465777) ^ (1400691 + 1400691 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 1400691 * (3 : ZMod 11474465777) ^ 1400691) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6821998717 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 11474465777) ^ 5602766 = 4091933675 := by
        calc
          (3 : ZMod 11474465777) ^ 5602766 = (3 : ZMod 11474465777) ^ (2801383 + 2801383) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2801383 * (3 : ZMod 11474465777) ^ 2801383 := by rw [pow_add]
          _ = 4091933675 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 11474465777) ^ 11205532 = 4551658988 := by
        calc
          (3 : ZMod 11474465777) ^ 11205532 = (3 : ZMod 11474465777) ^ (5602766 + 5602766) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 5602766 * (3 : ZMod 11474465777) ^ 5602766 := by rw [pow_add]
          _ = 4551658988 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 11474465777) ^ 22411065 = 3726625150 := by
        calc
          (3 : ZMod 11474465777) ^ 22411065 = (3 : ZMod 11474465777) ^ (11205532 + 11205532 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 11205532 * (3 : ZMod 11474465777) ^ 11205532) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 3726625150 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 11474465777) ^ 44822131 = 7387047282 := by
        calc
          (3 : ZMod 11474465777) ^ 44822131 = (3 : ZMod 11474465777) ^ (22411065 + 22411065 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 22411065 * (3 : ZMod 11474465777) ^ 22411065) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 7387047282 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 11474465777) ^ 89644263 = 6952421193 := by
        calc
          (3 : ZMod 11474465777) ^ 89644263 = (3 : ZMod 11474465777) ^ (44822131 + 44822131 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 44822131 * (3 : ZMod 11474465777) ^ 44822131) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6952421193 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 11474465777) ^ 179288527 = 8917732329 := by
        calc
          (3 : ZMod 11474465777) ^ 179288527 = (3 : ZMod 11474465777) ^ (89644263 + 89644263 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 89644263 * (3 : ZMod 11474465777) ^ 89644263) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 8917732329 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 11474465777) ^ 358577055 = 5271271162 := by
        calc
          (3 : ZMod 11474465777) ^ 358577055 = (3 : ZMod 11474465777) ^ (179288527 + 179288527 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 179288527 * (3 : ZMod 11474465777) ^ 179288527) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 5271271162 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 11474465777) ^ 717154111 = 1528397395 := by
        calc
          (3 : ZMod 11474465777) ^ 717154111 = (3 : ZMod 11474465777) ^ (358577055 + 358577055 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 358577055 * (3 : ZMod 11474465777) ^ 358577055) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 1528397395 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 11474465777) ^ 1434308222 = 3911207845 := by
        calc
          (3 : ZMod 11474465777) ^ 1434308222 = (3 : ZMod 11474465777) ^ (717154111 + 717154111) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 717154111 * (3 : ZMod 11474465777) ^ 717154111 := by rw [pow_add]
          _ = 3911207845 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 11474465777) ^ 2868616444 = 2420919947 := by
        calc
          (3 : ZMod 11474465777) ^ 2868616444 = (3 : ZMod 11474465777) ^ (1434308222 + 1434308222) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1434308222 * (3 : ZMod 11474465777) ^ 1434308222 := by rw [pow_add]
          _ = 2420919947 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 11474465777) ^ 5737232888 = 11474465776 := by
        calc
          (3 : ZMod 11474465777) ^ 5737232888 = (3 : ZMod 11474465777) ^ (2868616444 + 2868616444) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2868616444 * (3 : ZMod 11474465777) ^ 2868616444 := by rw [pow_add]
          _ = 11474465776 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 11474465777) ^ 11474465776 = 1 := by
        calc
          (3 : ZMod 11474465777) ^ 11474465776 = (3 : ZMod 11474465777) ^ (5737232888 + 5737232888) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 5737232888 * (3 : ZMod 11474465777) ^ 5737232888 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (607, 1), (1181473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (607, 1), (1181473, 1)] : List FactorBlock).map factorBlockValue).prod = 11474465777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 11474465777) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 11474465777) ^ 2 = 9 := by
        calc
          (3 : ZMod 11474465777) ^ 2 = (3 : ZMod 11474465777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1 * (3 : ZMod 11474465777) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 11474465777) ^ 5 = 243 := by
        calc
          (3 : ZMod 11474465777) ^ 5 = (3 : ZMod 11474465777) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 2 * (3 : ZMod 11474465777) ^ 2) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 11474465777) ^ 10 = 59049 := by
        calc
          (3 : ZMod 11474465777) ^ 10 = (3 : ZMod 11474465777) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 5 * (3 : ZMod 11474465777) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 11474465777) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 11474465777) ^ 21 = (3 : ZMod 11474465777) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 10 * (3 : ZMod 11474465777) ^ 10) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 11474465777) ^ 42 = 4809776414 := by
        calc
          (3 : ZMod 11474465777) ^ 42 = (3 : ZMod 11474465777) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 21 * (3 : ZMod 11474465777) ^ 21 := by rw [pow_add]
          _ = 4809776414 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 11474465777) ^ 85 = 559691306 := by
        calc
          (3 : ZMod 11474465777) ^ 85 = (3 : ZMod 11474465777) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 42 * (3 : ZMod 11474465777) ^ 42) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 559691306 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 11474465777) ^ 170 = 7991663511 := by
        calc
          (3 : ZMod 11474465777) ^ 170 = (3 : ZMod 11474465777) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 85 * (3 : ZMod 11474465777) ^ 85 := by rw [pow_add]
          _ = 7991663511 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 11474465777) ^ 341 = 4744950555 := by
        calc
          (3 : ZMod 11474465777) ^ 341 = (3 : ZMod 11474465777) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 170 * (3 : ZMod 11474465777) ^ 170) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 4744950555 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 11474465777) ^ 683 = 2168996843 := by
        calc
          (3 : ZMod 11474465777) ^ 683 = (3 : ZMod 11474465777) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 341 * (3 : ZMod 11474465777) ^ 341) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 2168996843 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 11474465777) ^ 1367 = 1678566380 := by
        calc
          (3 : ZMod 11474465777) ^ 1367 = (3 : ZMod 11474465777) ^ (683 + 683 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 683 * (3 : ZMod 11474465777) ^ 683) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 1678566380 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 11474465777) ^ 2735 = 9964445304 := by
        calc
          (3 : ZMod 11474465777) ^ 2735 = (3 : ZMod 11474465777) ^ (1367 + 1367 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 1367 * (3 : ZMod 11474465777) ^ 1367) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 9964445304 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 11474465777) ^ 5471 = 5698807126 := by
        calc
          (3 : ZMod 11474465777) ^ 5471 = (3 : ZMod 11474465777) ^ (2735 + 2735 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 2735 * (3 : ZMod 11474465777) ^ 2735) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 5698807126 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 11474465777) ^ 10942 = 2098905602 := by
        calc
          (3 : ZMod 11474465777) ^ 10942 = (3 : ZMod 11474465777) ^ (5471 + 5471) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 5471 * (3 : ZMod 11474465777) ^ 5471 := by rw [pow_add]
          _ = 2098905602 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 11474465777) ^ 21885 = 9831625649 := by
        calc
          (3 : ZMod 11474465777) ^ 21885 = (3 : ZMod 11474465777) ^ (10942 + 10942 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 10942 * (3 : ZMod 11474465777) ^ 10942) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 9831625649 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 11474465777) ^ 43771 = 8664185674 := by
        calc
          (3 : ZMod 11474465777) ^ 43771 = (3 : ZMod 11474465777) ^ (21885 + 21885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 21885 * (3 : ZMod 11474465777) ^ 21885) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 8664185674 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 11474465777) ^ 87543 = 6740925714 := by
        calc
          (3 : ZMod 11474465777) ^ 87543 = (3 : ZMod 11474465777) ^ (43771 + 43771 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 43771 * (3 : ZMod 11474465777) ^ 43771) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6740925714 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 11474465777) ^ 175086 = 7982529908 := by
        calc
          (3 : ZMod 11474465777) ^ 175086 = (3 : ZMod 11474465777) ^ (87543 + 87543) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 87543 * (3 : ZMod 11474465777) ^ 87543 := by rw [pow_add]
          _ = 7982529908 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 11474465777) ^ 350172 = 860594694 := by
        calc
          (3 : ZMod 11474465777) ^ 350172 = (3 : ZMod 11474465777) ^ (175086 + 175086) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 175086 * (3 : ZMod 11474465777) ^ 175086 := by rw [pow_add]
          _ = 860594694 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 11474465777) ^ 700345 = 3878757354 := by
        calc
          (3 : ZMod 11474465777) ^ 700345 = (3 : ZMod 11474465777) ^ (350172 + 350172 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 350172 * (3 : ZMod 11474465777) ^ 350172) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 3878757354 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 11474465777) ^ 1400691 = 6575172552 := by
        calc
          (3 : ZMod 11474465777) ^ 1400691 = (3 : ZMod 11474465777) ^ (700345 + 700345 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 700345 * (3 : ZMod 11474465777) ^ 700345) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6575172552 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 11474465777) ^ 2801383 = 6821998717 := by
        calc
          (3 : ZMod 11474465777) ^ 2801383 = (3 : ZMod 11474465777) ^ (1400691 + 1400691 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 1400691 * (3 : ZMod 11474465777) ^ 1400691) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6821998717 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 11474465777) ^ 5602766 = 4091933675 := by
        calc
          (3 : ZMod 11474465777) ^ 5602766 = (3 : ZMod 11474465777) ^ (2801383 + 2801383) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2801383 * (3 : ZMod 11474465777) ^ 2801383 := by rw [pow_add]
          _ = 4091933675 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 11474465777) ^ 11205532 = 4551658988 := by
        calc
          (3 : ZMod 11474465777) ^ 11205532 = (3 : ZMod 11474465777) ^ (5602766 + 5602766) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 5602766 * (3 : ZMod 11474465777) ^ 5602766 := by rw [pow_add]
          _ = 4551658988 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 11474465777) ^ 22411065 = 3726625150 := by
        calc
          (3 : ZMod 11474465777) ^ 22411065 = (3 : ZMod 11474465777) ^ (11205532 + 11205532 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 11205532 * (3 : ZMod 11474465777) ^ 11205532) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 3726625150 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 11474465777) ^ 44822131 = 7387047282 := by
        calc
          (3 : ZMod 11474465777) ^ 44822131 = (3 : ZMod 11474465777) ^ (22411065 + 22411065 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 22411065 * (3 : ZMod 11474465777) ^ 22411065) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 7387047282 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 11474465777) ^ 89644263 = 6952421193 := by
        calc
          (3 : ZMod 11474465777) ^ 89644263 = (3 : ZMod 11474465777) ^ (44822131 + 44822131 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 44822131 * (3 : ZMod 11474465777) ^ 44822131) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 6952421193 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 11474465777) ^ 179288527 = 8917732329 := by
        calc
          (3 : ZMod 11474465777) ^ 179288527 = (3 : ZMod 11474465777) ^ (89644263 + 89644263 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 89644263 * (3 : ZMod 11474465777) ^ 89644263) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 8917732329 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 11474465777) ^ 358577055 = 5271271162 := by
        calc
          (3 : ZMod 11474465777) ^ 358577055 = (3 : ZMod 11474465777) ^ (179288527 + 179288527 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 179288527 * (3 : ZMod 11474465777) ^ 179288527) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 5271271162 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 11474465777) ^ 717154111 = 1528397395 := by
        calc
          (3 : ZMod 11474465777) ^ 717154111 = (3 : ZMod 11474465777) ^ (358577055 + 358577055 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 358577055 * (3 : ZMod 11474465777) ^ 358577055) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 1528397395 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 11474465777) ^ 1434308222 = 3911207845 := by
        calc
          (3 : ZMod 11474465777) ^ 1434308222 = (3 : ZMod 11474465777) ^ (717154111 + 717154111) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 717154111 * (3 : ZMod 11474465777) ^ 717154111 := by rw [pow_add]
          _ = 3911207845 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 11474465777) ^ 2868616444 = 2420919947 := by
        calc
          (3 : ZMod 11474465777) ^ 2868616444 = (3 : ZMod 11474465777) ^ (1434308222 + 1434308222) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1434308222 * (3 : ZMod 11474465777) ^ 1434308222 := by rw [pow_add]
          _ = 2420919947 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 11474465777) ^ 5737232888 = 11474465776 := by
        calc
          (3 : ZMod 11474465777) ^ 5737232888 = (3 : ZMod 11474465777) ^ (2868616444 + 2868616444) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2868616444 * (3 : ZMod 11474465777) ^ 2868616444 := by rw [pow_add]
          _ = 11474465776 := by rw [factor_0_31]; decide
      change (3 : ZMod 11474465777) ^ 5737232888 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (3 : ZMod 11474465777) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 11474465777) ^ 2 = 9 := by
        calc
          (3 : ZMod 11474465777) ^ 2 = (3 : ZMod 11474465777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1 * (3 : ZMod 11474465777) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 11474465777) ^ 4 = 81 := by
        calc
          (3 : ZMod 11474465777) ^ 4 = (3 : ZMod 11474465777) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2 * (3 : ZMod 11474465777) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 11474465777) ^ 9 = 19683 := by
        calc
          (3 : ZMod 11474465777) ^ 9 = (3 : ZMod 11474465777) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 4 * (3 : ZMod 11474465777) ^ 4) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 11474465777) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 11474465777) ^ 18 = (3 : ZMod 11474465777) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 9 * (3 : ZMod 11474465777) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 11474465777) ^ 36 = 5610040594 := by
        calc
          (3 : ZMod 11474465777) ^ 36 = (3 : ZMod 11474465777) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 18 * (3 : ZMod 11474465777) ^ 18 := by rw [pow_add]
          _ = 5610040594 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 11474465777) ^ 72 = 4663634432 := by
        calc
          (3 : ZMod 11474465777) ^ 72 = (3 : ZMod 11474465777) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 36 * (3 : ZMod 11474465777) ^ 36 := by rw [pow_add]
          _ = 4663634432 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 11474465777) ^ 144 = 10020990855 := by
        calc
          (3 : ZMod 11474465777) ^ 144 = (3 : ZMod 11474465777) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 72 * (3 : ZMod 11474465777) ^ 72 := by rw [pow_add]
          _ = 10020990855 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 11474465777) ^ 288 = 4314342698 := by
        calc
          (3 : ZMod 11474465777) ^ 288 = (3 : ZMod 11474465777) ^ (144 + 144) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 144 * (3 : ZMod 11474465777) ^ 144 := by rw [pow_add]
          _ = 4314342698 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 11474465777) ^ 576 = 5558283809 := by
        calc
          (3 : ZMod 11474465777) ^ 576 = (3 : ZMod 11474465777) ^ (288 + 288) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 288 * (3 : ZMod 11474465777) ^ 288 := by rw [pow_add]
          _ = 5558283809 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 11474465777) ^ 1153 = 9635447793 := by
        calc
          (3 : ZMod 11474465777) ^ 1153 = (3 : ZMod 11474465777) ^ (576 + 576 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 576 * (3 : ZMod 11474465777) ^ 576) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 9635447793 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 11474465777) ^ 2307 = 1295587621 := by
        calc
          (3 : ZMod 11474465777) ^ 2307 = (3 : ZMod 11474465777) ^ (1153 + 1153 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 1153 * (3 : ZMod 11474465777) ^ 1153) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 1295587621 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 11474465777) ^ 4615 = 3256226729 := by
        calc
          (3 : ZMod 11474465777) ^ 4615 = (3 : ZMod 11474465777) ^ (2307 + 2307 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 2307 * (3 : ZMod 11474465777) ^ 2307) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 3256226729 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 11474465777) ^ 9230 = 5525835193 := by
        calc
          (3 : ZMod 11474465777) ^ 9230 = (3 : ZMod 11474465777) ^ (4615 + 4615) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 4615 * (3 : ZMod 11474465777) ^ 4615 := by rw [pow_add]
          _ = 5525835193 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 11474465777) ^ 18460 = 553564334 := by
        calc
          (3 : ZMod 11474465777) ^ 18460 = (3 : ZMod 11474465777) ^ (9230 + 9230) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 9230 * (3 : ZMod 11474465777) ^ 9230 := by rw [pow_add]
          _ = 553564334 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 11474465777) ^ 36921 = 9879063933 := by
        calc
          (3 : ZMod 11474465777) ^ 36921 = (3 : ZMod 11474465777) ^ (18460 + 18460 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 18460 * (3 : ZMod 11474465777) ^ 18460) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 9879063933 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 11474465777) ^ 73842 = 1020376007 := by
        calc
          (3 : ZMod 11474465777) ^ 73842 = (3 : ZMod 11474465777) ^ (36921 + 36921) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 36921 * (3 : ZMod 11474465777) ^ 36921 := by rw [pow_add]
          _ = 1020376007 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 11474465777) ^ 147684 = 78748076 := by
        calc
          (3 : ZMod 11474465777) ^ 147684 = (3 : ZMod 11474465777) ^ (73842 + 73842) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 73842 * (3 : ZMod 11474465777) ^ 73842 := by rw [pow_add]
          _ = 78748076 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 11474465777) ^ 295368 = 10663645673 := by
        calc
          (3 : ZMod 11474465777) ^ 295368 = (3 : ZMod 11474465777) ^ (147684 + 147684) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 147684 * (3 : ZMod 11474465777) ^ 147684 := by rw [pow_add]
          _ = 10663645673 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 11474465777) ^ 590736 = 11219000241 := by
        calc
          (3 : ZMod 11474465777) ^ 590736 = (3 : ZMod 11474465777) ^ (295368 + 295368) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 295368 * (3 : ZMod 11474465777) ^ 295368 := by rw [pow_add]
          _ = 11219000241 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 11474465777) ^ 1181473 = 5706681494 := by
        calc
          (3 : ZMod 11474465777) ^ 1181473 = (3 : ZMod 11474465777) ^ (590736 + 590736 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 590736 * (3 : ZMod 11474465777) ^ 590736) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 5706681494 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 11474465777) ^ 2362946 = 5893113898 := by
        calc
          (3 : ZMod 11474465777) ^ 2362946 = (3 : ZMod 11474465777) ^ (1181473 + 1181473) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1181473 * (3 : ZMod 11474465777) ^ 1181473 := by rw [pow_add]
          _ = 5893113898 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 11474465777) ^ 4725892 = 6750390150 := by
        calc
          (3 : ZMod 11474465777) ^ 4725892 = (3 : ZMod 11474465777) ^ (2362946 + 2362946) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2362946 * (3 : ZMod 11474465777) ^ 2362946 := by rw [pow_add]
          _ = 6750390150 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 11474465777) ^ 9451784 = 9009207490 := by
        calc
          (3 : ZMod 11474465777) ^ 9451784 = (3 : ZMod 11474465777) ^ (4725892 + 4725892) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 4725892 * (3 : ZMod 11474465777) ^ 4725892 := by rw [pow_add]
          _ = 9009207490 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 11474465777) ^ 18903568 = 3801149819 := by
        calc
          (3 : ZMod 11474465777) ^ 18903568 = (3 : ZMod 11474465777) ^ (9451784 + 9451784) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 9451784 * (3 : ZMod 11474465777) ^ 9451784 := by rw [pow_add]
          _ = 3801149819 := by rw [factor_1_23]; decide
      change (3 : ZMod 11474465777) ^ 18903568 ≠ 1
      rw [factor_1_24]
      decide
    ·
      have factor_2_0 : (3 : ZMod 11474465777) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 11474465777) ^ 2 = 9 := by
        calc
          (3 : ZMod 11474465777) ^ 2 = (3 : ZMod 11474465777) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1 * (3 : ZMod 11474465777) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 11474465777) ^ 4 = 81 := by
        calc
          (3 : ZMod 11474465777) ^ 4 = (3 : ZMod 11474465777) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2 * (3 : ZMod 11474465777) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 11474465777) ^ 9 = 19683 := by
        calc
          (3 : ZMod 11474465777) ^ 9 = (3 : ZMod 11474465777) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 4 * (3 : ZMod 11474465777) ^ 4) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 11474465777) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 11474465777) ^ 18 = (3 : ZMod 11474465777) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 9 * (3 : ZMod 11474465777) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 11474465777) ^ 37 = 5355656005 := by
        calc
          (3 : ZMod 11474465777) ^ 37 = (3 : ZMod 11474465777) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 18 * (3 : ZMod 11474465777) ^ 18) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 5355656005 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 11474465777) ^ 75 = 11173471894 := by
        calc
          (3 : ZMod 11474465777) ^ 75 = (3 : ZMod 11474465777) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 37 * (3 : ZMod 11474465777) ^ 37) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 11173471894 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 11474465777) ^ 151 = 11151831592 := by
        calc
          (3 : ZMod 11474465777) ^ 151 = (3 : ZMod 11474465777) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 75 * (3 : ZMod 11474465777) ^ 75) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 11151831592 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 11474465777) ^ 303 = 5285854400 := by
        calc
          (3 : ZMod 11474465777) ^ 303 = (3 : ZMod 11474465777) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 151 * (3 : ZMod 11474465777) ^ 151) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 5285854400 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 11474465777) ^ 607 = 7844728510 := by
        calc
          (3 : ZMod 11474465777) ^ 607 = (3 : ZMod 11474465777) ^ (303 + 303 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = ((3 : ZMod 11474465777) ^ 303 * (3 : ZMod 11474465777) ^ 303) * (3 : ZMod 11474465777) := by rw [pow_succ, pow_add]
          _ = 7844728510 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 11474465777) ^ 1214 = 6810083369 := by
        calc
          (3 : ZMod 11474465777) ^ 1214 = (3 : ZMod 11474465777) ^ (607 + 607) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 607 * (3 : ZMod 11474465777) ^ 607 := by rw [pow_add]
          _ = 6810083369 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 11474465777) ^ 2428 = 2033475629 := by
        calc
          (3 : ZMod 11474465777) ^ 2428 = (3 : ZMod 11474465777) ^ (1214 + 1214) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 1214 * (3 : ZMod 11474465777) ^ 1214 := by rw [pow_add]
          _ = 2033475629 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 11474465777) ^ 4856 = 10677654489 := by
        calc
          (3 : ZMod 11474465777) ^ 4856 = (3 : ZMod 11474465777) ^ (2428 + 2428) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 2428 * (3 : ZMod 11474465777) ^ 2428 := by rw [pow_add]
          _ = 10677654489 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 11474465777) ^ 9712 = 1679960931 := by
        calc
          (3 : ZMod 11474465777) ^ 9712 = (3 : ZMod 11474465777) ^ (4856 + 4856) :=
            congrArg (fun n : ℕ => (3 : ZMod 11474465777) ^ n) (by norm_num)
          _ = (3 : ZMod 11474465777) ^ 4856 * (3 : ZMod 11474465777) ^ 4856 := by rw [pow_add]
          _ = 1679960931 := by rw [factor_2_12]; decide
      change (3 : ZMod 11474465777) ^ 9712 ≠ 1
      rw [factor_2_13]
      decide

#print axioms prime_lucas_11474465777

end TotientTailPeriodKiller
end Erdos249257
