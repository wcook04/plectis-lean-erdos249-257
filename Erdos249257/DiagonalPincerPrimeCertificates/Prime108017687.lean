import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_108017687 : Nat.Prime 108017687 := by
  apply lucas_primality 108017687 (5 : ZMod 108017687)
  ·
      have fermat_0 : (5 : ZMod 108017687) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 108017687) ^ 3 = 125 := by
        calc
          (5 : ZMod 108017687) ^ 3 = (5 : ZMod 108017687) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 1 * (5 : ZMod 108017687) ^ 1) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 108017687) ^ 6 = 15625 := by
        calc
          (5 : ZMod 108017687) ^ 6 = (5 : ZMod 108017687) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 3 * (5 : ZMod 108017687) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 108017687) ^ 12 = 28105251 := by
        calc
          (5 : ZMod 108017687) ^ 12 = (5 : ZMod 108017687) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 6 * (5 : ZMod 108017687) ^ 6 := by rw [pow_add]
          _ = 28105251 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 108017687) ^ 25 = 14809227 := by
        calc
          (5 : ZMod 108017687) ^ 25 = (5 : ZMod 108017687) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 12 * (5 : ZMod 108017687) ^ 12) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 14809227 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 108017687) ^ 51 = 60109883 := by
        calc
          (5 : ZMod 108017687) ^ 51 = (5 : ZMod 108017687) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 25 * (5 : ZMod 108017687) ^ 25) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 60109883 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 108017687) ^ 103 = 47383093 := by
        calc
          (5 : ZMod 108017687) ^ 103 = (5 : ZMod 108017687) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 51 * (5 : ZMod 108017687) ^ 51) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 47383093 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 108017687) ^ 206 = 48342132 := by
        calc
          (5 : ZMod 108017687) ^ 206 = (5 : ZMod 108017687) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 103 * (5 : ZMod 108017687) ^ 103 := by rw [pow_add]
          _ = 48342132 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 108017687) ^ 412 = 40219607 := by
        calc
          (5 : ZMod 108017687) ^ 412 = (5 : ZMod 108017687) ^ (206 + 206) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 206 * (5 : ZMod 108017687) ^ 206 := by rw [pow_add]
          _ = 40219607 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 108017687) ^ 824 = 75919689 := by
        calc
          (5 : ZMod 108017687) ^ 824 = (5 : ZMod 108017687) ^ (412 + 412) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 412 * (5 : ZMod 108017687) ^ 412 := by rw [pow_add]
          _ = 75919689 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 108017687) ^ 1648 = 27569357 := by
        calc
          (5 : ZMod 108017687) ^ 1648 = (5 : ZMod 108017687) ^ (824 + 824) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 824 * (5 : ZMod 108017687) ^ 824 := by rw [pow_add]
          _ = 27569357 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 108017687) ^ 3296 = 74340400 := by
        calc
          (5 : ZMod 108017687) ^ 3296 = (5 : ZMod 108017687) ^ (1648 + 1648) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 1648 * (5 : ZMod 108017687) ^ 1648 := by rw [pow_add]
          _ = 74340400 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 108017687) ^ 6592 = 86460623 := by
        calc
          (5 : ZMod 108017687) ^ 6592 = (5 : ZMod 108017687) ^ (3296 + 3296) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 3296 * (5 : ZMod 108017687) ^ 3296 := by rw [pow_add]
          _ = 86460623 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 108017687) ^ 13185 = 61926450 := by
        calc
          (5 : ZMod 108017687) ^ 13185 = (5 : ZMod 108017687) ^ (6592 + 6592 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 6592 * (5 : ZMod 108017687) ^ 6592) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 61926450 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 108017687) ^ 26371 = 6842643 := by
        calc
          (5 : ZMod 108017687) ^ 26371 = (5 : ZMod 108017687) ^ (13185 + 13185 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 13185 * (5 : ZMod 108017687) ^ 13185) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 6842643 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 108017687) ^ 52743 = 30756092 := by
        calc
          (5 : ZMod 108017687) ^ 52743 = (5 : ZMod 108017687) ^ (26371 + 26371 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 26371 * (5 : ZMod 108017687) ^ 26371) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 30756092 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 108017687) ^ 105486 = 61755523 := by
        calc
          (5 : ZMod 108017687) ^ 105486 = (5 : ZMod 108017687) ^ (52743 + 52743) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 52743 * (5 : ZMod 108017687) ^ 52743 := by rw [pow_add]
          _ = 61755523 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 108017687) ^ 210972 = 7966613 := by
        calc
          (5 : ZMod 108017687) ^ 210972 = (5 : ZMod 108017687) ^ (105486 + 105486) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 105486 * (5 : ZMod 108017687) ^ 105486 := by rw [pow_add]
          _ = 7966613 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 108017687) ^ 421944 = 50518049 := by
        calc
          (5 : ZMod 108017687) ^ 421944 = (5 : ZMod 108017687) ^ (210972 + 210972) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 210972 * (5 : ZMod 108017687) ^ 210972 := by rw [pow_add]
          _ = 50518049 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 108017687) ^ 843888 = 89957495 := by
        calc
          (5 : ZMod 108017687) ^ 843888 = (5 : ZMod 108017687) ^ (421944 + 421944) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 421944 * (5 : ZMod 108017687) ^ 421944 := by rw [pow_add]
          _ = 89957495 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 108017687) ^ 1687776 = 3358603 := by
        calc
          (5 : ZMod 108017687) ^ 1687776 = (5 : ZMod 108017687) ^ (843888 + 843888) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 843888 * (5 : ZMod 108017687) ^ 843888 := by rw [pow_add]
          _ = 3358603 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 108017687) ^ 3375552 = 35075886 := by
        calc
          (5 : ZMod 108017687) ^ 3375552 = (5 : ZMod 108017687) ^ (1687776 + 1687776) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 1687776 * (5 : ZMod 108017687) ^ 1687776 := by rw [pow_add]
          _ = 35075886 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 108017687) ^ 6751105 = 89799457 := by
        calc
          (5 : ZMod 108017687) ^ 6751105 = (5 : ZMod 108017687) ^ (3375552 + 3375552 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 3375552 * (5 : ZMod 108017687) ^ 3375552) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 89799457 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 108017687) ^ 13502210 = 9824053 := by
        calc
          (5 : ZMod 108017687) ^ 13502210 = (5 : ZMod 108017687) ^ (6751105 + 6751105) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 6751105 * (5 : ZMod 108017687) ^ 6751105 := by rw [pow_add]
          _ = 9824053 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 108017687) ^ 27004421 = 35529566 := by
        calc
          (5 : ZMod 108017687) ^ 27004421 = (5 : ZMod 108017687) ^ (13502210 + 13502210 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 13502210 * (5 : ZMod 108017687) ^ 13502210) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 35529566 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 108017687) ^ 54008843 = 108017686 := by
        calc
          (5 : ZMod 108017687) ^ 54008843 = (5 : ZMod 108017687) ^ (27004421 + 27004421 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 27004421 * (5 : ZMod 108017687) ^ 27004421) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 108017686 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 108017687) ^ 108017686 = 1 := by
        calc
          (5 : ZMod 108017687) ^ 108017686 = (5 : ZMod 108017687) ^ (54008843 + 54008843) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 54008843 * (5 : ZMod 108017687) ^ 54008843 := by rw [pow_add]
          _ = 1 := by rw [fermat_25]; decide
      simpa using fermat_26
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (7715549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (7715549, 1)] : List FactorBlock).map factorBlockValue).prod = 108017687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 108017687) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 108017687) ^ 3 = 125 := by
        calc
          (5 : ZMod 108017687) ^ 3 = (5 : ZMod 108017687) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 1 * (5 : ZMod 108017687) ^ 1) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 108017687) ^ 6 = 15625 := by
        calc
          (5 : ZMod 108017687) ^ 6 = (5 : ZMod 108017687) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 3 * (5 : ZMod 108017687) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 108017687) ^ 12 = 28105251 := by
        calc
          (5 : ZMod 108017687) ^ 12 = (5 : ZMod 108017687) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 6 * (5 : ZMod 108017687) ^ 6 := by rw [pow_add]
          _ = 28105251 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 108017687) ^ 25 = 14809227 := by
        calc
          (5 : ZMod 108017687) ^ 25 = (5 : ZMod 108017687) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 12 * (5 : ZMod 108017687) ^ 12) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 14809227 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 108017687) ^ 51 = 60109883 := by
        calc
          (5 : ZMod 108017687) ^ 51 = (5 : ZMod 108017687) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 25 * (5 : ZMod 108017687) ^ 25) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 60109883 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 108017687) ^ 103 = 47383093 := by
        calc
          (5 : ZMod 108017687) ^ 103 = (5 : ZMod 108017687) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 51 * (5 : ZMod 108017687) ^ 51) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 47383093 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 108017687) ^ 206 = 48342132 := by
        calc
          (5 : ZMod 108017687) ^ 206 = (5 : ZMod 108017687) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 103 * (5 : ZMod 108017687) ^ 103 := by rw [pow_add]
          _ = 48342132 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 108017687) ^ 412 = 40219607 := by
        calc
          (5 : ZMod 108017687) ^ 412 = (5 : ZMod 108017687) ^ (206 + 206) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 206 * (5 : ZMod 108017687) ^ 206 := by rw [pow_add]
          _ = 40219607 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 108017687) ^ 824 = 75919689 := by
        calc
          (5 : ZMod 108017687) ^ 824 = (5 : ZMod 108017687) ^ (412 + 412) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 412 * (5 : ZMod 108017687) ^ 412 := by rw [pow_add]
          _ = 75919689 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 108017687) ^ 1648 = 27569357 := by
        calc
          (5 : ZMod 108017687) ^ 1648 = (5 : ZMod 108017687) ^ (824 + 824) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 824 * (5 : ZMod 108017687) ^ 824 := by rw [pow_add]
          _ = 27569357 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 108017687) ^ 3296 = 74340400 := by
        calc
          (5 : ZMod 108017687) ^ 3296 = (5 : ZMod 108017687) ^ (1648 + 1648) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 1648 * (5 : ZMod 108017687) ^ 1648 := by rw [pow_add]
          _ = 74340400 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 108017687) ^ 6592 = 86460623 := by
        calc
          (5 : ZMod 108017687) ^ 6592 = (5 : ZMod 108017687) ^ (3296 + 3296) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 3296 * (5 : ZMod 108017687) ^ 3296 := by rw [pow_add]
          _ = 86460623 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 108017687) ^ 13185 = 61926450 := by
        calc
          (5 : ZMod 108017687) ^ 13185 = (5 : ZMod 108017687) ^ (6592 + 6592 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 6592 * (5 : ZMod 108017687) ^ 6592) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 61926450 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 108017687) ^ 26371 = 6842643 := by
        calc
          (5 : ZMod 108017687) ^ 26371 = (5 : ZMod 108017687) ^ (13185 + 13185 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 13185 * (5 : ZMod 108017687) ^ 13185) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 6842643 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 108017687) ^ 52743 = 30756092 := by
        calc
          (5 : ZMod 108017687) ^ 52743 = (5 : ZMod 108017687) ^ (26371 + 26371 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 26371 * (5 : ZMod 108017687) ^ 26371) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 30756092 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 108017687) ^ 105486 = 61755523 := by
        calc
          (5 : ZMod 108017687) ^ 105486 = (5 : ZMod 108017687) ^ (52743 + 52743) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 52743 * (5 : ZMod 108017687) ^ 52743 := by rw [pow_add]
          _ = 61755523 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 108017687) ^ 210972 = 7966613 := by
        calc
          (5 : ZMod 108017687) ^ 210972 = (5 : ZMod 108017687) ^ (105486 + 105486) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 105486 * (5 : ZMod 108017687) ^ 105486 := by rw [pow_add]
          _ = 7966613 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 108017687) ^ 421944 = 50518049 := by
        calc
          (5 : ZMod 108017687) ^ 421944 = (5 : ZMod 108017687) ^ (210972 + 210972) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 210972 * (5 : ZMod 108017687) ^ 210972 := by rw [pow_add]
          _ = 50518049 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 108017687) ^ 843888 = 89957495 := by
        calc
          (5 : ZMod 108017687) ^ 843888 = (5 : ZMod 108017687) ^ (421944 + 421944) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 421944 * (5 : ZMod 108017687) ^ 421944 := by rw [pow_add]
          _ = 89957495 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 108017687) ^ 1687776 = 3358603 := by
        calc
          (5 : ZMod 108017687) ^ 1687776 = (5 : ZMod 108017687) ^ (843888 + 843888) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 843888 * (5 : ZMod 108017687) ^ 843888 := by rw [pow_add]
          _ = 3358603 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 108017687) ^ 3375552 = 35075886 := by
        calc
          (5 : ZMod 108017687) ^ 3375552 = (5 : ZMod 108017687) ^ (1687776 + 1687776) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 1687776 * (5 : ZMod 108017687) ^ 1687776 := by rw [pow_add]
          _ = 35075886 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 108017687) ^ 6751105 = 89799457 := by
        calc
          (5 : ZMod 108017687) ^ 6751105 = (5 : ZMod 108017687) ^ (3375552 + 3375552 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 3375552 * (5 : ZMod 108017687) ^ 3375552) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 89799457 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 108017687) ^ 13502210 = 9824053 := by
        calc
          (5 : ZMod 108017687) ^ 13502210 = (5 : ZMod 108017687) ^ (6751105 + 6751105) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 6751105 * (5 : ZMod 108017687) ^ 6751105 := by rw [pow_add]
          _ = 9824053 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 108017687) ^ 27004421 = 35529566 := by
        calc
          (5 : ZMod 108017687) ^ 27004421 = (5 : ZMod 108017687) ^ (13502210 + 13502210 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 13502210 * (5 : ZMod 108017687) ^ 13502210) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 35529566 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 108017687) ^ 54008843 = 108017686 := by
        calc
          (5 : ZMod 108017687) ^ 54008843 = (5 : ZMod 108017687) ^ (27004421 + 27004421 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 27004421 * (5 : ZMod 108017687) ^ 27004421) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 108017686 := by rw [factor_0_24]; decide
      change (5 : ZMod 108017687) ^ 54008843 ≠ 1
      rw [factor_0_25]
      decide
    ·
      have factor_1_0 : (5 : ZMod 108017687) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 108017687) ^ 3 = 125 := by
        calc
          (5 : ZMod 108017687) ^ 3 = (5 : ZMod 108017687) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 1 * (5 : ZMod 108017687) ^ 1) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 108017687) ^ 7 = 78125 := by
        calc
          (5 : ZMod 108017687) ^ 7 = (5 : ZMod 108017687) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 3 * (5 : ZMod 108017687) ^ 3) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 108017687) ^ 14 = 54525153 := by
        calc
          (5 : ZMod 108017687) ^ 14 = (5 : ZMod 108017687) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 7 * (5 : ZMod 108017687) ^ 7 := by rw [pow_add]
          _ = 54525153 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 108017687) ^ 29 = 74263480 := by
        calc
          (5 : ZMod 108017687) ^ 29 = (5 : ZMod 108017687) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 14 * (5 : ZMod 108017687) ^ 14) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 74263480 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 108017687) ^ 58 = 15667050 := by
        calc
          (5 : ZMod 108017687) ^ 58 = (5 : ZMod 108017687) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 29 * (5 : ZMod 108017687) ^ 29 := by rw [pow_add]
          _ = 15667050 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 108017687) ^ 117 = 9223932 := by
        calc
          (5 : ZMod 108017687) ^ 117 = (5 : ZMod 108017687) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 58 * (5 : ZMod 108017687) ^ 58) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 9223932 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 108017687) ^ 235 = 63238638 := by
        calc
          (5 : ZMod 108017687) ^ 235 = (5 : ZMod 108017687) ^ (117 + 117 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 117 * (5 : ZMod 108017687) ^ 117) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 63238638 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 108017687) ^ 470 = 12504919 := by
        calc
          (5 : ZMod 108017687) ^ 470 = (5 : ZMod 108017687) ^ (235 + 235) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 235 * (5 : ZMod 108017687) ^ 235 := by rw [pow_add]
          _ = 12504919 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 108017687) ^ 941 = 32082270 := by
        calc
          (5 : ZMod 108017687) ^ 941 = (5 : ZMod 108017687) ^ (470 + 470 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 470 * (5 : ZMod 108017687) ^ 470) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 32082270 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 108017687) ^ 1883 = 19978653 := by
        calc
          (5 : ZMod 108017687) ^ 1883 = (5 : ZMod 108017687) ^ (941 + 941 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 941 * (5 : ZMod 108017687) ^ 941) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 19978653 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 108017687) ^ 3767 = 37778411 := by
        calc
          (5 : ZMod 108017687) ^ 3767 = (5 : ZMod 108017687) ^ (1883 + 1883 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 1883 * (5 : ZMod 108017687) ^ 1883) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 37778411 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 108017687) ^ 7534 = 20164785 := by
        calc
          (5 : ZMod 108017687) ^ 7534 = (5 : ZMod 108017687) ^ (3767 + 3767) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 3767 * (5 : ZMod 108017687) ^ 3767 := by rw [pow_add]
          _ = 20164785 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 108017687) ^ 15069 = 68420175 := by
        calc
          (5 : ZMod 108017687) ^ 15069 = (5 : ZMod 108017687) ^ (7534 + 7534 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 7534 * (5 : ZMod 108017687) ^ 7534) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 68420175 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 108017687) ^ 30138 = 31670918 := by
        calc
          (5 : ZMod 108017687) ^ 30138 = (5 : ZMod 108017687) ^ (15069 + 15069) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 15069 * (5 : ZMod 108017687) ^ 15069 := by rw [pow_add]
          _ = 31670918 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 108017687) ^ 60277 = 59666187 := by
        calc
          (5 : ZMod 108017687) ^ 60277 = (5 : ZMod 108017687) ^ (30138 + 30138 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 30138 * (5 : ZMod 108017687) ^ 30138) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 59666187 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 108017687) ^ 120555 = 41187318 := by
        calc
          (5 : ZMod 108017687) ^ 120555 = (5 : ZMod 108017687) ^ (60277 + 60277 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 60277 * (5 : ZMod 108017687) ^ 60277) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 41187318 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 108017687) ^ 241110 = 73412394 := by
        calc
          (5 : ZMod 108017687) ^ 241110 = (5 : ZMod 108017687) ^ (120555 + 120555) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 120555 * (5 : ZMod 108017687) ^ 120555 := by rw [pow_add]
          _ = 73412394 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 108017687) ^ 482221 = 61108847 := by
        calc
          (5 : ZMod 108017687) ^ 482221 = (5 : ZMod 108017687) ^ (241110 + 241110 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 241110 * (5 : ZMod 108017687) ^ 241110) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 61108847 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 108017687) ^ 964443 = 76375691 := by
        calc
          (5 : ZMod 108017687) ^ 964443 = (5 : ZMod 108017687) ^ (482221 + 482221 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 482221 * (5 : ZMod 108017687) ^ 482221) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 76375691 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 108017687) ^ 1928887 = 66340454 := by
        calc
          (5 : ZMod 108017687) ^ 1928887 = (5 : ZMod 108017687) ^ (964443 + 964443 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 964443 * (5 : ZMod 108017687) ^ 964443) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 66340454 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 108017687) ^ 3857774 = 48557288 := by
        calc
          (5 : ZMod 108017687) ^ 3857774 = (5 : ZMod 108017687) ^ (1928887 + 1928887) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 1928887 * (5 : ZMod 108017687) ^ 1928887 := by rw [pow_add]
          _ = 48557288 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 108017687) ^ 7715549 = 82288598 := by
        calc
          (5 : ZMod 108017687) ^ 7715549 = (5 : ZMod 108017687) ^ (3857774 + 3857774 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 3857774 * (5 : ZMod 108017687) ^ 3857774) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 82288598 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 108017687) ^ 15431098 = 58061169 := by
        calc
          (5 : ZMod 108017687) ^ 15431098 = (5 : ZMod 108017687) ^ (7715549 + 7715549) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 7715549 * (5 : ZMod 108017687) ^ 7715549 := by rw [pow_add]
          _ = 58061169 := by rw [factor_1_22]; decide
      change (5 : ZMod 108017687) ^ 15431098 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (5 : ZMod 108017687) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 108017687) ^ 3 = 125 := by
        calc
          (5 : ZMod 108017687) ^ 3 = (5 : ZMod 108017687) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 1 * (5 : ZMod 108017687) ^ 1) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 108017687) ^ 7 = 78125 := by
        calc
          (5 : ZMod 108017687) ^ 7 = (5 : ZMod 108017687) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = ((5 : ZMod 108017687) ^ 3 * (5 : ZMod 108017687) ^ 3) * (5 : ZMod 108017687) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 108017687) ^ 14 = 54525153 := by
        calc
          (5 : ZMod 108017687) ^ 14 = (5 : ZMod 108017687) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 108017687) ^ n) (by norm_num)
          _ = (5 : ZMod 108017687) ^ 7 * (5 : ZMod 108017687) ^ 7 := by rw [pow_add]
          _ = 54525153 := by rw [factor_2_2]; decide
      change (5 : ZMod 108017687) ^ 14 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_108017687

end TotientTailPeriodKiller
end Erdos249257
