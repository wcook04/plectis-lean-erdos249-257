import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3376178933

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6752357867 : Nat.Prime 6752357867 := by
  apply lucas_primality 6752357867 (2 : ZMod 6752357867)
  ·
      have fermat_0 : (2 : ZMod 6752357867) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 6752357867) ^ 3 = 8 := by
        calc
          (2 : ZMod 6752357867) ^ 3 = (2 : ZMod 6752357867) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1 * (2 : ZMod 6752357867) ^ 1) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 6752357867) ^ 6 = 64 := by
        calc
          (2 : ZMod 6752357867) ^ 6 = (2 : ZMod 6752357867) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 3 * (2 : ZMod 6752357867) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 6752357867) ^ 12 = 4096 := by
        calc
          (2 : ZMod 6752357867) ^ 12 = (2 : ZMod 6752357867) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 6 * (2 : ZMod 6752357867) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 6752357867) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 6752357867) ^ 25 = (2 : ZMod 6752357867) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 12 * (2 : ZMod 6752357867) ^ 12) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 6752357867) ^ 50 = 5003741177 := by
        calc
          (2 : ZMod 6752357867) ^ 50 = (2 : ZMod 6752357867) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 25 * (2 : ZMod 6752357867) ^ 25 := by rw [pow_add]
          _ = 5003741177 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 6752357867) ^ 100 = 1084863388 := by
        calc
          (2 : ZMod 6752357867) ^ 100 = (2 : ZMod 6752357867) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 50 * (2 : ZMod 6752357867) ^ 50 := by rw [pow_add]
          _ = 1084863388 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 6752357867) ^ 201 = 3482637286 := by
        calc
          (2 : ZMod 6752357867) ^ 201 = (2 : ZMod 6752357867) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 100 * (2 : ZMod 6752357867) ^ 100) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3482637286 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 6752357867) ^ 402 = 2233321312 := by
        calc
          (2 : ZMod 6752357867) ^ 402 = (2 : ZMod 6752357867) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 201 * (2 : ZMod 6752357867) ^ 201 := by rw [pow_add]
          _ = 2233321312 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 6752357867) ^ 804 = 6022241324 := by
        calc
          (2 : ZMod 6752357867) ^ 804 = (2 : ZMod 6752357867) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 402 * (2 : ZMod 6752357867) ^ 402 := by rw [pow_add]
          _ = 6022241324 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 6752357867) ^ 1609 = 1920923444 := by
        calc
          (2 : ZMod 6752357867) ^ 1609 = (2 : ZMod 6752357867) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 804 * (2 : ZMod 6752357867) ^ 804) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 1920923444 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 6752357867) ^ 3219 = 123977800 := by
        calc
          (2 : ZMod 6752357867) ^ 3219 = (2 : ZMod 6752357867) ^ (1609 + 1609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1609 * (2 : ZMod 6752357867) ^ 1609) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 123977800 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 6752357867) ^ 6439 = 2789639790 := by
        calc
          (2 : ZMod 6752357867) ^ 6439 = (2 : ZMod 6752357867) ^ (3219 + 3219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 3219 * (2 : ZMod 6752357867) ^ 3219) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 2789639790 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 6752357867) ^ 12879 = 3813764159 := by
        calc
          (2 : ZMod 6752357867) ^ 12879 = (2 : ZMod 6752357867) ^ (6439 + 6439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 6439 * (2 : ZMod 6752357867) ^ 6439) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3813764159 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 6752357867) ^ 25758 = 5758147309 := by
        calc
          (2 : ZMod 6752357867) ^ 25758 = (2 : ZMod 6752357867) ^ (12879 + 12879) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 12879 * (2 : ZMod 6752357867) ^ 12879 := by rw [pow_add]
          _ = 5758147309 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 6752357867) ^ 51516 = 4533583568 := by
        calc
          (2 : ZMod 6752357867) ^ 51516 = (2 : ZMod 6752357867) ^ (25758 + 25758) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 25758 * (2 : ZMod 6752357867) ^ 25758 := by rw [pow_add]
          _ = 4533583568 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 6752357867) ^ 103032 = 79766787 := by
        calc
          (2 : ZMod 6752357867) ^ 103032 = (2 : ZMod 6752357867) ^ (51516 + 51516) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 51516 * (2 : ZMod 6752357867) ^ 51516 := by rw [pow_add]
          _ = 79766787 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 6752357867) ^ 206065 = 485174272 := by
        calc
          (2 : ZMod 6752357867) ^ 206065 = (2 : ZMod 6752357867) ^ (103032 + 103032 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 103032 * (2 : ZMod 6752357867) ^ 103032) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 485174272 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 6752357867) ^ 412131 = 3381244889 := by
        calc
          (2 : ZMod 6752357867) ^ 412131 = (2 : ZMod 6752357867) ^ (206065 + 206065 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 206065 * (2 : ZMod 6752357867) ^ 206065) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3381244889 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 6752357867) ^ 824262 = 6633322847 := by
        calc
          (2 : ZMod 6752357867) ^ 824262 = (2 : ZMod 6752357867) ^ (412131 + 412131) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 412131 * (2 : ZMod 6752357867) ^ 412131 := by rw [pow_add]
          _ = 6633322847 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 6752357867) ^ 1648524 = 5924625191 := by
        calc
          (2 : ZMod 6752357867) ^ 1648524 = (2 : ZMod 6752357867) ^ (824262 + 824262) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 824262 * (2 : ZMod 6752357867) ^ 824262 := by rw [pow_add]
          _ = 5924625191 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 6752357867) ^ 3297049 = 4034631430 := by
        calc
          (2 : ZMod 6752357867) ^ 3297049 = (2 : ZMod 6752357867) ^ (1648524 + 1648524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1648524 * (2 : ZMod 6752357867) ^ 1648524) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 4034631430 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 6752357867) ^ 6594099 = 70107267 := by
        calc
          (2 : ZMod 6752357867) ^ 6594099 = (2 : ZMod 6752357867) ^ (3297049 + 3297049 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 3297049 * (2 : ZMod 6752357867) ^ 3297049) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 70107267 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 6752357867) ^ 13188198 = 1099535723 := by
        calc
          (2 : ZMod 6752357867) ^ 13188198 = (2 : ZMod 6752357867) ^ (6594099 + 6594099) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 6594099 * (2 : ZMod 6752357867) ^ 6594099 := by rw [pow_add]
          _ = 1099535723 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 6752357867) ^ 26376397 = 3693901306 := by
        calc
          (2 : ZMod 6752357867) ^ 26376397 = (2 : ZMod 6752357867) ^ (13188198 + 13188198 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 13188198 * (2 : ZMod 6752357867) ^ 13188198) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3693901306 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 6752357867) ^ 52752795 = 1296702870 := by
        calc
          (2 : ZMod 6752357867) ^ 52752795 = (2 : ZMod 6752357867) ^ (26376397 + 26376397 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 26376397 * (2 : ZMod 6752357867) ^ 26376397) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 1296702870 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 6752357867) ^ 105505591 = 5925263273 := by
        calc
          (2 : ZMod 6752357867) ^ 105505591 = (2 : ZMod 6752357867) ^ (52752795 + 52752795 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 52752795 * (2 : ZMod 6752357867) ^ 52752795) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 5925263273 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 6752357867) ^ 211011183 = 6731132735 := by
        calc
          (2 : ZMod 6752357867) ^ 211011183 = (2 : ZMod 6752357867) ^ (105505591 + 105505591 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 105505591 * (2 : ZMod 6752357867) ^ 105505591) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 6731132735 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 6752357867) ^ 422022366 = 2416246918 := by
        calc
          (2 : ZMod 6752357867) ^ 422022366 = (2 : ZMod 6752357867) ^ (211011183 + 211011183) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 211011183 * (2 : ZMod 6752357867) ^ 211011183 := by rw [pow_add]
          _ = 2416246918 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 6752357867) ^ 844044733 = 5494232263 := by
        calc
          (2 : ZMod 6752357867) ^ 844044733 = (2 : ZMod 6752357867) ^ (422022366 + 422022366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 422022366 * (2 : ZMod 6752357867) ^ 422022366) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 5494232263 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 6752357867) ^ 1688089466 = 1946193196 := by
        calc
          (2 : ZMod 6752357867) ^ 1688089466 = (2 : ZMod 6752357867) ^ (844044733 + 844044733) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 844044733 * (2 : ZMod 6752357867) ^ 844044733 := by rw [pow_add]
          _ = 1946193196 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 6752357867) ^ 3376178933 = 6752357866 := by
        calc
          (2 : ZMod 6752357867) ^ 3376178933 = (2 : ZMod 6752357867) ^ (1688089466 + 1688089466 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1688089466 * (2 : ZMod 6752357867) ^ 1688089466) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 6752357866 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 6752357867) ^ 6752357866 = 1 := by
        calc
          (2 : ZMod 6752357867) ^ 6752357866 = (2 : ZMod 6752357867) ^ (3376178933 + 3376178933) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 3376178933 * (2 : ZMod 6752357867) ^ 3376178933 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3376178933, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3376178933, 1)] : List FactorBlock).map factorBlockValue).prod = 6752357867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_3376178933) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 6752357867) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 6752357867) ^ 3 = 8 := by
        calc
          (2 : ZMod 6752357867) ^ 3 = (2 : ZMod 6752357867) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1 * (2 : ZMod 6752357867) ^ 1) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 6752357867) ^ 6 = 64 := by
        calc
          (2 : ZMod 6752357867) ^ 6 = (2 : ZMod 6752357867) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 3 * (2 : ZMod 6752357867) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 6752357867) ^ 12 = 4096 := by
        calc
          (2 : ZMod 6752357867) ^ 12 = (2 : ZMod 6752357867) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 6 * (2 : ZMod 6752357867) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 6752357867) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 6752357867) ^ 25 = (2 : ZMod 6752357867) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 12 * (2 : ZMod 6752357867) ^ 12) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 6752357867) ^ 50 = 5003741177 := by
        calc
          (2 : ZMod 6752357867) ^ 50 = (2 : ZMod 6752357867) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 25 * (2 : ZMod 6752357867) ^ 25 := by rw [pow_add]
          _ = 5003741177 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 6752357867) ^ 100 = 1084863388 := by
        calc
          (2 : ZMod 6752357867) ^ 100 = (2 : ZMod 6752357867) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 50 * (2 : ZMod 6752357867) ^ 50 := by rw [pow_add]
          _ = 1084863388 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 6752357867) ^ 201 = 3482637286 := by
        calc
          (2 : ZMod 6752357867) ^ 201 = (2 : ZMod 6752357867) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 100 * (2 : ZMod 6752357867) ^ 100) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3482637286 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 6752357867) ^ 402 = 2233321312 := by
        calc
          (2 : ZMod 6752357867) ^ 402 = (2 : ZMod 6752357867) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 201 * (2 : ZMod 6752357867) ^ 201 := by rw [pow_add]
          _ = 2233321312 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 6752357867) ^ 804 = 6022241324 := by
        calc
          (2 : ZMod 6752357867) ^ 804 = (2 : ZMod 6752357867) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 402 * (2 : ZMod 6752357867) ^ 402 := by rw [pow_add]
          _ = 6022241324 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 6752357867) ^ 1609 = 1920923444 := by
        calc
          (2 : ZMod 6752357867) ^ 1609 = (2 : ZMod 6752357867) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 804 * (2 : ZMod 6752357867) ^ 804) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 1920923444 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 6752357867) ^ 3219 = 123977800 := by
        calc
          (2 : ZMod 6752357867) ^ 3219 = (2 : ZMod 6752357867) ^ (1609 + 1609 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1609 * (2 : ZMod 6752357867) ^ 1609) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 123977800 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 6752357867) ^ 6439 = 2789639790 := by
        calc
          (2 : ZMod 6752357867) ^ 6439 = (2 : ZMod 6752357867) ^ (3219 + 3219 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 3219 * (2 : ZMod 6752357867) ^ 3219) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 2789639790 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 6752357867) ^ 12879 = 3813764159 := by
        calc
          (2 : ZMod 6752357867) ^ 12879 = (2 : ZMod 6752357867) ^ (6439 + 6439 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 6439 * (2 : ZMod 6752357867) ^ 6439) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3813764159 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 6752357867) ^ 25758 = 5758147309 := by
        calc
          (2 : ZMod 6752357867) ^ 25758 = (2 : ZMod 6752357867) ^ (12879 + 12879) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 12879 * (2 : ZMod 6752357867) ^ 12879 := by rw [pow_add]
          _ = 5758147309 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 6752357867) ^ 51516 = 4533583568 := by
        calc
          (2 : ZMod 6752357867) ^ 51516 = (2 : ZMod 6752357867) ^ (25758 + 25758) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 25758 * (2 : ZMod 6752357867) ^ 25758 := by rw [pow_add]
          _ = 4533583568 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 6752357867) ^ 103032 = 79766787 := by
        calc
          (2 : ZMod 6752357867) ^ 103032 = (2 : ZMod 6752357867) ^ (51516 + 51516) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 51516 * (2 : ZMod 6752357867) ^ 51516 := by rw [pow_add]
          _ = 79766787 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 6752357867) ^ 206065 = 485174272 := by
        calc
          (2 : ZMod 6752357867) ^ 206065 = (2 : ZMod 6752357867) ^ (103032 + 103032 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 103032 * (2 : ZMod 6752357867) ^ 103032) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 485174272 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 6752357867) ^ 412131 = 3381244889 := by
        calc
          (2 : ZMod 6752357867) ^ 412131 = (2 : ZMod 6752357867) ^ (206065 + 206065 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 206065 * (2 : ZMod 6752357867) ^ 206065) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3381244889 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 6752357867) ^ 824262 = 6633322847 := by
        calc
          (2 : ZMod 6752357867) ^ 824262 = (2 : ZMod 6752357867) ^ (412131 + 412131) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 412131 * (2 : ZMod 6752357867) ^ 412131 := by rw [pow_add]
          _ = 6633322847 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 6752357867) ^ 1648524 = 5924625191 := by
        calc
          (2 : ZMod 6752357867) ^ 1648524 = (2 : ZMod 6752357867) ^ (824262 + 824262) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 824262 * (2 : ZMod 6752357867) ^ 824262 := by rw [pow_add]
          _ = 5924625191 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 6752357867) ^ 3297049 = 4034631430 := by
        calc
          (2 : ZMod 6752357867) ^ 3297049 = (2 : ZMod 6752357867) ^ (1648524 + 1648524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1648524 * (2 : ZMod 6752357867) ^ 1648524) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 4034631430 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 6752357867) ^ 6594099 = 70107267 := by
        calc
          (2 : ZMod 6752357867) ^ 6594099 = (2 : ZMod 6752357867) ^ (3297049 + 3297049 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 3297049 * (2 : ZMod 6752357867) ^ 3297049) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 70107267 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 6752357867) ^ 13188198 = 1099535723 := by
        calc
          (2 : ZMod 6752357867) ^ 13188198 = (2 : ZMod 6752357867) ^ (6594099 + 6594099) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 6594099 * (2 : ZMod 6752357867) ^ 6594099 := by rw [pow_add]
          _ = 1099535723 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 6752357867) ^ 26376397 = 3693901306 := by
        calc
          (2 : ZMod 6752357867) ^ 26376397 = (2 : ZMod 6752357867) ^ (13188198 + 13188198 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 13188198 * (2 : ZMod 6752357867) ^ 13188198) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 3693901306 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 6752357867) ^ 52752795 = 1296702870 := by
        calc
          (2 : ZMod 6752357867) ^ 52752795 = (2 : ZMod 6752357867) ^ (26376397 + 26376397 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 26376397 * (2 : ZMod 6752357867) ^ 26376397) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 1296702870 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 6752357867) ^ 105505591 = 5925263273 := by
        calc
          (2 : ZMod 6752357867) ^ 105505591 = (2 : ZMod 6752357867) ^ (52752795 + 52752795 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 52752795 * (2 : ZMod 6752357867) ^ 52752795) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 5925263273 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 6752357867) ^ 211011183 = 6731132735 := by
        calc
          (2 : ZMod 6752357867) ^ 211011183 = (2 : ZMod 6752357867) ^ (105505591 + 105505591 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 105505591 * (2 : ZMod 6752357867) ^ 105505591) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 6731132735 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 6752357867) ^ 422022366 = 2416246918 := by
        calc
          (2 : ZMod 6752357867) ^ 422022366 = (2 : ZMod 6752357867) ^ (211011183 + 211011183) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 211011183 * (2 : ZMod 6752357867) ^ 211011183 := by rw [pow_add]
          _ = 2416246918 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 6752357867) ^ 844044733 = 5494232263 := by
        calc
          (2 : ZMod 6752357867) ^ 844044733 = (2 : ZMod 6752357867) ^ (422022366 + 422022366 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 422022366 * (2 : ZMod 6752357867) ^ 422022366) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 5494232263 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 6752357867) ^ 1688089466 = 1946193196 := by
        calc
          (2 : ZMod 6752357867) ^ 1688089466 = (2 : ZMod 6752357867) ^ (844044733 + 844044733) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 844044733 * (2 : ZMod 6752357867) ^ 844044733 := by rw [pow_add]
          _ = 1946193196 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 6752357867) ^ 3376178933 = 6752357866 := by
        calc
          (2 : ZMod 6752357867) ^ 3376178933 = (2 : ZMod 6752357867) ^ (1688089466 + 1688089466 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = ((2 : ZMod 6752357867) ^ 1688089466 * (2 : ZMod 6752357867) ^ 1688089466) * (2 : ZMod 6752357867) := by rw [pow_succ, pow_add]
          _ = 6752357866 := by rw [factor_0_30]; decide
      change (2 : ZMod 6752357867) ^ 3376178933 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (2 : ZMod 6752357867) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 6752357867) ^ 2 = 4 := by
        calc
          (2 : ZMod 6752357867) ^ 2 = (2 : ZMod 6752357867) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6752357867) ^ n) (by norm_num)
          _ = (2 : ZMod 6752357867) ^ 1 * (2 : ZMod 6752357867) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      change (2 : ZMod 6752357867) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_6752357867

end TotientTailPeriodKiller
end Erdos249257
