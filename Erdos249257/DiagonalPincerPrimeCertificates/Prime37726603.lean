import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_37726603 : Nat.Prime 37726603 := by
  apply lucas_primality 37726603 (2 : ZMod 37726603)
  ·
      have fermat_0 : (2 : ZMod 37726603) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 37726603) ^ 2 = 4 := by
        calc
          (2 : ZMod 37726603) ^ 2 = (2 : ZMod 37726603) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1 * (2 : ZMod 37726603) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 37726603) ^ 4 = 16 := by
        calc
          (2 : ZMod 37726603) ^ 4 = (2 : ZMod 37726603) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 2 * (2 : ZMod 37726603) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 37726603) ^ 8 = 256 := by
        calc
          (2 : ZMod 37726603) ^ 8 = (2 : ZMod 37726603) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 4 * (2 : ZMod 37726603) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 37726603) ^ 17 = 131072 := by
        calc
          (2 : ZMod 37726603) ^ 17 = (2 : ZMod 37726603) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 8 * (2 : ZMod 37726603) ^ 8) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 37726603) ^ 35 = 28529638 := by
        calc
          (2 : ZMod 37726603) ^ 35 = (2 : ZMod 37726603) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 17 * (2 : ZMod 37726603) ^ 17) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 28529638 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 37726603) ^ 71 = 16700873 := by
        calc
          (2 : ZMod 37726603) ^ 71 = (2 : ZMod 37726603) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 35 * (2 : ZMod 37726603) ^ 35) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 16700873 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 37726603) ^ 143 = 14374444 := by
        calc
          (2 : ZMod 37726603) ^ 143 = (2 : ZMod 37726603) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 71 * (2 : ZMod 37726603) ^ 71) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 14374444 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 37726603) ^ 287 = 31669505 := by
        calc
          (2 : ZMod 37726603) ^ 287 = (2 : ZMod 37726603) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 143 * (2 : ZMod 37726603) ^ 143) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 31669505 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 37726603) ^ 575 = 25412519 := by
        calc
          (2 : ZMod 37726603) ^ 575 = (2 : ZMod 37726603) ^ (287 + 287 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 287 * (2 : ZMod 37726603) ^ 287) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 25412519 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 37726603) ^ 1151 = 33262776 := by
        calc
          (2 : ZMod 37726603) ^ 1151 = (2 : ZMod 37726603) ^ (575 + 575 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 575 * (2 : ZMod 37726603) ^ 575) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 33262776 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 37726603) ^ 2302 = 31118846 := by
        calc
          (2 : ZMod 37726603) ^ 2302 = (2 : ZMod 37726603) ^ (1151 + 1151) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1151 * (2 : ZMod 37726603) ^ 1151 := by rw [pow_add]
          _ = 31118846 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 37726603) ^ 4605 = 4889867 := by
        calc
          (2 : ZMod 37726603) ^ 4605 = (2 : ZMod 37726603) ^ (2302 + 2302 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 2302 * (2 : ZMod 37726603) ^ 2302) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 4889867 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 37726603) ^ 9210 = 17835716 := by
        calc
          (2 : ZMod 37726603) ^ 9210 = (2 : ZMod 37726603) ^ (4605 + 4605) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 4605 * (2 : ZMod 37726603) ^ 4605 := by rw [pow_add]
          _ = 17835716 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 37726603) ^ 18421 = 23000188 := by
        calc
          (2 : ZMod 37726603) ^ 18421 = (2 : ZMod 37726603) ^ (9210 + 9210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 9210 * (2 : ZMod 37726603) ^ 9210) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 23000188 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 37726603) ^ 36842 = 33606452 := by
        calc
          (2 : ZMod 37726603) ^ 36842 = (2 : ZMod 37726603) ^ (18421 + 18421) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 18421 * (2 : ZMod 37726603) ^ 18421 := by rw [pow_add]
          _ = 33606452 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 37726603) ^ 73684 = 31070509 := by
        calc
          (2 : ZMod 37726603) ^ 73684 = (2 : ZMod 37726603) ^ (36842 + 36842) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 36842 * (2 : ZMod 37726603) ^ 36842 := by rw [pow_add]
          _ = 31070509 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 37726603) ^ 147369 = 22638677 := by
        calc
          (2 : ZMod 37726603) ^ 147369 = (2 : ZMod 37726603) ^ (73684 + 73684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 73684 * (2 : ZMod 37726603) ^ 73684) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 22638677 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 37726603) ^ 294739 = 1163045 := by
        calc
          (2 : ZMod 37726603) ^ 294739 = (2 : ZMod 37726603) ^ (147369 + 147369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 147369 * (2 : ZMod 37726603) ^ 147369) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 1163045 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 37726603) ^ 589478 = 24048063 := by
        calc
          (2 : ZMod 37726603) ^ 589478 = (2 : ZMod 37726603) ^ (294739 + 294739) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 294739 * (2 : ZMod 37726603) ^ 294739 := by rw [pow_add]
          _ = 24048063 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 37726603) ^ 1178956 = 9815310 := by
        calc
          (2 : ZMod 37726603) ^ 1178956 = (2 : ZMod 37726603) ^ (589478 + 589478) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 589478 * (2 : ZMod 37726603) ^ 589478 := by rw [pow_add]
          _ = 9815310 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 37726603) ^ 2357912 = 34731371 := by
        calc
          (2 : ZMod 37726603) ^ 2357912 = (2 : ZMod 37726603) ^ (1178956 + 1178956) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1178956 * (2 : ZMod 37726603) ^ 1178956 := by rw [pow_add]
          _ = 34731371 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 37726603) ^ 4715825 = 19354245 := by
        calc
          (2 : ZMod 37726603) ^ 4715825 = (2 : ZMod 37726603) ^ (2357912 + 2357912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 2357912 * (2 : ZMod 37726603) ^ 2357912) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 19354245 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 37726603) ^ 9431650 = 37411879 := by
        calc
          (2 : ZMod 37726603) ^ 9431650 = (2 : ZMod 37726603) ^ (4715825 + 4715825) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 4715825 * (2 : ZMod 37726603) ^ 4715825 := by rw [pow_add]
          _ = 37411879 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 37726603) ^ 18863301 = 37726602 := by
        calc
          (2 : ZMod 37726603) ^ 18863301 = (2 : ZMod 37726603) ^ (9431650 + 9431650 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 9431650 * (2 : ZMod 37726603) ^ 9431650) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 37726602 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 37726603) ^ 37726602 = 1 := by
        calc
          (2 : ZMod 37726603) ^ 37726602 = (2 : ZMod 37726603) ^ (18863301 + 18863301) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 18863301 * (2 : ZMod 37726603) ^ 18863301 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (6287767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (6287767, 1)] : List FactorBlock).map factorBlockValue).prod = 37726603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 37726603) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 37726603) ^ 2 = 4 := by
        calc
          (2 : ZMod 37726603) ^ 2 = (2 : ZMod 37726603) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1 * (2 : ZMod 37726603) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 37726603) ^ 4 = 16 := by
        calc
          (2 : ZMod 37726603) ^ 4 = (2 : ZMod 37726603) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 2 * (2 : ZMod 37726603) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 37726603) ^ 8 = 256 := by
        calc
          (2 : ZMod 37726603) ^ 8 = (2 : ZMod 37726603) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 4 * (2 : ZMod 37726603) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 37726603) ^ 17 = 131072 := by
        calc
          (2 : ZMod 37726603) ^ 17 = (2 : ZMod 37726603) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 8 * (2 : ZMod 37726603) ^ 8) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 37726603) ^ 35 = 28529638 := by
        calc
          (2 : ZMod 37726603) ^ 35 = (2 : ZMod 37726603) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 17 * (2 : ZMod 37726603) ^ 17) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 28529638 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 37726603) ^ 71 = 16700873 := by
        calc
          (2 : ZMod 37726603) ^ 71 = (2 : ZMod 37726603) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 35 * (2 : ZMod 37726603) ^ 35) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 16700873 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 37726603) ^ 143 = 14374444 := by
        calc
          (2 : ZMod 37726603) ^ 143 = (2 : ZMod 37726603) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 71 * (2 : ZMod 37726603) ^ 71) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 14374444 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 37726603) ^ 287 = 31669505 := by
        calc
          (2 : ZMod 37726603) ^ 287 = (2 : ZMod 37726603) ^ (143 + 143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 143 * (2 : ZMod 37726603) ^ 143) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 31669505 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 37726603) ^ 575 = 25412519 := by
        calc
          (2 : ZMod 37726603) ^ 575 = (2 : ZMod 37726603) ^ (287 + 287 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 287 * (2 : ZMod 37726603) ^ 287) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 25412519 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 37726603) ^ 1151 = 33262776 := by
        calc
          (2 : ZMod 37726603) ^ 1151 = (2 : ZMod 37726603) ^ (575 + 575 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 575 * (2 : ZMod 37726603) ^ 575) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 33262776 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 37726603) ^ 2302 = 31118846 := by
        calc
          (2 : ZMod 37726603) ^ 2302 = (2 : ZMod 37726603) ^ (1151 + 1151) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1151 * (2 : ZMod 37726603) ^ 1151 := by rw [pow_add]
          _ = 31118846 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 37726603) ^ 4605 = 4889867 := by
        calc
          (2 : ZMod 37726603) ^ 4605 = (2 : ZMod 37726603) ^ (2302 + 2302 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 2302 * (2 : ZMod 37726603) ^ 2302) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 4889867 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 37726603) ^ 9210 = 17835716 := by
        calc
          (2 : ZMod 37726603) ^ 9210 = (2 : ZMod 37726603) ^ (4605 + 4605) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 4605 * (2 : ZMod 37726603) ^ 4605 := by rw [pow_add]
          _ = 17835716 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 37726603) ^ 18421 = 23000188 := by
        calc
          (2 : ZMod 37726603) ^ 18421 = (2 : ZMod 37726603) ^ (9210 + 9210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 9210 * (2 : ZMod 37726603) ^ 9210) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 23000188 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 37726603) ^ 36842 = 33606452 := by
        calc
          (2 : ZMod 37726603) ^ 36842 = (2 : ZMod 37726603) ^ (18421 + 18421) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 18421 * (2 : ZMod 37726603) ^ 18421 := by rw [pow_add]
          _ = 33606452 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 37726603) ^ 73684 = 31070509 := by
        calc
          (2 : ZMod 37726603) ^ 73684 = (2 : ZMod 37726603) ^ (36842 + 36842) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 36842 * (2 : ZMod 37726603) ^ 36842 := by rw [pow_add]
          _ = 31070509 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 37726603) ^ 147369 = 22638677 := by
        calc
          (2 : ZMod 37726603) ^ 147369 = (2 : ZMod 37726603) ^ (73684 + 73684 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 73684 * (2 : ZMod 37726603) ^ 73684) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 22638677 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 37726603) ^ 294739 = 1163045 := by
        calc
          (2 : ZMod 37726603) ^ 294739 = (2 : ZMod 37726603) ^ (147369 + 147369 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 147369 * (2 : ZMod 37726603) ^ 147369) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 1163045 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 37726603) ^ 589478 = 24048063 := by
        calc
          (2 : ZMod 37726603) ^ 589478 = (2 : ZMod 37726603) ^ (294739 + 294739) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 294739 * (2 : ZMod 37726603) ^ 294739 := by rw [pow_add]
          _ = 24048063 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 37726603) ^ 1178956 = 9815310 := by
        calc
          (2 : ZMod 37726603) ^ 1178956 = (2 : ZMod 37726603) ^ (589478 + 589478) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 589478 * (2 : ZMod 37726603) ^ 589478 := by rw [pow_add]
          _ = 9815310 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 37726603) ^ 2357912 = 34731371 := by
        calc
          (2 : ZMod 37726603) ^ 2357912 = (2 : ZMod 37726603) ^ (1178956 + 1178956) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1178956 * (2 : ZMod 37726603) ^ 1178956 := by rw [pow_add]
          _ = 34731371 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 37726603) ^ 4715825 = 19354245 := by
        calc
          (2 : ZMod 37726603) ^ 4715825 = (2 : ZMod 37726603) ^ (2357912 + 2357912 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 2357912 * (2 : ZMod 37726603) ^ 2357912) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 19354245 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 37726603) ^ 9431650 = 37411879 := by
        calc
          (2 : ZMod 37726603) ^ 9431650 = (2 : ZMod 37726603) ^ (4715825 + 4715825) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 4715825 * (2 : ZMod 37726603) ^ 4715825 := by rw [pow_add]
          _ = 37411879 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 37726603) ^ 18863301 = 37726602 := by
        calc
          (2 : ZMod 37726603) ^ 18863301 = (2 : ZMod 37726603) ^ (9431650 + 9431650 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 9431650 * (2 : ZMod 37726603) ^ 9431650) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 37726602 := by rw [factor_0_23]; decide
      change (2 : ZMod 37726603) ^ 18863301 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (2 : ZMod 37726603) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 37726603) ^ 2 = 4 := by
        calc
          (2 : ZMod 37726603) ^ 2 = (2 : ZMod 37726603) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1 * (2 : ZMod 37726603) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 37726603) ^ 5 = 32 := by
        calc
          (2 : ZMod 37726603) ^ 5 = (2 : ZMod 37726603) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 2 * (2 : ZMod 37726603) ^ 2) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 37726603) ^ 11 = 2048 := by
        calc
          (2 : ZMod 37726603) ^ 11 = (2 : ZMod 37726603) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 5 * (2 : ZMod 37726603) ^ 5) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 37726603) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 37726603) ^ 23 = (2 : ZMod 37726603) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 11 * (2 : ZMod 37726603) ^ 11) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 37726603) ^ 47 = 18107757 := by
        calc
          (2 : ZMod 37726603) ^ 47 = (2 : ZMod 37726603) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 23 * (2 : ZMod 37726603) ^ 23) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 18107757 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 37726603) ^ 95 = 31386276 := by
        calc
          (2 : ZMod 37726603) ^ 95 = (2 : ZMod 37726603) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 47 * (2 : ZMod 37726603) ^ 47) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 31386276 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 37726603) ^ 191 = 27467734 := by
        calc
          (2 : ZMod 37726603) ^ 191 = (2 : ZMod 37726603) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 95 * (2 : ZMod 37726603) ^ 95) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 27467734 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 37726603) ^ 383 = 33394965 := by
        calc
          (2 : ZMod 37726603) ^ 383 = (2 : ZMod 37726603) ^ (191 + 191 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 191 * (2 : ZMod 37726603) ^ 191) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 33394965 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 37726603) ^ 767 = 13967827 := by
        calc
          (2 : ZMod 37726603) ^ 767 = (2 : ZMod 37726603) ^ (383 + 383 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 383 * (2 : ZMod 37726603) ^ 383) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 13967827 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 37726603) ^ 1535 = 12724926 := by
        calc
          (2 : ZMod 37726603) ^ 1535 = (2 : ZMod 37726603) ^ (767 + 767 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 767 * (2 : ZMod 37726603) ^ 767) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 12724926 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 37726603) ^ 3070 = 29831386 := by
        calc
          (2 : ZMod 37726603) ^ 3070 = (2 : ZMod 37726603) ^ (1535 + 1535) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 1535 * (2 : ZMod 37726603) ^ 1535 := by rw [pow_add]
          _ = 29831386 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 37726603) ^ 6140 = 30318088 := by
        calc
          (2 : ZMod 37726603) ^ 6140 = (2 : ZMod 37726603) ^ (3070 + 3070) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 3070 * (2 : ZMod 37726603) ^ 3070 := by rw [pow_add]
          _ = 30318088 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 37726603) ^ 12280 = 36576514 := by
        calc
          (2 : ZMod 37726603) ^ 12280 = (2 : ZMod 37726603) ^ (6140 + 6140) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 6140 * (2 : ZMod 37726603) ^ 6140 := by rw [pow_add]
          _ = 36576514 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 37726603) ^ 24561 = 20013482 := by
        calc
          (2 : ZMod 37726603) ^ 24561 = (2 : ZMod 37726603) ^ (12280 + 12280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 12280 * (2 : ZMod 37726603) ^ 12280) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 20013482 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 37726603) ^ 49123 = 7106866 := by
        calc
          (2 : ZMod 37726603) ^ 49123 = (2 : ZMod 37726603) ^ (24561 + 24561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 24561 * (2 : ZMod 37726603) ^ 24561) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 7106866 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 37726603) ^ 98246 = 35957425 := by
        calc
          (2 : ZMod 37726603) ^ 98246 = (2 : ZMod 37726603) ^ (49123 + 49123) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 49123 * (2 : ZMod 37726603) ^ 49123 := by rw [pow_add]
          _ = 35957425 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 37726603) ^ 196492 = 3177789 := by
        calc
          (2 : ZMod 37726603) ^ 196492 = (2 : ZMod 37726603) ^ (98246 + 98246) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 98246 * (2 : ZMod 37726603) ^ 98246 := by rw [pow_add]
          _ = 3177789 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 37726603) ^ 392985 = 13027213 := by
        calc
          (2 : ZMod 37726603) ^ 392985 = (2 : ZMod 37726603) ^ (196492 + 196492 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 196492 * (2 : ZMod 37726603) ^ 196492) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 13027213 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 37726603) ^ 785970 = 21683656 := by
        calc
          (2 : ZMod 37726603) ^ 785970 = (2 : ZMod 37726603) ^ (392985 + 392985) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 392985 * (2 : ZMod 37726603) ^ 392985 := by rw [pow_add]
          _ = 21683656 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 37726603) ^ 1571941 = 37561984 := by
        calc
          (2 : ZMod 37726603) ^ 1571941 = (2 : ZMod 37726603) ^ (785970 + 785970 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 785970 * (2 : ZMod 37726603) ^ 785970) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 37561984 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 37726603) ^ 3143883 = 23428414 := by
        calc
          (2 : ZMod 37726603) ^ 3143883 = (2 : ZMod 37726603) ^ (1571941 + 1571941 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 1571941 * (2 : ZMod 37726603) ^ 1571941) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 23428414 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 37726603) ^ 6287767 = 21237802 := by
        calc
          (2 : ZMod 37726603) ^ 6287767 = (2 : ZMod 37726603) ^ (3143883 + 3143883 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 3143883 * (2 : ZMod 37726603) ^ 3143883) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 21237802 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 37726603) ^ 12575534 = 21237801 := by
        calc
          (2 : ZMod 37726603) ^ 12575534 = (2 : ZMod 37726603) ^ (6287767 + 6287767) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 6287767 * (2 : ZMod 37726603) ^ 6287767 := by rw [pow_add]
          _ = 21237801 := by rw [factor_1_22]; decide
      change (2 : ZMod 37726603) ^ 12575534 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (2 : ZMod 37726603) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 37726603) ^ 3 = 8 := by
        calc
          (2 : ZMod 37726603) ^ 3 = (2 : ZMod 37726603) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = ((2 : ZMod 37726603) ^ 1 * (2 : ZMod 37726603) ^ 1) * (2 : ZMod 37726603) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 37726603) ^ 6 = 64 := by
        calc
          (2 : ZMod 37726603) ^ 6 = (2 : ZMod 37726603) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 37726603) ^ n) (by norm_num)
          _ = (2 : ZMod 37726603) ^ 3 * (2 : ZMod 37726603) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      change (2 : ZMod 37726603) ^ 6 ≠ 1
      rw [factor_2_2]
      decide

#print axioms prime_lucas_37726603

end TotientTailPeriodKiller
end Erdos249257
