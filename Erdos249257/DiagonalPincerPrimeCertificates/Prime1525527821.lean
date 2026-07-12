import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime76276391

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1525527821 : Nat.Prime 1525527821 := by
  apply lucas_primality 1525527821 (3 : ZMod 1525527821)
  ·
      have fermat_0 : (3 : ZMod 1525527821) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 1525527821) ^ 2 = 9 := by
        calc
          (3 : ZMod 1525527821) ^ 2 = (3 : ZMod 1525527821) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 1 * (3 : ZMod 1525527821) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 1525527821) ^ 5 = 243 := by
        calc
          (3 : ZMod 1525527821) ^ 5 = (3 : ZMod 1525527821) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2 * (3 : ZMod 1525527821) ^ 2) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 1525527821) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1525527821) ^ 11 = (3 : ZMod 1525527821) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 5 * (3 : ZMod 1525527821) ^ 5) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 1525527821) ^ 22 = 870503189 := by
        calc
          (3 : ZMod 1525527821) ^ 22 = (3 : ZMod 1525527821) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 11 * (3 : ZMod 1525527821) ^ 11 := by rw [pow_add]
          _ = 870503189 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 1525527821) ^ 45 = 1170432401 := by
        calc
          (3 : ZMod 1525527821) ^ 45 = (3 : ZMod 1525527821) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 22 * (3 : ZMod 1525527821) ^ 22) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1170432401 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 1525527821) ^ 90 = 497075293 := by
        calc
          (3 : ZMod 1525527821) ^ 90 = (3 : ZMod 1525527821) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 45 * (3 : ZMod 1525527821) ^ 45 := by rw [pow_add]
          _ = 497075293 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 1525527821) ^ 181 = 1149498579 := by
        calc
          (3 : ZMod 1525527821) ^ 181 = (3 : ZMod 1525527821) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 90 * (3 : ZMod 1525527821) ^ 90) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1149498579 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 1525527821) ^ 363 = 1135973152 := by
        calc
          (3 : ZMod 1525527821) ^ 363 = (3 : ZMod 1525527821) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 181 * (3 : ZMod 1525527821) ^ 181) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1135973152 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 1525527821) ^ 727 = 240647635 := by
        calc
          (3 : ZMod 1525527821) ^ 727 = (3 : ZMod 1525527821) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 363 * (3 : ZMod 1525527821) ^ 363) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 240647635 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 1525527821) ^ 1454 = 1043452892 := by
        calc
          (3 : ZMod 1525527821) ^ 1454 = (3 : ZMod 1525527821) ^ (727 + 727) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 727 * (3 : ZMod 1525527821) ^ 727 := by rw [pow_add]
          _ = 1043452892 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 1525527821) ^ 2909 = 355288836 := by
        calc
          (3 : ZMod 1525527821) ^ 2909 = (3 : ZMod 1525527821) ^ (1454 + 1454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 1454 * (3 : ZMod 1525527821) ^ 1454) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 355288836 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 1525527821) ^ 5819 = 1392239346 := by
        calc
          (3 : ZMod 1525527821) ^ 5819 = (3 : ZMod 1525527821) ^ (2909 + 2909 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2909 * (3 : ZMod 1525527821) ^ 2909) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1392239346 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 1525527821) ^ 11638 = 1105723240 := by
        calc
          (3 : ZMod 1525527821) ^ 11638 = (3 : ZMod 1525527821) ^ (5819 + 5819) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 5819 * (3 : ZMod 1525527821) ^ 5819 := by rw [pow_add]
          _ = 1105723240 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 1525527821) ^ 23277 = 540325830 := by
        calc
          (3 : ZMod 1525527821) ^ 23277 = (3 : ZMod 1525527821) ^ (11638 + 11638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 11638 * (3 : ZMod 1525527821) ^ 11638) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 540325830 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 1525527821) ^ 46555 = 1367286347 := by
        calc
          (3 : ZMod 1525527821) ^ 46555 = (3 : ZMod 1525527821) ^ (23277 + 23277 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 23277 * (3 : ZMod 1525527821) ^ 23277) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1367286347 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 1525527821) ^ 93110 = 1093927667 := by
        calc
          (3 : ZMod 1525527821) ^ 93110 = (3 : ZMod 1525527821) ^ (46555 + 46555) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 46555 * (3 : ZMod 1525527821) ^ 46555 := by rw [pow_add]
          _ = 1093927667 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 1525527821) ^ 186221 = 1324561690 := by
        calc
          (3 : ZMod 1525527821) ^ 186221 = (3 : ZMod 1525527821) ^ (93110 + 93110 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 93110 * (3 : ZMod 1525527821) ^ 93110) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1324561690 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 1525527821) ^ 372443 = 1119623278 := by
        calc
          (3 : ZMod 1525527821) ^ 372443 = (3 : ZMod 1525527821) ^ (186221 + 186221 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 186221 * (3 : ZMod 1525527821) ^ 186221) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1119623278 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 1525527821) ^ 744886 = 1393829911 := by
        calc
          (3 : ZMod 1525527821) ^ 744886 = (3 : ZMod 1525527821) ^ (372443 + 372443) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 372443 * (3 : ZMod 1525527821) ^ 372443 := by rw [pow_add]
          _ = 1393829911 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 1525527821) ^ 1489773 = 1317705174 := by
        calc
          (3 : ZMod 1525527821) ^ 1489773 = (3 : ZMod 1525527821) ^ (744886 + 744886 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 744886 * (3 : ZMod 1525527821) ^ 744886) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1317705174 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 1525527821) ^ 2979546 = 157892971 := by
        calc
          (3 : ZMod 1525527821) ^ 2979546 = (3 : ZMod 1525527821) ^ (1489773 + 1489773) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 1489773 * (3 : ZMod 1525527821) ^ 1489773 := by rw [pow_add]
          _ = 157892971 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 1525527821) ^ 5959093 = 1206495535 := by
        calc
          (3 : ZMod 1525527821) ^ 5959093 = (3 : ZMod 1525527821) ^ (2979546 + 2979546 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2979546 * (3 : ZMod 1525527821) ^ 2979546) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1206495535 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 1525527821) ^ 11918186 = 352756056 := by
        calc
          (3 : ZMod 1525527821) ^ 11918186 = (3 : ZMod 1525527821) ^ (5959093 + 5959093) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 5959093 * (3 : ZMod 1525527821) ^ 5959093 := by rw [pow_add]
          _ = 352756056 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 1525527821) ^ 23836372 = 548274004 := by
        calc
          (3 : ZMod 1525527821) ^ 23836372 = (3 : ZMod 1525527821) ^ (11918186 + 11918186) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 11918186 * (3 : ZMod 1525527821) ^ 11918186 := by rw [pow_add]
          _ = 548274004 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 1525527821) ^ 47672744 = 461583449 := by
        calc
          (3 : ZMod 1525527821) ^ 47672744 = (3 : ZMod 1525527821) ^ (23836372 + 23836372) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 23836372 * (3 : ZMod 1525527821) ^ 23836372 := by rw [pow_add]
          _ = 461583449 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 1525527821) ^ 95345488 = 903760457 := by
        calc
          (3 : ZMod 1525527821) ^ 95345488 = (3 : ZMod 1525527821) ^ (47672744 + 47672744) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 47672744 * (3 : ZMod 1525527821) ^ 47672744 := by rw [pow_add]
          _ = 903760457 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 1525527821) ^ 190690977 = 318540285 := by
        calc
          (3 : ZMod 1525527821) ^ 190690977 = (3 : ZMod 1525527821) ^ (95345488 + 95345488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 95345488 * (3 : ZMod 1525527821) ^ 95345488) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 318540285 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 1525527821) ^ 381381955 = 479806009 := by
        calc
          (3 : ZMod 1525527821) ^ 381381955 = (3 : ZMod 1525527821) ^ (190690977 + 190690977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 190690977 * (3 : ZMod 1525527821) ^ 190690977) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 479806009 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 1525527821) ^ 762763910 = 1525527820 := by
        calc
          (3 : ZMod 1525527821) ^ 762763910 = (3 : ZMod 1525527821) ^ (381381955 + 381381955) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 381381955 * (3 : ZMod 1525527821) ^ 381381955 := by rw [pow_add]
          _ = 1525527820 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 1525527821) ^ 1525527820 = 1 := by
        calc
          (3 : ZMod 1525527821) ^ 1525527820 = (3 : ZMod 1525527821) ^ (762763910 + 762763910) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 762763910 * (3 : ZMod 1525527821) ^ 762763910 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (76276391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (76276391, 1)] : List FactorBlock).map factorBlockValue).prod = 1525527821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_76276391) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 1525527821) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 1525527821) ^ 2 = 9 := by
        calc
          (3 : ZMod 1525527821) ^ 2 = (3 : ZMod 1525527821) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 1 * (3 : ZMod 1525527821) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 1525527821) ^ 5 = 243 := by
        calc
          (3 : ZMod 1525527821) ^ 5 = (3 : ZMod 1525527821) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2 * (3 : ZMod 1525527821) ^ 2) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 1525527821) ^ 11 = 177147 := by
        calc
          (3 : ZMod 1525527821) ^ 11 = (3 : ZMod 1525527821) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 5 * (3 : ZMod 1525527821) ^ 5) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 1525527821) ^ 22 = 870503189 := by
        calc
          (3 : ZMod 1525527821) ^ 22 = (3 : ZMod 1525527821) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 11 * (3 : ZMod 1525527821) ^ 11 := by rw [pow_add]
          _ = 870503189 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 1525527821) ^ 45 = 1170432401 := by
        calc
          (3 : ZMod 1525527821) ^ 45 = (3 : ZMod 1525527821) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 22 * (3 : ZMod 1525527821) ^ 22) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1170432401 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 1525527821) ^ 90 = 497075293 := by
        calc
          (3 : ZMod 1525527821) ^ 90 = (3 : ZMod 1525527821) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 45 * (3 : ZMod 1525527821) ^ 45 := by rw [pow_add]
          _ = 497075293 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 1525527821) ^ 181 = 1149498579 := by
        calc
          (3 : ZMod 1525527821) ^ 181 = (3 : ZMod 1525527821) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 90 * (3 : ZMod 1525527821) ^ 90) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1149498579 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 1525527821) ^ 363 = 1135973152 := by
        calc
          (3 : ZMod 1525527821) ^ 363 = (3 : ZMod 1525527821) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 181 * (3 : ZMod 1525527821) ^ 181) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1135973152 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 1525527821) ^ 727 = 240647635 := by
        calc
          (3 : ZMod 1525527821) ^ 727 = (3 : ZMod 1525527821) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 363 * (3 : ZMod 1525527821) ^ 363) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 240647635 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 1525527821) ^ 1454 = 1043452892 := by
        calc
          (3 : ZMod 1525527821) ^ 1454 = (3 : ZMod 1525527821) ^ (727 + 727) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 727 * (3 : ZMod 1525527821) ^ 727 := by rw [pow_add]
          _ = 1043452892 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 1525527821) ^ 2909 = 355288836 := by
        calc
          (3 : ZMod 1525527821) ^ 2909 = (3 : ZMod 1525527821) ^ (1454 + 1454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 1454 * (3 : ZMod 1525527821) ^ 1454) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 355288836 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 1525527821) ^ 5819 = 1392239346 := by
        calc
          (3 : ZMod 1525527821) ^ 5819 = (3 : ZMod 1525527821) ^ (2909 + 2909 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2909 * (3 : ZMod 1525527821) ^ 2909) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1392239346 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 1525527821) ^ 11638 = 1105723240 := by
        calc
          (3 : ZMod 1525527821) ^ 11638 = (3 : ZMod 1525527821) ^ (5819 + 5819) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 5819 * (3 : ZMod 1525527821) ^ 5819 := by rw [pow_add]
          _ = 1105723240 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 1525527821) ^ 23277 = 540325830 := by
        calc
          (3 : ZMod 1525527821) ^ 23277 = (3 : ZMod 1525527821) ^ (11638 + 11638 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 11638 * (3 : ZMod 1525527821) ^ 11638) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 540325830 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 1525527821) ^ 46555 = 1367286347 := by
        calc
          (3 : ZMod 1525527821) ^ 46555 = (3 : ZMod 1525527821) ^ (23277 + 23277 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 23277 * (3 : ZMod 1525527821) ^ 23277) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1367286347 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 1525527821) ^ 93110 = 1093927667 := by
        calc
          (3 : ZMod 1525527821) ^ 93110 = (3 : ZMod 1525527821) ^ (46555 + 46555) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 46555 * (3 : ZMod 1525527821) ^ 46555 := by rw [pow_add]
          _ = 1093927667 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 1525527821) ^ 186221 = 1324561690 := by
        calc
          (3 : ZMod 1525527821) ^ 186221 = (3 : ZMod 1525527821) ^ (93110 + 93110 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 93110 * (3 : ZMod 1525527821) ^ 93110) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1324561690 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 1525527821) ^ 372443 = 1119623278 := by
        calc
          (3 : ZMod 1525527821) ^ 372443 = (3 : ZMod 1525527821) ^ (186221 + 186221 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 186221 * (3 : ZMod 1525527821) ^ 186221) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1119623278 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 1525527821) ^ 744886 = 1393829911 := by
        calc
          (3 : ZMod 1525527821) ^ 744886 = (3 : ZMod 1525527821) ^ (372443 + 372443) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 372443 * (3 : ZMod 1525527821) ^ 372443 := by rw [pow_add]
          _ = 1393829911 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 1525527821) ^ 1489773 = 1317705174 := by
        calc
          (3 : ZMod 1525527821) ^ 1489773 = (3 : ZMod 1525527821) ^ (744886 + 744886 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 744886 * (3 : ZMod 1525527821) ^ 744886) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1317705174 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 1525527821) ^ 2979546 = 157892971 := by
        calc
          (3 : ZMod 1525527821) ^ 2979546 = (3 : ZMod 1525527821) ^ (1489773 + 1489773) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 1489773 * (3 : ZMod 1525527821) ^ 1489773 := by rw [pow_add]
          _ = 157892971 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 1525527821) ^ 5959093 = 1206495535 := by
        calc
          (3 : ZMod 1525527821) ^ 5959093 = (3 : ZMod 1525527821) ^ (2979546 + 2979546 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2979546 * (3 : ZMod 1525527821) ^ 2979546) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1206495535 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 1525527821) ^ 11918186 = 352756056 := by
        calc
          (3 : ZMod 1525527821) ^ 11918186 = (3 : ZMod 1525527821) ^ (5959093 + 5959093) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 5959093 * (3 : ZMod 1525527821) ^ 5959093 := by rw [pow_add]
          _ = 352756056 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 1525527821) ^ 23836372 = 548274004 := by
        calc
          (3 : ZMod 1525527821) ^ 23836372 = (3 : ZMod 1525527821) ^ (11918186 + 11918186) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 11918186 * (3 : ZMod 1525527821) ^ 11918186 := by rw [pow_add]
          _ = 548274004 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 1525527821) ^ 47672744 = 461583449 := by
        calc
          (3 : ZMod 1525527821) ^ 47672744 = (3 : ZMod 1525527821) ^ (23836372 + 23836372) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 23836372 * (3 : ZMod 1525527821) ^ 23836372 := by rw [pow_add]
          _ = 461583449 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 1525527821) ^ 95345488 = 903760457 := by
        calc
          (3 : ZMod 1525527821) ^ 95345488 = (3 : ZMod 1525527821) ^ (47672744 + 47672744) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 47672744 * (3 : ZMod 1525527821) ^ 47672744 := by rw [pow_add]
          _ = 903760457 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 1525527821) ^ 190690977 = 318540285 := by
        calc
          (3 : ZMod 1525527821) ^ 190690977 = (3 : ZMod 1525527821) ^ (95345488 + 95345488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 95345488 * (3 : ZMod 1525527821) ^ 95345488) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 318540285 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 1525527821) ^ 381381955 = 479806009 := by
        calc
          (3 : ZMod 1525527821) ^ 381381955 = (3 : ZMod 1525527821) ^ (190690977 + 190690977 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 190690977 * (3 : ZMod 1525527821) ^ 190690977) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 479806009 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 1525527821) ^ 762763910 = 1525527820 := by
        calc
          (3 : ZMod 1525527821) ^ 762763910 = (3 : ZMod 1525527821) ^ (381381955 + 381381955) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 381381955 * (3 : ZMod 1525527821) ^ 381381955 := by rw [pow_add]
          _ = 1525527820 := by rw [factor_0_28]; decide
      change (3 : ZMod 1525527821) ^ 762763910 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (3 : ZMod 1525527821) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 1525527821) ^ 2 = 9 := by
        calc
          (3 : ZMod 1525527821) ^ 2 = (3 : ZMod 1525527821) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 1 * (3 : ZMod 1525527821) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 1525527821) ^ 4 = 81 := by
        calc
          (3 : ZMod 1525527821) ^ 4 = (3 : ZMod 1525527821) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 2 * (3 : ZMod 1525527821) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 1525527821) ^ 9 = 19683 := by
        calc
          (3 : ZMod 1525527821) ^ 9 = (3 : ZMod 1525527821) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 4 * (3 : ZMod 1525527821) ^ 4) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 1525527821) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 1525527821) ^ 18 = (3 : ZMod 1525527821) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 9 * (3 : ZMod 1525527821) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 1525527821) ^ 36 = 247144903 := by
        calc
          (3 : ZMod 1525527821) ^ 36 = (3 : ZMod 1525527821) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 18 * (3 : ZMod 1525527821) ^ 18 := by rw [pow_add]
          _ = 247144903 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 1525527821) ^ 72 = 755971693 := by
        calc
          (3 : ZMod 1525527821) ^ 72 = (3 : ZMod 1525527821) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 36 * (3 : ZMod 1525527821) ^ 36 := by rw [pow_add]
          _ = 755971693 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 1525527821) ^ 145 = 1051051470 := by
        calc
          (3 : ZMod 1525527821) ^ 145 = (3 : ZMod 1525527821) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 72 * (3 : ZMod 1525527821) ^ 72) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1051051470 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 1525527821) ^ 290 = 1302978007 := by
        calc
          (3 : ZMod 1525527821) ^ 290 = (3 : ZMod 1525527821) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 145 * (3 : ZMod 1525527821) ^ 145 := by rw [pow_add]
          _ = 1302978007 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 1525527821) ^ 581 = 1142408643 := by
        calc
          (3 : ZMod 1525527821) ^ 581 = (3 : ZMod 1525527821) ^ (290 + 290 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 290 * (3 : ZMod 1525527821) ^ 290) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1142408643 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 1525527821) ^ 1163 = 679141117 := by
        calc
          (3 : ZMod 1525527821) ^ 1163 = (3 : ZMod 1525527821) ^ (581 + 581 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 581 * (3 : ZMod 1525527821) ^ 581) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 679141117 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 1525527821) ^ 2327 = 1022797530 := by
        calc
          (3 : ZMod 1525527821) ^ 2327 = (3 : ZMod 1525527821) ^ (1163 + 1163 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 1163 * (3 : ZMod 1525527821) ^ 1163) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1022797530 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 1525527821) ^ 4655 = 1390850000 := by
        calc
          (3 : ZMod 1525527821) ^ 4655 = (3 : ZMod 1525527821) ^ (2327 + 2327 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2327 * (3 : ZMod 1525527821) ^ 2327) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1390850000 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 1525527821) ^ 9311 = 133805670 := by
        calc
          (3 : ZMod 1525527821) ^ 9311 = (3 : ZMod 1525527821) ^ (4655 + 4655 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 4655 * (3 : ZMod 1525527821) ^ 4655) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 133805670 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 1525527821) ^ 18622 = 1266799323 := by
        calc
          (3 : ZMod 1525527821) ^ 18622 = (3 : ZMod 1525527821) ^ (9311 + 9311) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 9311 * (3 : ZMod 1525527821) ^ 9311 := by rw [pow_add]
          _ = 1266799323 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 1525527821) ^ 37244 = 296848224 := by
        calc
          (3 : ZMod 1525527821) ^ 37244 = (3 : ZMod 1525527821) ^ (18622 + 18622) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 18622 * (3 : ZMod 1525527821) ^ 18622 := by rw [pow_add]
          _ = 296848224 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 1525527821) ^ 74488 = 1360620085 := by
        calc
          (3 : ZMod 1525527821) ^ 74488 = (3 : ZMod 1525527821) ^ (37244 + 37244) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 37244 * (3 : ZMod 1525527821) ^ 37244 := by rw [pow_add]
          _ = 1360620085 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 1525527821) ^ 148977 = 145011940 := by
        calc
          (3 : ZMod 1525527821) ^ 148977 = (3 : ZMod 1525527821) ^ (74488 + 74488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 74488 * (3 : ZMod 1525527821) ^ 74488) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 145011940 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 1525527821) ^ 297954 = 1455216336 := by
        calc
          (3 : ZMod 1525527821) ^ 297954 = (3 : ZMod 1525527821) ^ (148977 + 148977) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 148977 * (3 : ZMod 1525527821) ^ 148977 := by rw [pow_add]
          _ = 1455216336 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 1525527821) ^ 595909 = 416177799 := by
        calc
          (3 : ZMod 1525527821) ^ 595909 = (3 : ZMod 1525527821) ^ (297954 + 297954 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 297954 * (3 : ZMod 1525527821) ^ 297954) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 416177799 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 1525527821) ^ 1191818 = 1380659931 := by
        calc
          (3 : ZMod 1525527821) ^ 1191818 = (3 : ZMod 1525527821) ^ (595909 + 595909) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 595909 * (3 : ZMod 1525527821) ^ 595909 := by rw [pow_add]
          _ = 1380659931 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 1525527821) ^ 2383637 = 1514135923 := by
        calc
          (3 : ZMod 1525527821) ^ 2383637 = (3 : ZMod 1525527821) ^ (1191818 + 1191818 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 1191818 * (3 : ZMod 1525527821) ^ 1191818) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1514135923 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 1525527821) ^ 4767274 = 213837755 := by
        calc
          (3 : ZMod 1525527821) ^ 4767274 = (3 : ZMod 1525527821) ^ (2383637 + 2383637) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 2383637 * (3 : ZMod 1525527821) ^ 2383637 := by rw [pow_add]
          _ = 213837755 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 1525527821) ^ 9534548 = 1138746534 := by
        calc
          (3 : ZMod 1525527821) ^ 9534548 = (3 : ZMod 1525527821) ^ (4767274 + 4767274) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 4767274 * (3 : ZMod 1525527821) ^ 4767274 := by rw [pow_add]
          _ = 1138746534 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 1525527821) ^ 19069097 = 1460935054 := by
        calc
          (3 : ZMod 1525527821) ^ 19069097 = (3 : ZMod 1525527821) ^ (9534548 + 9534548 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 9534548 * (3 : ZMod 1525527821) ^ 9534548) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 1460935054 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 1525527821) ^ 38138195 = 46435110 := by
        calc
          (3 : ZMod 1525527821) ^ 38138195 = (3 : ZMod 1525527821) ^ (19069097 + 19069097 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 19069097 * (3 : ZMod 1525527821) ^ 19069097) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 46435110 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 1525527821) ^ 76276391 = 840945525 := by
        calc
          (3 : ZMod 1525527821) ^ 76276391 = (3 : ZMod 1525527821) ^ (38138195 + 38138195 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 38138195 * (3 : ZMod 1525527821) ^ 38138195) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 840945525 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 1525527821) ^ 152552782 = 107959714 := by
        calc
          (3 : ZMod 1525527821) ^ 152552782 = (3 : ZMod 1525527821) ^ (76276391 + 76276391) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 76276391 * (3 : ZMod 1525527821) ^ 76276391 := by rw [pow_add]
          _ = 107959714 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 1525527821) ^ 305105564 = 327153121 := by
        calc
          (3 : ZMod 1525527821) ^ 305105564 = (3 : ZMod 1525527821) ^ (152552782 + 152552782) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 152552782 * (3 : ZMod 1525527821) ^ 152552782 := by rw [pow_add]
          _ = 327153121 := by rw [factor_1_27]; decide
      change (3 : ZMod 1525527821) ^ 305105564 ≠ 1
      rw [factor_1_28]
      decide
    ·
      have factor_2_0 : (3 : ZMod 1525527821) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 1525527821) ^ 2 = 9 := by
        calc
          (3 : ZMod 1525527821) ^ 2 = (3 : ZMod 1525527821) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 1 * (3 : ZMod 1525527821) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 1525527821) ^ 5 = 243 := by
        calc
          (3 : ZMod 1525527821) ^ 5 = (3 : ZMod 1525527821) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = ((3 : ZMod 1525527821) ^ 2 * (3 : ZMod 1525527821) ^ 2) * (3 : ZMod 1525527821) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 1525527821) ^ 10 = 59049 := by
        calc
          (3 : ZMod 1525527821) ^ 10 = (3 : ZMod 1525527821) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 5 * (3 : ZMod 1525527821) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 1525527821) ^ 20 = 435728759 := by
        calc
          (3 : ZMod 1525527821) ^ 20 = (3 : ZMod 1525527821) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 1525527821) ^ n) (by norm_num)
          _ = (3 : ZMod 1525527821) ^ 10 * (3 : ZMod 1525527821) ^ 10 := by rw [pow_add]
          _ = 435728759 := by rw [factor_2_3]; decide
      change (3 : ZMod 1525527821) ^ 20 ≠ 1
      rw [factor_2_4]
      decide

#print axioms prime_lucas_1525527821

end TotientTailPeriodKiller
end Erdos249257
