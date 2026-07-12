import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1525527821

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3051055643 : Nat.Prime 3051055643 := by
  apply lucas_primality 3051055643 (2 : ZMod 3051055643)
  ·
      have fermat_0 : (2 : ZMod 3051055643) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 3051055643) ^ 2 = 4 := by
        calc
          (2 : ZMod 3051055643) ^ 2 = (2 : ZMod 3051055643) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 1 * (2 : ZMod 3051055643) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 3051055643) ^ 5 = 32 := by
        calc
          (2 : ZMod 3051055643) ^ 5 = (2 : ZMod 3051055643) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 2 * (2 : ZMod 3051055643) ^ 2) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 3051055643) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3051055643) ^ 11 = (2 : ZMod 3051055643) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 5 * (2 : ZMod 3051055643) ^ 5) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 3051055643) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 3051055643) ^ 22 = (2 : ZMod 3051055643) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 11 * (2 : ZMod 3051055643) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 3051055643) ^ 45 = 2649469399 := by
        calc
          (2 : ZMod 3051055643) ^ 45 = (2 : ZMod 3051055643) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 22 * (2 : ZMod 3051055643) ^ 22) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2649469399 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 3051055643) ^ 90 = 2104034306 := by
        calc
          (2 : ZMod 3051055643) ^ 90 = (2 : ZMod 3051055643) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 45 * (2 : ZMod 3051055643) ^ 45 := by rw [pow_add]
          _ = 2104034306 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 3051055643) ^ 181 = 2906038567 := by
        calc
          (2 : ZMod 3051055643) ^ 181 = (2 : ZMod 3051055643) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 90 * (2 : ZMod 3051055643) ^ 90) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2906038567 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 3051055643) ^ 363 = 1193337429 := by
        calc
          (2 : ZMod 3051055643) ^ 363 = (2 : ZMod 3051055643) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 181 * (2 : ZMod 3051055643) ^ 181) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1193337429 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 3051055643) ^ 727 = 1407595017 := by
        calc
          (2 : ZMod 3051055643) ^ 727 = (2 : ZMod 3051055643) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 363 * (2 : ZMod 3051055643) ^ 363) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1407595017 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 3051055643) ^ 1454 = 1523052921 := by
        calc
          (2 : ZMod 3051055643) ^ 1454 = (2 : ZMod 3051055643) ^ (727 + 727) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 727 * (2 : ZMod 3051055643) ^ 727 := by rw [pow_add]
          _ = 1523052921 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 3051055643) ^ 2909 = 1802090977 := by
        calc
          (2 : ZMod 3051055643) ^ 2909 = (2 : ZMod 3051055643) ^ (1454 + 1454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 1454 * (2 : ZMod 3051055643) ^ 1454) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1802090977 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 3051055643) ^ 5819 = 773346300 := by
        calc
          (2 : ZMod 3051055643) ^ 5819 = (2 : ZMod 3051055643) ^ (2909 + 2909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 2909 * (2 : ZMod 3051055643) ^ 2909) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 773346300 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 3051055643) ^ 11638 = 1969372732 := by
        calc
          (2 : ZMod 3051055643) ^ 11638 = (2 : ZMod 3051055643) ^ (5819 + 5819) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 5819 * (2 : ZMod 3051055643) ^ 5819 := by rw [pow_add]
          _ = 1969372732 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 3051055643) ^ 23277 = 1675881839 := by
        calc
          (2 : ZMod 3051055643) ^ 23277 = (2 : ZMod 3051055643) ^ (11638 + 11638 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 11638 * (2 : ZMod 3051055643) ^ 11638) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1675881839 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 3051055643) ^ 46555 = 2731718192 := by
        calc
          (2 : ZMod 3051055643) ^ 46555 = (2 : ZMod 3051055643) ^ (23277 + 23277 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 23277 * (2 : ZMod 3051055643) ^ 23277) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2731718192 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 3051055643) ^ 93110 = 1568438284 := by
        calc
          (2 : ZMod 3051055643) ^ 93110 = (2 : ZMod 3051055643) ^ (46555 + 46555) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 46555 * (2 : ZMod 3051055643) ^ 46555 := by rw [pow_add]
          _ = 1568438284 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 3051055643) ^ 186221 = 2101521563 := by
        calc
          (2 : ZMod 3051055643) ^ 186221 = (2 : ZMod 3051055643) ^ (93110 + 93110 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 93110 * (2 : ZMod 3051055643) ^ 93110) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2101521563 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 3051055643) ^ 372443 = 2206675247 := by
        calc
          (2 : ZMod 3051055643) ^ 372443 = (2 : ZMod 3051055643) ^ (186221 + 186221 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 186221 * (2 : ZMod 3051055643) ^ 186221) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2206675247 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 3051055643) ^ 744886 = 823826533 := by
        calc
          (2 : ZMod 3051055643) ^ 744886 = (2 : ZMod 3051055643) ^ (372443 + 372443) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 372443 * (2 : ZMod 3051055643) ^ 372443 := by rw [pow_add]
          _ = 823826533 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 3051055643) ^ 1489773 = 61217786 := by
        calc
          (2 : ZMod 3051055643) ^ 1489773 = (2 : ZMod 3051055643) ^ (744886 + 744886 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 744886 * (2 : ZMod 3051055643) ^ 744886) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 61217786 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 3051055643) ^ 2979546 = 2625389253 := by
        calc
          (2 : ZMod 3051055643) ^ 2979546 = (2 : ZMod 3051055643) ^ (1489773 + 1489773) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 1489773 * (2 : ZMod 3051055643) ^ 1489773 := by rw [pow_add]
          _ = 2625389253 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 3051055643) ^ 5959093 = 2267149095 := by
        calc
          (2 : ZMod 3051055643) ^ 5959093 = (2 : ZMod 3051055643) ^ (2979546 + 2979546 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 2979546 * (2 : ZMod 3051055643) ^ 2979546) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2267149095 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 3051055643) ^ 11918186 = 1901084046 := by
        calc
          (2 : ZMod 3051055643) ^ 11918186 = (2 : ZMod 3051055643) ^ (5959093 + 5959093) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 5959093 * (2 : ZMod 3051055643) ^ 5959093 := by rw [pow_add]
          _ = 1901084046 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 3051055643) ^ 23836372 = 2105292606 := by
        calc
          (2 : ZMod 3051055643) ^ 23836372 = (2 : ZMod 3051055643) ^ (11918186 + 11918186) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 11918186 * (2 : ZMod 3051055643) ^ 11918186 := by rw [pow_add]
          _ = 2105292606 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 3051055643) ^ 47672744 = 3048336421 := by
        calc
          (2 : ZMod 3051055643) ^ 47672744 = (2 : ZMod 3051055643) ^ (23836372 + 23836372) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 23836372 * (2 : ZMod 3051055643) ^ 23836372 := by rw [pow_add]
          _ = 3048336421 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 3051055643) ^ 95345488 = 1460462295 := by
        calc
          (2 : ZMod 3051055643) ^ 95345488 = (2 : ZMod 3051055643) ^ (47672744 + 47672744) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 47672744 * (2 : ZMod 3051055643) ^ 47672744 := by rw [pow_add]
          _ = 1460462295 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 3051055643) ^ 190690977 = 1466970066 := by
        calc
          (2 : ZMod 3051055643) ^ 190690977 = (2 : ZMod 3051055643) ^ (95345488 + 95345488 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 95345488 * (2 : ZMod 3051055643) ^ 95345488) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1466970066 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 3051055643) ^ 381381955 = 458147560 := by
        calc
          (2 : ZMod 3051055643) ^ 381381955 = (2 : ZMod 3051055643) ^ (190690977 + 190690977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 190690977 * (2 : ZMod 3051055643) ^ 190690977) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 458147560 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 3051055643) ^ 762763910 = 1446716658 := by
        calc
          (2 : ZMod 3051055643) ^ 762763910 = (2 : ZMod 3051055643) ^ (381381955 + 381381955) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 381381955 * (2 : ZMod 3051055643) ^ 381381955 := by rw [pow_add]
          _ = 1446716658 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 3051055643) ^ 1525527821 = 3051055642 := by
        calc
          (2 : ZMod 3051055643) ^ 1525527821 = (2 : ZMod 3051055643) ^ (762763910 + 762763910 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 762763910 * (2 : ZMod 3051055643) ^ 762763910) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 3051055642 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 3051055643) ^ 3051055642 = 1 := by
        calc
          (2 : ZMod 3051055643) ^ 3051055642 = (2 : ZMod 3051055643) ^ (1525527821 + 1525527821) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 1525527821 * (2 : ZMod 3051055643) ^ 1525527821 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1525527821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1525527821, 1)] : List FactorBlock).map factorBlockValue).prod = 3051055643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_1525527821) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 3051055643) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 3051055643) ^ 2 = 4 := by
        calc
          (2 : ZMod 3051055643) ^ 2 = (2 : ZMod 3051055643) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 1 * (2 : ZMod 3051055643) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 3051055643) ^ 5 = 32 := by
        calc
          (2 : ZMod 3051055643) ^ 5 = (2 : ZMod 3051055643) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 2 * (2 : ZMod 3051055643) ^ 2) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 3051055643) ^ 11 = 2048 := by
        calc
          (2 : ZMod 3051055643) ^ 11 = (2 : ZMod 3051055643) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 5 * (2 : ZMod 3051055643) ^ 5) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 3051055643) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 3051055643) ^ 22 = (2 : ZMod 3051055643) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 11 * (2 : ZMod 3051055643) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 3051055643) ^ 45 = 2649469399 := by
        calc
          (2 : ZMod 3051055643) ^ 45 = (2 : ZMod 3051055643) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 22 * (2 : ZMod 3051055643) ^ 22) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2649469399 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 3051055643) ^ 90 = 2104034306 := by
        calc
          (2 : ZMod 3051055643) ^ 90 = (2 : ZMod 3051055643) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 45 * (2 : ZMod 3051055643) ^ 45 := by rw [pow_add]
          _ = 2104034306 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 3051055643) ^ 181 = 2906038567 := by
        calc
          (2 : ZMod 3051055643) ^ 181 = (2 : ZMod 3051055643) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 90 * (2 : ZMod 3051055643) ^ 90) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2906038567 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 3051055643) ^ 363 = 1193337429 := by
        calc
          (2 : ZMod 3051055643) ^ 363 = (2 : ZMod 3051055643) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 181 * (2 : ZMod 3051055643) ^ 181) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1193337429 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 3051055643) ^ 727 = 1407595017 := by
        calc
          (2 : ZMod 3051055643) ^ 727 = (2 : ZMod 3051055643) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 363 * (2 : ZMod 3051055643) ^ 363) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1407595017 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 3051055643) ^ 1454 = 1523052921 := by
        calc
          (2 : ZMod 3051055643) ^ 1454 = (2 : ZMod 3051055643) ^ (727 + 727) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 727 * (2 : ZMod 3051055643) ^ 727 := by rw [pow_add]
          _ = 1523052921 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 3051055643) ^ 2909 = 1802090977 := by
        calc
          (2 : ZMod 3051055643) ^ 2909 = (2 : ZMod 3051055643) ^ (1454 + 1454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 1454 * (2 : ZMod 3051055643) ^ 1454) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1802090977 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 3051055643) ^ 5819 = 773346300 := by
        calc
          (2 : ZMod 3051055643) ^ 5819 = (2 : ZMod 3051055643) ^ (2909 + 2909 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 2909 * (2 : ZMod 3051055643) ^ 2909) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 773346300 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 3051055643) ^ 11638 = 1969372732 := by
        calc
          (2 : ZMod 3051055643) ^ 11638 = (2 : ZMod 3051055643) ^ (5819 + 5819) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 5819 * (2 : ZMod 3051055643) ^ 5819 := by rw [pow_add]
          _ = 1969372732 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 3051055643) ^ 23277 = 1675881839 := by
        calc
          (2 : ZMod 3051055643) ^ 23277 = (2 : ZMod 3051055643) ^ (11638 + 11638 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 11638 * (2 : ZMod 3051055643) ^ 11638) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1675881839 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 3051055643) ^ 46555 = 2731718192 := by
        calc
          (2 : ZMod 3051055643) ^ 46555 = (2 : ZMod 3051055643) ^ (23277 + 23277 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 23277 * (2 : ZMod 3051055643) ^ 23277) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2731718192 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 3051055643) ^ 93110 = 1568438284 := by
        calc
          (2 : ZMod 3051055643) ^ 93110 = (2 : ZMod 3051055643) ^ (46555 + 46555) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 46555 * (2 : ZMod 3051055643) ^ 46555 := by rw [pow_add]
          _ = 1568438284 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 3051055643) ^ 186221 = 2101521563 := by
        calc
          (2 : ZMod 3051055643) ^ 186221 = (2 : ZMod 3051055643) ^ (93110 + 93110 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 93110 * (2 : ZMod 3051055643) ^ 93110) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2101521563 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 3051055643) ^ 372443 = 2206675247 := by
        calc
          (2 : ZMod 3051055643) ^ 372443 = (2 : ZMod 3051055643) ^ (186221 + 186221 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 186221 * (2 : ZMod 3051055643) ^ 186221) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2206675247 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 3051055643) ^ 744886 = 823826533 := by
        calc
          (2 : ZMod 3051055643) ^ 744886 = (2 : ZMod 3051055643) ^ (372443 + 372443) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 372443 * (2 : ZMod 3051055643) ^ 372443 := by rw [pow_add]
          _ = 823826533 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 3051055643) ^ 1489773 = 61217786 := by
        calc
          (2 : ZMod 3051055643) ^ 1489773 = (2 : ZMod 3051055643) ^ (744886 + 744886 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 744886 * (2 : ZMod 3051055643) ^ 744886) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 61217786 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 3051055643) ^ 2979546 = 2625389253 := by
        calc
          (2 : ZMod 3051055643) ^ 2979546 = (2 : ZMod 3051055643) ^ (1489773 + 1489773) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 1489773 * (2 : ZMod 3051055643) ^ 1489773 := by rw [pow_add]
          _ = 2625389253 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 3051055643) ^ 5959093 = 2267149095 := by
        calc
          (2 : ZMod 3051055643) ^ 5959093 = (2 : ZMod 3051055643) ^ (2979546 + 2979546 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 2979546 * (2 : ZMod 3051055643) ^ 2979546) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 2267149095 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 3051055643) ^ 11918186 = 1901084046 := by
        calc
          (2 : ZMod 3051055643) ^ 11918186 = (2 : ZMod 3051055643) ^ (5959093 + 5959093) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 5959093 * (2 : ZMod 3051055643) ^ 5959093 := by rw [pow_add]
          _ = 1901084046 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 3051055643) ^ 23836372 = 2105292606 := by
        calc
          (2 : ZMod 3051055643) ^ 23836372 = (2 : ZMod 3051055643) ^ (11918186 + 11918186) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 11918186 * (2 : ZMod 3051055643) ^ 11918186 := by rw [pow_add]
          _ = 2105292606 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 3051055643) ^ 47672744 = 3048336421 := by
        calc
          (2 : ZMod 3051055643) ^ 47672744 = (2 : ZMod 3051055643) ^ (23836372 + 23836372) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 23836372 * (2 : ZMod 3051055643) ^ 23836372 := by rw [pow_add]
          _ = 3048336421 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 3051055643) ^ 95345488 = 1460462295 := by
        calc
          (2 : ZMod 3051055643) ^ 95345488 = (2 : ZMod 3051055643) ^ (47672744 + 47672744) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 47672744 * (2 : ZMod 3051055643) ^ 47672744 := by rw [pow_add]
          _ = 1460462295 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 3051055643) ^ 190690977 = 1466970066 := by
        calc
          (2 : ZMod 3051055643) ^ 190690977 = (2 : ZMod 3051055643) ^ (95345488 + 95345488 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 95345488 * (2 : ZMod 3051055643) ^ 95345488) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 1466970066 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 3051055643) ^ 381381955 = 458147560 := by
        calc
          (2 : ZMod 3051055643) ^ 381381955 = (2 : ZMod 3051055643) ^ (190690977 + 190690977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 190690977 * (2 : ZMod 3051055643) ^ 190690977) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 458147560 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 3051055643) ^ 762763910 = 1446716658 := by
        calc
          (2 : ZMod 3051055643) ^ 762763910 = (2 : ZMod 3051055643) ^ (381381955 + 381381955) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 381381955 * (2 : ZMod 3051055643) ^ 381381955 := by rw [pow_add]
          _ = 1446716658 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 3051055643) ^ 1525527821 = 3051055642 := by
        calc
          (2 : ZMod 3051055643) ^ 1525527821 = (2 : ZMod 3051055643) ^ (762763910 + 762763910 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = ((2 : ZMod 3051055643) ^ 762763910 * (2 : ZMod 3051055643) ^ 762763910) * (2 : ZMod 3051055643) := by rw [pow_succ, pow_add]
          _ = 3051055642 := by rw [factor_0_29]; decide
      change (2 : ZMod 3051055643) ^ 1525527821 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (2 : ZMod 3051055643) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 3051055643) ^ 2 = 4 := by
        calc
          (2 : ZMod 3051055643) ^ 2 = (2 : ZMod 3051055643) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 3051055643) ^ n) (by norm_num)
          _ = (2 : ZMod 3051055643) ^ 1 * (2 : ZMod 3051055643) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      change (2 : ZMod 3051055643) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_3051055643

end TotientTailPeriodKiller
end Erdos249257
