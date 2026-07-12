import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1567050703

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6268202813 : Nat.Prime 6268202813 := by
  apply lucas_primality 6268202813 (2 : ZMod 6268202813)
  ·
      have fermat_0 : (2 : ZMod 6268202813) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 6268202813) ^ 2 = 4 := by
        calc
          (2 : ZMod 6268202813) ^ 2 = (2 : ZMod 6268202813) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 1 * (2 : ZMod 6268202813) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 6268202813) ^ 5 = 32 := by
        calc
          (2 : ZMod 6268202813) ^ 5 = (2 : ZMod 6268202813) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 2 * (2 : ZMod 6268202813) ^ 2) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 6268202813) ^ 11 = 2048 := by
        calc
          (2 : ZMod 6268202813) ^ 11 = (2 : ZMod 6268202813) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 5 * (2 : ZMod 6268202813) ^ 5) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 6268202813) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 6268202813) ^ 23 = (2 : ZMod 6268202813) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 11 * (2 : ZMod 6268202813) ^ 11) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 6268202813) ^ 46 = 1899398926 := by
        calc
          (2 : ZMod 6268202813) ^ 46 = (2 : ZMod 6268202813) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 23 * (2 : ZMod 6268202813) ^ 23 := by rw [pow_add]
          _ = 1899398926 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 6268202813) ^ 93 = 5509001445 := by
        calc
          (2 : ZMod 6268202813) ^ 93 = (2 : ZMod 6268202813) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 46 * (2 : ZMod 6268202813) ^ 46) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5509001445 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 6268202813) ^ 186 = 809692205 := by
        calc
          (2 : ZMod 6268202813) ^ 186 = (2 : ZMod 6268202813) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 93 * (2 : ZMod 6268202813) ^ 93 := by rw [pow_add]
          _ = 809692205 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 6268202813) ^ 373 = 4152489621 := by
        calc
          (2 : ZMod 6268202813) ^ 373 = (2 : ZMod 6268202813) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 186 * (2 : ZMod 6268202813) ^ 186) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 4152489621 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 6268202813) ^ 747 = 6043137857 := by
        calc
          (2 : ZMod 6268202813) ^ 747 = (2 : ZMod 6268202813) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 373 * (2 : ZMod 6268202813) ^ 373) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 6043137857 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 6268202813) ^ 1494 = 3670832303 := by
        calc
          (2 : ZMod 6268202813) ^ 1494 = (2 : ZMod 6268202813) ^ (747 + 747) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 747 * (2 : ZMod 6268202813) ^ 747 := by rw [pow_add]
          _ = 3670832303 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 6268202813) ^ 2988 = 2677102594 := by
        calc
          (2 : ZMod 6268202813) ^ 2988 = (2 : ZMod 6268202813) ^ (1494 + 1494) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 1494 * (2 : ZMod 6268202813) ^ 1494 := by rw [pow_add]
          _ = 2677102594 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 6268202813) ^ 5977 = 3145323404 := by
        calc
          (2 : ZMod 6268202813) ^ 5977 = (2 : ZMod 6268202813) ^ (2988 + 2988 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 2988 * (2 : ZMod 6268202813) ^ 2988) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3145323404 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 6268202813) ^ 11955 = 664449453 := by
        calc
          (2 : ZMod 6268202813) ^ 11955 = (2 : ZMod 6268202813) ^ (5977 + 5977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 5977 * (2 : ZMod 6268202813) ^ 5977) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 664449453 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 6268202813) ^ 23911 = 3668881536 := by
        calc
          (2 : ZMod 6268202813) ^ 23911 = (2 : ZMod 6268202813) ^ (11955 + 11955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 11955 * (2 : ZMod 6268202813) ^ 11955) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3668881536 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 6268202813) ^ 47822 = 4455902388 := by
        calc
          (2 : ZMod 6268202813) ^ 47822 = (2 : ZMod 6268202813) ^ (23911 + 23911) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 23911 * (2 : ZMod 6268202813) ^ 23911 := by rw [pow_add]
          _ = 4455902388 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 6268202813) ^ 95645 = 301801822 := by
        calc
          (2 : ZMod 6268202813) ^ 95645 = (2 : ZMod 6268202813) ^ (47822 + 47822 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 47822 * (2 : ZMod 6268202813) ^ 47822) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 301801822 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 6268202813) ^ 191290 = 287730035 := by
        calc
          (2 : ZMod 6268202813) ^ 191290 = (2 : ZMod 6268202813) ^ (95645 + 95645) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 95645 * (2 : ZMod 6268202813) ^ 95645 := by rw [pow_add]
          _ = 287730035 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 6268202813) ^ 382580 = 5675029873 := by
        calc
          (2 : ZMod 6268202813) ^ 382580 = (2 : ZMod 6268202813) ^ (191290 + 191290) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 191290 * (2 : ZMod 6268202813) ^ 191290 := by rw [pow_add]
          _ = 5675029873 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 6268202813) ^ 765161 = 3816636211 := by
        calc
          (2 : ZMod 6268202813) ^ 765161 = (2 : ZMod 6268202813) ^ (382580 + 382580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 382580 * (2 : ZMod 6268202813) ^ 382580) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3816636211 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 6268202813) ^ 1530322 = 3298829006 := by
        calc
          (2 : ZMod 6268202813) ^ 1530322 = (2 : ZMod 6268202813) ^ (765161 + 765161) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 765161 * (2 : ZMod 6268202813) ^ 765161 := by rw [pow_add]
          _ = 3298829006 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 6268202813) ^ 3060645 = 3988694061 := by
        calc
          (2 : ZMod 6268202813) ^ 3060645 = (2 : ZMod 6268202813) ^ (1530322 + 1530322 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 1530322 * (2 : ZMod 6268202813) ^ 1530322) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3988694061 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 6268202813) ^ 6121291 = 1018137159 := by
        calc
          (2 : ZMod 6268202813) ^ 6121291 = (2 : ZMod 6268202813) ^ (3060645 + 3060645 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 3060645 * (2 : ZMod 6268202813) ^ 3060645) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 1018137159 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 6268202813) ^ 12242583 = 4383121747 := by
        calc
          (2 : ZMod 6268202813) ^ 12242583 = (2 : ZMod 6268202813) ^ (6121291 + 6121291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 6121291 * (2 : ZMod 6268202813) ^ 6121291) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 4383121747 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 6268202813) ^ 24485167 = 5565801733 := by
        calc
          (2 : ZMod 6268202813) ^ 24485167 = (2 : ZMod 6268202813) ^ (12242583 + 12242583 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 12242583 * (2 : ZMod 6268202813) ^ 12242583) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5565801733 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 6268202813) ^ 48970334 = 4902069762 := by
        calc
          (2 : ZMod 6268202813) ^ 48970334 = (2 : ZMod 6268202813) ^ (24485167 + 24485167) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 24485167 * (2 : ZMod 6268202813) ^ 24485167 := by rw [pow_add]
          _ = 4902069762 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 6268202813) ^ 97940668 = 4213417560 := by
        calc
          (2 : ZMod 6268202813) ^ 97940668 = (2 : ZMod 6268202813) ^ (48970334 + 48970334) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 48970334 * (2 : ZMod 6268202813) ^ 48970334 := by rw [pow_add]
          _ = 4213417560 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 6268202813) ^ 195881337 = 2002337937 := by
        calc
          (2 : ZMod 6268202813) ^ 195881337 = (2 : ZMod 6268202813) ^ (97940668 + 97940668 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 97940668 * (2 : ZMod 6268202813) ^ 97940668) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 2002337937 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 6268202813) ^ 391762675 = 5080135812 := by
        calc
          (2 : ZMod 6268202813) ^ 391762675 = (2 : ZMod 6268202813) ^ (195881337 + 195881337 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 195881337 * (2 : ZMod 6268202813) ^ 195881337) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5080135812 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 6268202813) ^ 783525351 = 2512300517 := by
        calc
          (2 : ZMod 6268202813) ^ 783525351 = (2 : ZMod 6268202813) ^ (391762675 + 391762675 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 391762675 * (2 : ZMod 6268202813) ^ 391762675) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 2512300517 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 6268202813) ^ 1567050703 = 5024601033 := by
        calc
          (2 : ZMod 6268202813) ^ 1567050703 = (2 : ZMod 6268202813) ^ (783525351 + 783525351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 783525351 * (2 : ZMod 6268202813) ^ 783525351) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5024601033 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 6268202813) ^ 3134101406 = 6268202812 := by
        calc
          (2 : ZMod 6268202813) ^ 3134101406 = (2 : ZMod 6268202813) ^ (1567050703 + 1567050703) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 1567050703 * (2 : ZMod 6268202813) ^ 1567050703 := by rw [pow_add]
          _ = 6268202812 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 6268202813) ^ 6268202812 = 1 := by
        calc
          (2 : ZMod 6268202813) ^ 6268202812 = (2 : ZMod 6268202813) ^ (3134101406 + 3134101406) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 3134101406 * (2 : ZMod 6268202813) ^ 3134101406 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1567050703, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1567050703, 1)] : List FactorBlock).map factorBlockValue).prod = 6268202813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_1567050703) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 6268202813) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 6268202813) ^ 2 = 4 := by
        calc
          (2 : ZMod 6268202813) ^ 2 = (2 : ZMod 6268202813) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 1 * (2 : ZMod 6268202813) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 6268202813) ^ 5 = 32 := by
        calc
          (2 : ZMod 6268202813) ^ 5 = (2 : ZMod 6268202813) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 2 * (2 : ZMod 6268202813) ^ 2) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 6268202813) ^ 11 = 2048 := by
        calc
          (2 : ZMod 6268202813) ^ 11 = (2 : ZMod 6268202813) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 5 * (2 : ZMod 6268202813) ^ 5) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 6268202813) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 6268202813) ^ 23 = (2 : ZMod 6268202813) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 11 * (2 : ZMod 6268202813) ^ 11) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 6268202813) ^ 46 = 1899398926 := by
        calc
          (2 : ZMod 6268202813) ^ 46 = (2 : ZMod 6268202813) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 23 * (2 : ZMod 6268202813) ^ 23 := by rw [pow_add]
          _ = 1899398926 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 6268202813) ^ 93 = 5509001445 := by
        calc
          (2 : ZMod 6268202813) ^ 93 = (2 : ZMod 6268202813) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 46 * (2 : ZMod 6268202813) ^ 46) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5509001445 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 6268202813) ^ 186 = 809692205 := by
        calc
          (2 : ZMod 6268202813) ^ 186 = (2 : ZMod 6268202813) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 93 * (2 : ZMod 6268202813) ^ 93 := by rw [pow_add]
          _ = 809692205 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 6268202813) ^ 373 = 4152489621 := by
        calc
          (2 : ZMod 6268202813) ^ 373 = (2 : ZMod 6268202813) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 186 * (2 : ZMod 6268202813) ^ 186) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 4152489621 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 6268202813) ^ 747 = 6043137857 := by
        calc
          (2 : ZMod 6268202813) ^ 747 = (2 : ZMod 6268202813) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 373 * (2 : ZMod 6268202813) ^ 373) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 6043137857 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 6268202813) ^ 1494 = 3670832303 := by
        calc
          (2 : ZMod 6268202813) ^ 1494 = (2 : ZMod 6268202813) ^ (747 + 747) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 747 * (2 : ZMod 6268202813) ^ 747 := by rw [pow_add]
          _ = 3670832303 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 6268202813) ^ 2988 = 2677102594 := by
        calc
          (2 : ZMod 6268202813) ^ 2988 = (2 : ZMod 6268202813) ^ (1494 + 1494) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 1494 * (2 : ZMod 6268202813) ^ 1494 := by rw [pow_add]
          _ = 2677102594 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 6268202813) ^ 5977 = 3145323404 := by
        calc
          (2 : ZMod 6268202813) ^ 5977 = (2 : ZMod 6268202813) ^ (2988 + 2988 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 2988 * (2 : ZMod 6268202813) ^ 2988) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3145323404 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 6268202813) ^ 11955 = 664449453 := by
        calc
          (2 : ZMod 6268202813) ^ 11955 = (2 : ZMod 6268202813) ^ (5977 + 5977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 5977 * (2 : ZMod 6268202813) ^ 5977) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 664449453 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 6268202813) ^ 23911 = 3668881536 := by
        calc
          (2 : ZMod 6268202813) ^ 23911 = (2 : ZMod 6268202813) ^ (11955 + 11955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 11955 * (2 : ZMod 6268202813) ^ 11955) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3668881536 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 6268202813) ^ 47822 = 4455902388 := by
        calc
          (2 : ZMod 6268202813) ^ 47822 = (2 : ZMod 6268202813) ^ (23911 + 23911) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 23911 * (2 : ZMod 6268202813) ^ 23911 := by rw [pow_add]
          _ = 4455902388 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 6268202813) ^ 95645 = 301801822 := by
        calc
          (2 : ZMod 6268202813) ^ 95645 = (2 : ZMod 6268202813) ^ (47822 + 47822 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 47822 * (2 : ZMod 6268202813) ^ 47822) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 301801822 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 6268202813) ^ 191290 = 287730035 := by
        calc
          (2 : ZMod 6268202813) ^ 191290 = (2 : ZMod 6268202813) ^ (95645 + 95645) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 95645 * (2 : ZMod 6268202813) ^ 95645 := by rw [pow_add]
          _ = 287730035 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 6268202813) ^ 382580 = 5675029873 := by
        calc
          (2 : ZMod 6268202813) ^ 382580 = (2 : ZMod 6268202813) ^ (191290 + 191290) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 191290 * (2 : ZMod 6268202813) ^ 191290 := by rw [pow_add]
          _ = 5675029873 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 6268202813) ^ 765161 = 3816636211 := by
        calc
          (2 : ZMod 6268202813) ^ 765161 = (2 : ZMod 6268202813) ^ (382580 + 382580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 382580 * (2 : ZMod 6268202813) ^ 382580) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3816636211 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 6268202813) ^ 1530322 = 3298829006 := by
        calc
          (2 : ZMod 6268202813) ^ 1530322 = (2 : ZMod 6268202813) ^ (765161 + 765161) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 765161 * (2 : ZMod 6268202813) ^ 765161 := by rw [pow_add]
          _ = 3298829006 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 6268202813) ^ 3060645 = 3988694061 := by
        calc
          (2 : ZMod 6268202813) ^ 3060645 = (2 : ZMod 6268202813) ^ (1530322 + 1530322 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 1530322 * (2 : ZMod 6268202813) ^ 1530322) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 3988694061 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 6268202813) ^ 6121291 = 1018137159 := by
        calc
          (2 : ZMod 6268202813) ^ 6121291 = (2 : ZMod 6268202813) ^ (3060645 + 3060645 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 3060645 * (2 : ZMod 6268202813) ^ 3060645) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 1018137159 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 6268202813) ^ 12242583 = 4383121747 := by
        calc
          (2 : ZMod 6268202813) ^ 12242583 = (2 : ZMod 6268202813) ^ (6121291 + 6121291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 6121291 * (2 : ZMod 6268202813) ^ 6121291) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 4383121747 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 6268202813) ^ 24485167 = 5565801733 := by
        calc
          (2 : ZMod 6268202813) ^ 24485167 = (2 : ZMod 6268202813) ^ (12242583 + 12242583 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 12242583 * (2 : ZMod 6268202813) ^ 12242583) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5565801733 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 6268202813) ^ 48970334 = 4902069762 := by
        calc
          (2 : ZMod 6268202813) ^ 48970334 = (2 : ZMod 6268202813) ^ (24485167 + 24485167) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 24485167 * (2 : ZMod 6268202813) ^ 24485167 := by rw [pow_add]
          _ = 4902069762 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 6268202813) ^ 97940668 = 4213417560 := by
        calc
          (2 : ZMod 6268202813) ^ 97940668 = (2 : ZMod 6268202813) ^ (48970334 + 48970334) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 48970334 * (2 : ZMod 6268202813) ^ 48970334 := by rw [pow_add]
          _ = 4213417560 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 6268202813) ^ 195881337 = 2002337937 := by
        calc
          (2 : ZMod 6268202813) ^ 195881337 = (2 : ZMod 6268202813) ^ (97940668 + 97940668 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 97940668 * (2 : ZMod 6268202813) ^ 97940668) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 2002337937 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 6268202813) ^ 391762675 = 5080135812 := by
        calc
          (2 : ZMod 6268202813) ^ 391762675 = (2 : ZMod 6268202813) ^ (195881337 + 195881337 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 195881337 * (2 : ZMod 6268202813) ^ 195881337) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5080135812 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 6268202813) ^ 783525351 = 2512300517 := by
        calc
          (2 : ZMod 6268202813) ^ 783525351 = (2 : ZMod 6268202813) ^ (391762675 + 391762675 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 391762675 * (2 : ZMod 6268202813) ^ 391762675) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 2512300517 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 6268202813) ^ 1567050703 = 5024601033 := by
        calc
          (2 : ZMod 6268202813) ^ 1567050703 = (2 : ZMod 6268202813) ^ (783525351 + 783525351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = ((2 : ZMod 6268202813) ^ 783525351 * (2 : ZMod 6268202813) ^ 783525351) * (2 : ZMod 6268202813) := by rw [pow_succ, pow_add]
          _ = 5024601033 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 6268202813) ^ 3134101406 = 6268202812 := by
        calc
          (2 : ZMod 6268202813) ^ 3134101406 = (2 : ZMod 6268202813) ^ (1567050703 + 1567050703) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 1567050703 * (2 : ZMod 6268202813) ^ 1567050703 := by rw [pow_add]
          _ = 6268202812 := by rw [factor_0_30]; decide
      change (2 : ZMod 6268202813) ^ 3134101406 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (2 : ZMod 6268202813) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 6268202813) ^ 2 = 4 := by
        calc
          (2 : ZMod 6268202813) ^ 2 = (2 : ZMod 6268202813) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 1 * (2 : ZMod 6268202813) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 6268202813) ^ 4 = 16 := by
        calc
          (2 : ZMod 6268202813) ^ 4 = (2 : ZMod 6268202813) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 6268202813) ^ n) (by norm_num)
          _ = (2 : ZMod 6268202813) ^ 2 * (2 : ZMod 6268202813) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      change (2 : ZMod 6268202813) ^ 4 ≠ 1
      rw [factor_1_2]
      decide

#print axioms prime_lucas_6268202813

end TotientTailPeriodKiller
end Erdos249257
