import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1632785537

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_107763845443 : Nat.Prime 107763845443 := by
  apply lucas_primality 107763845443 (2 : ZMod 107763845443)
  ·
      have fermat_0 : (2 : ZMod 107763845443) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 107763845443) ^ 3 = 8 := by
        calc
          (2 : ZMod 107763845443) ^ 3 = (2 : ZMod 107763845443) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1 * (2 : ZMod 107763845443) ^ 1) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 107763845443) ^ 6 = 64 := by
        calc
          (2 : ZMod 107763845443) ^ 6 = (2 : ZMod 107763845443) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 3 * (2 : ZMod 107763845443) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 107763845443) ^ 12 = 4096 := by
        calc
          (2 : ZMod 107763845443) ^ 12 = (2 : ZMod 107763845443) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6 * (2 : ZMod 107763845443) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 107763845443) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 107763845443) ^ 25 = (2 : ZMod 107763845443) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 12 * (2 : ZMod 107763845443) ^ 12) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 107763845443) ^ 50 = 91013499603 := by
        calc
          (2 : ZMod 107763845443) ^ 50 = (2 : ZMod 107763845443) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 25 * (2 : ZMod 107763845443) ^ 25 := by rw [pow_add]
          _ = 91013499603 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 107763845443) ^ 100 = 42016029446 := by
        calc
          (2 : ZMod 107763845443) ^ 100 = (2 : ZMod 107763845443) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 50 * (2 : ZMod 107763845443) ^ 50 := by rw [pow_add]
          _ = 42016029446 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 107763845443) ^ 200 = 56092273247 := by
        calc
          (2 : ZMod 107763845443) ^ 200 = (2 : ZMod 107763845443) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 100 * (2 : ZMod 107763845443) ^ 100 := by rw [pow_add]
          _ = 56092273247 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 107763845443) ^ 401 = 91876757171 := by
        calc
          (2 : ZMod 107763845443) ^ 401 = (2 : ZMod 107763845443) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 200 * (2 : ZMod 107763845443) ^ 200) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 91876757171 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 107763845443) ^ 802 = 52678375015 := by
        calc
          (2 : ZMod 107763845443) ^ 802 = (2 : ZMod 107763845443) ^ (401 + 401) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 401 * (2 : ZMod 107763845443) ^ 401 := by rw [pow_add]
          _ = 52678375015 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 107763845443) ^ 1605 = 73260059969 := by
        calc
          (2 : ZMod 107763845443) ^ 1605 = (2 : ZMod 107763845443) ^ (802 + 802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 802 * (2 : ZMod 107763845443) ^ 802) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 73260059969 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 107763845443) ^ 3211 = 51860821636 := by
        calc
          (2 : ZMod 107763845443) ^ 3211 = (2 : ZMod 107763845443) ^ (1605 + 1605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1605 * (2 : ZMod 107763845443) ^ 1605) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 51860821636 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 107763845443) ^ 6423 = 30029762423 := by
        calc
          (2 : ZMod 107763845443) ^ 6423 = (2 : ZMod 107763845443) ^ (3211 + 3211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 3211 * (2 : ZMod 107763845443) ^ 3211) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 30029762423 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 107763845443) ^ 12846 = 52922660329 := by
        calc
          (2 : ZMod 107763845443) ^ 12846 = (2 : ZMod 107763845443) ^ (6423 + 6423) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6423 * (2 : ZMod 107763845443) ^ 6423 := by rw [pow_add]
          _ = 52922660329 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 107763845443) ^ 25692 = 95807934489 := by
        calc
          (2 : ZMod 107763845443) ^ 25692 = (2 : ZMod 107763845443) ^ (12846 + 12846) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 12846 * (2 : ZMod 107763845443) ^ 12846 := by rw [pow_add]
          _ = 95807934489 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 107763845443) ^ 51385 = 101585668400 := by
        calc
          (2 : ZMod 107763845443) ^ 51385 = (2 : ZMod 107763845443) ^ (25692 + 25692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 25692 * (2 : ZMod 107763845443) ^ 25692) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 101585668400 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 107763845443) ^ 102771 = 23930620931 := by
        calc
          (2 : ZMod 107763845443) ^ 102771 = (2 : ZMod 107763845443) ^ (51385 + 51385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 51385 * (2 : ZMod 107763845443) ^ 51385) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 23930620931 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 107763845443) ^ 205543 = 87788827152 := by
        calc
          (2 : ZMod 107763845443) ^ 205543 = (2 : ZMod 107763845443) ^ (102771 + 102771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 102771 * (2 : ZMod 107763845443) ^ 102771) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 87788827152 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 107763845443) ^ 411086 = 23437855101 := by
        calc
          (2 : ZMod 107763845443) ^ 411086 = (2 : ZMod 107763845443) ^ (205543 + 205543) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 205543 * (2 : ZMod 107763845443) ^ 205543 := by rw [pow_add]
          _ = 23437855101 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 107763845443) ^ 822172 = 11999017678 := by
        calc
          (2 : ZMod 107763845443) ^ 822172 = (2 : ZMod 107763845443) ^ (411086 + 411086) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 411086 * (2 : ZMod 107763845443) ^ 411086 := by rw [pow_add]
          _ = 11999017678 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 107763845443) ^ 1644345 = 4703455883 := by
        calc
          (2 : ZMod 107763845443) ^ 1644345 = (2 : ZMod 107763845443) ^ (822172 + 822172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 822172 * (2 : ZMod 107763845443) ^ 822172) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 4703455883 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 107763845443) ^ 3288691 = 94960851415 := by
        calc
          (2 : ZMod 107763845443) ^ 3288691 = (2 : ZMod 107763845443) ^ (1644345 + 1644345 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1644345 * (2 : ZMod 107763845443) ^ 1644345) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 94960851415 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 107763845443) ^ 6577383 = 29006392820 := by
        calc
          (2 : ZMod 107763845443) ^ 6577383 = (2 : ZMod 107763845443) ^ (3288691 + 3288691 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 3288691 * (2 : ZMod 107763845443) ^ 3288691) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 29006392820 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 107763845443) ^ 13154766 = 46780018072 := by
        calc
          (2 : ZMod 107763845443) ^ 13154766 = (2 : ZMod 107763845443) ^ (6577383 + 6577383) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6577383 * (2 : ZMod 107763845443) ^ 6577383 := by rw [pow_add]
          _ = 46780018072 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 107763845443) ^ 26309532 = 9534843507 := by
        calc
          (2 : ZMod 107763845443) ^ 26309532 = (2 : ZMod 107763845443) ^ (13154766 + 13154766) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 13154766 * (2 : ZMod 107763845443) ^ 13154766 := by rw [pow_add]
          _ = 9534843507 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 107763845443) ^ 52619065 = 6634966121 := by
        calc
          (2 : ZMod 107763845443) ^ 52619065 = (2 : ZMod 107763845443) ^ (26309532 + 26309532 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 26309532 * (2 : ZMod 107763845443) ^ 26309532) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 6634966121 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 107763845443) ^ 105238130 = 106465110877 := by
        calc
          (2 : ZMod 107763845443) ^ 105238130 = (2 : ZMod 107763845443) ^ (52619065 + 52619065) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 52619065 * (2 : ZMod 107763845443) ^ 52619065 := by rw [pow_add]
          _ = 106465110877 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 107763845443) ^ 210476260 = 61865471467 := by
        calc
          (2 : ZMod 107763845443) ^ 210476260 = (2 : ZMod 107763845443) ^ (105238130 + 105238130) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 105238130 * (2 : ZMod 107763845443) ^ 105238130 := by rw [pow_add]
          _ = 61865471467 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 107763845443) ^ 420952521 = 27242724147 := by
        calc
          (2 : ZMod 107763845443) ^ 420952521 = (2 : ZMod 107763845443) ^ (210476260 + 210476260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 210476260 * (2 : ZMod 107763845443) ^ 210476260) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 27242724147 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 107763845443) ^ 841905042 = 40150693561 := by
        calc
          (2 : ZMod 107763845443) ^ 841905042 = (2 : ZMod 107763845443) ^ (420952521 + 420952521) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 420952521 * (2 : ZMod 107763845443) ^ 420952521 := by rw [pow_add]
          _ = 40150693561 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 107763845443) ^ 1683810085 = 65163523365 := by
        calc
          (2 : ZMod 107763845443) ^ 1683810085 = (2 : ZMod 107763845443) ^ (841905042 + 841905042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 841905042 * (2 : ZMod 107763845443) ^ 841905042) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 65163523365 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 107763845443) ^ 3367620170 = 61150964322 := by
        calc
          (2 : ZMod 107763845443) ^ 3367620170 = (2 : ZMod 107763845443) ^ (1683810085 + 1683810085) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 1683810085 * (2 : ZMod 107763845443) ^ 1683810085 := by rw [pow_add]
          _ = 61150964322 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 107763845443) ^ 6735240340 = 19055487714 := by
        calc
          (2 : ZMod 107763845443) ^ 6735240340 = (2 : ZMod 107763845443) ^ (3367620170 + 3367620170) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 3367620170 * (2 : ZMod 107763845443) ^ 3367620170 := by rw [pow_add]
          _ = 19055487714 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 107763845443) ^ 13470480680 = 35226788798 := by
        calc
          (2 : ZMod 107763845443) ^ 13470480680 = (2 : ZMod 107763845443) ^ (6735240340 + 6735240340) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6735240340 * (2 : ZMod 107763845443) ^ 6735240340 := by rw [pow_add]
          _ = 35226788798 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 107763845443) ^ 26940961360 = 26806121550 := by
        calc
          (2 : ZMod 107763845443) ^ 26940961360 = (2 : ZMod 107763845443) ^ (13470480680 + 13470480680) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 13470480680 * (2 : ZMod 107763845443) ^ 13470480680 := by rw [pow_add]
          _ = 26806121550 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 107763845443) ^ 53881922721 = 107763845442 := by
        calc
          (2 : ZMod 107763845443) ^ 53881922721 = (2 : ZMod 107763845443) ^ (26940961360 + 26940961360 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 26940961360 * (2 : ZMod 107763845443) ^ 26940961360) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 107763845442 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 107763845443) ^ 107763845442 = 1 := by
        calc
          (2 : ZMod 107763845443) ^ 107763845442 = (2 : ZMod 107763845443) ^ (53881922721 + 53881922721) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 53881922721 * (2 : ZMod 107763845443) ^ 53881922721 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (1632785537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (1632785537, 1)] : List FactorBlock).map factorBlockValue).prod = 107763845443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1632785537) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 107763845443) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 107763845443) ^ 3 = 8 := by
        calc
          (2 : ZMod 107763845443) ^ 3 = (2 : ZMod 107763845443) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1 * (2 : ZMod 107763845443) ^ 1) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 107763845443) ^ 6 = 64 := by
        calc
          (2 : ZMod 107763845443) ^ 6 = (2 : ZMod 107763845443) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 3 * (2 : ZMod 107763845443) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 107763845443) ^ 12 = 4096 := by
        calc
          (2 : ZMod 107763845443) ^ 12 = (2 : ZMod 107763845443) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6 * (2 : ZMod 107763845443) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 107763845443) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 107763845443) ^ 25 = (2 : ZMod 107763845443) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 12 * (2 : ZMod 107763845443) ^ 12) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 107763845443) ^ 50 = 91013499603 := by
        calc
          (2 : ZMod 107763845443) ^ 50 = (2 : ZMod 107763845443) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 25 * (2 : ZMod 107763845443) ^ 25 := by rw [pow_add]
          _ = 91013499603 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 107763845443) ^ 100 = 42016029446 := by
        calc
          (2 : ZMod 107763845443) ^ 100 = (2 : ZMod 107763845443) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 50 * (2 : ZMod 107763845443) ^ 50 := by rw [pow_add]
          _ = 42016029446 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 107763845443) ^ 200 = 56092273247 := by
        calc
          (2 : ZMod 107763845443) ^ 200 = (2 : ZMod 107763845443) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 100 * (2 : ZMod 107763845443) ^ 100 := by rw [pow_add]
          _ = 56092273247 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 107763845443) ^ 401 = 91876757171 := by
        calc
          (2 : ZMod 107763845443) ^ 401 = (2 : ZMod 107763845443) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 200 * (2 : ZMod 107763845443) ^ 200) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 91876757171 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 107763845443) ^ 802 = 52678375015 := by
        calc
          (2 : ZMod 107763845443) ^ 802 = (2 : ZMod 107763845443) ^ (401 + 401) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 401 * (2 : ZMod 107763845443) ^ 401 := by rw [pow_add]
          _ = 52678375015 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 107763845443) ^ 1605 = 73260059969 := by
        calc
          (2 : ZMod 107763845443) ^ 1605 = (2 : ZMod 107763845443) ^ (802 + 802 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 802 * (2 : ZMod 107763845443) ^ 802) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 73260059969 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 107763845443) ^ 3211 = 51860821636 := by
        calc
          (2 : ZMod 107763845443) ^ 3211 = (2 : ZMod 107763845443) ^ (1605 + 1605 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1605 * (2 : ZMod 107763845443) ^ 1605) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 51860821636 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 107763845443) ^ 6423 = 30029762423 := by
        calc
          (2 : ZMod 107763845443) ^ 6423 = (2 : ZMod 107763845443) ^ (3211 + 3211 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 3211 * (2 : ZMod 107763845443) ^ 3211) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 30029762423 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 107763845443) ^ 12846 = 52922660329 := by
        calc
          (2 : ZMod 107763845443) ^ 12846 = (2 : ZMod 107763845443) ^ (6423 + 6423) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6423 * (2 : ZMod 107763845443) ^ 6423 := by rw [pow_add]
          _ = 52922660329 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 107763845443) ^ 25692 = 95807934489 := by
        calc
          (2 : ZMod 107763845443) ^ 25692 = (2 : ZMod 107763845443) ^ (12846 + 12846) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 12846 * (2 : ZMod 107763845443) ^ 12846 := by rw [pow_add]
          _ = 95807934489 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 107763845443) ^ 51385 = 101585668400 := by
        calc
          (2 : ZMod 107763845443) ^ 51385 = (2 : ZMod 107763845443) ^ (25692 + 25692 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 25692 * (2 : ZMod 107763845443) ^ 25692) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 101585668400 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 107763845443) ^ 102771 = 23930620931 := by
        calc
          (2 : ZMod 107763845443) ^ 102771 = (2 : ZMod 107763845443) ^ (51385 + 51385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 51385 * (2 : ZMod 107763845443) ^ 51385) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 23930620931 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 107763845443) ^ 205543 = 87788827152 := by
        calc
          (2 : ZMod 107763845443) ^ 205543 = (2 : ZMod 107763845443) ^ (102771 + 102771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 102771 * (2 : ZMod 107763845443) ^ 102771) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 87788827152 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 107763845443) ^ 411086 = 23437855101 := by
        calc
          (2 : ZMod 107763845443) ^ 411086 = (2 : ZMod 107763845443) ^ (205543 + 205543) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 205543 * (2 : ZMod 107763845443) ^ 205543 := by rw [pow_add]
          _ = 23437855101 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 107763845443) ^ 822172 = 11999017678 := by
        calc
          (2 : ZMod 107763845443) ^ 822172 = (2 : ZMod 107763845443) ^ (411086 + 411086) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 411086 * (2 : ZMod 107763845443) ^ 411086 := by rw [pow_add]
          _ = 11999017678 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 107763845443) ^ 1644345 = 4703455883 := by
        calc
          (2 : ZMod 107763845443) ^ 1644345 = (2 : ZMod 107763845443) ^ (822172 + 822172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 822172 * (2 : ZMod 107763845443) ^ 822172) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 4703455883 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 107763845443) ^ 3288691 = 94960851415 := by
        calc
          (2 : ZMod 107763845443) ^ 3288691 = (2 : ZMod 107763845443) ^ (1644345 + 1644345 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1644345 * (2 : ZMod 107763845443) ^ 1644345) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 94960851415 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 107763845443) ^ 6577383 = 29006392820 := by
        calc
          (2 : ZMod 107763845443) ^ 6577383 = (2 : ZMod 107763845443) ^ (3288691 + 3288691 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 3288691 * (2 : ZMod 107763845443) ^ 3288691) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 29006392820 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 107763845443) ^ 13154766 = 46780018072 := by
        calc
          (2 : ZMod 107763845443) ^ 13154766 = (2 : ZMod 107763845443) ^ (6577383 + 6577383) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6577383 * (2 : ZMod 107763845443) ^ 6577383 := by rw [pow_add]
          _ = 46780018072 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 107763845443) ^ 26309532 = 9534843507 := by
        calc
          (2 : ZMod 107763845443) ^ 26309532 = (2 : ZMod 107763845443) ^ (13154766 + 13154766) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 13154766 * (2 : ZMod 107763845443) ^ 13154766 := by rw [pow_add]
          _ = 9534843507 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 107763845443) ^ 52619065 = 6634966121 := by
        calc
          (2 : ZMod 107763845443) ^ 52619065 = (2 : ZMod 107763845443) ^ (26309532 + 26309532 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 26309532 * (2 : ZMod 107763845443) ^ 26309532) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 6634966121 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 107763845443) ^ 105238130 = 106465110877 := by
        calc
          (2 : ZMod 107763845443) ^ 105238130 = (2 : ZMod 107763845443) ^ (52619065 + 52619065) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 52619065 * (2 : ZMod 107763845443) ^ 52619065 := by rw [pow_add]
          _ = 106465110877 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 107763845443) ^ 210476260 = 61865471467 := by
        calc
          (2 : ZMod 107763845443) ^ 210476260 = (2 : ZMod 107763845443) ^ (105238130 + 105238130) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 105238130 * (2 : ZMod 107763845443) ^ 105238130 := by rw [pow_add]
          _ = 61865471467 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 107763845443) ^ 420952521 = 27242724147 := by
        calc
          (2 : ZMod 107763845443) ^ 420952521 = (2 : ZMod 107763845443) ^ (210476260 + 210476260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 210476260 * (2 : ZMod 107763845443) ^ 210476260) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 27242724147 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 107763845443) ^ 841905042 = 40150693561 := by
        calc
          (2 : ZMod 107763845443) ^ 841905042 = (2 : ZMod 107763845443) ^ (420952521 + 420952521) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 420952521 * (2 : ZMod 107763845443) ^ 420952521 := by rw [pow_add]
          _ = 40150693561 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 107763845443) ^ 1683810085 = 65163523365 := by
        calc
          (2 : ZMod 107763845443) ^ 1683810085 = (2 : ZMod 107763845443) ^ (841905042 + 841905042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 841905042 * (2 : ZMod 107763845443) ^ 841905042) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 65163523365 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 107763845443) ^ 3367620170 = 61150964322 := by
        calc
          (2 : ZMod 107763845443) ^ 3367620170 = (2 : ZMod 107763845443) ^ (1683810085 + 1683810085) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 1683810085 * (2 : ZMod 107763845443) ^ 1683810085 := by rw [pow_add]
          _ = 61150964322 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 107763845443) ^ 6735240340 = 19055487714 := by
        calc
          (2 : ZMod 107763845443) ^ 6735240340 = (2 : ZMod 107763845443) ^ (3367620170 + 3367620170) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 3367620170 * (2 : ZMod 107763845443) ^ 3367620170 := by rw [pow_add]
          _ = 19055487714 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 107763845443) ^ 13470480680 = 35226788798 := by
        calc
          (2 : ZMod 107763845443) ^ 13470480680 = (2 : ZMod 107763845443) ^ (6735240340 + 6735240340) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 6735240340 * (2 : ZMod 107763845443) ^ 6735240340 := by rw [pow_add]
          _ = 35226788798 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 107763845443) ^ 26940961360 = 26806121550 := by
        calc
          (2 : ZMod 107763845443) ^ 26940961360 = (2 : ZMod 107763845443) ^ (13470480680 + 13470480680) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 13470480680 * (2 : ZMod 107763845443) ^ 13470480680 := by rw [pow_add]
          _ = 26806121550 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 107763845443) ^ 53881922721 = 107763845442 := by
        calc
          (2 : ZMod 107763845443) ^ 53881922721 = (2 : ZMod 107763845443) ^ (26940961360 + 26940961360 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 26940961360 * (2 : ZMod 107763845443) ^ 26940961360) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 107763845442 := by rw [factor_0_34]; decide
      change (2 : ZMod 107763845443) ^ 53881922721 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (2 : ZMod 107763845443) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 107763845443) ^ 2 = 4 := by
        calc
          (2 : ZMod 107763845443) ^ 2 = (2 : ZMod 107763845443) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 1 * (2 : ZMod 107763845443) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 107763845443) ^ 4 = 16 := by
        calc
          (2 : ZMod 107763845443) ^ 4 = (2 : ZMod 107763845443) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 2 * (2 : ZMod 107763845443) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 107763845443) ^ 8 = 256 := by
        calc
          (2 : ZMod 107763845443) ^ 8 = (2 : ZMod 107763845443) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 4 * (2 : ZMod 107763845443) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 107763845443) ^ 16 = 65536 := by
        calc
          (2 : ZMod 107763845443) ^ 16 = (2 : ZMod 107763845443) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 8 * (2 : ZMod 107763845443) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 107763845443) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 107763845443) ^ 33 = (2 : ZMod 107763845443) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 16 * (2 : ZMod 107763845443) ^ 16) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 107763845443) ^ 66 = 39628557601 := by
        calc
          (2 : ZMod 107763845443) ^ 66 = (2 : ZMod 107763845443) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 33 * (2 : ZMod 107763845443) ^ 33 := by rw [pow_add]
          _ = 39628557601 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 107763845443) ^ 133 = 51180968246 := by
        calc
          (2 : ZMod 107763845443) ^ 133 = (2 : ZMod 107763845443) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 66 * (2 : ZMod 107763845443) ^ 66) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 51180968246 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 107763845443) ^ 267 = 22339112220 := by
        calc
          (2 : ZMod 107763845443) ^ 267 = (2 : ZMod 107763845443) ^ (133 + 133 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 133 * (2 : ZMod 107763845443) ^ 133) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 22339112220 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 107763845443) ^ 535 = 43841316087 := by
        calc
          (2 : ZMod 107763845443) ^ 535 = (2 : ZMod 107763845443) ^ (267 + 267 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 267 * (2 : ZMod 107763845443) ^ 267) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 43841316087 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 107763845443) ^ 1070 = 74813753389 := by
        calc
          (2 : ZMod 107763845443) ^ 1070 = (2 : ZMod 107763845443) ^ (535 + 535) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 535 * (2 : ZMod 107763845443) ^ 535 := by rw [pow_add]
          _ = 74813753389 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 107763845443) ^ 2141 = 70310314187 := by
        calc
          (2 : ZMod 107763845443) ^ 2141 = (2 : ZMod 107763845443) ^ (1070 + 1070 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1070 * (2 : ZMod 107763845443) ^ 1070) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 70310314187 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 107763845443) ^ 4282 = 13720330700 := by
        calc
          (2 : ZMod 107763845443) ^ 4282 = (2 : ZMod 107763845443) ^ (2141 + 2141) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 2141 * (2 : ZMod 107763845443) ^ 2141 := by rw [pow_add]
          _ = 13720330700 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 107763845443) ^ 8564 = 17922343362 := by
        calc
          (2 : ZMod 107763845443) ^ 8564 = (2 : ZMod 107763845443) ^ (4282 + 4282) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 4282 * (2 : ZMod 107763845443) ^ 4282 := by rw [pow_add]
          _ = 17922343362 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 107763845443) ^ 17128 = 15075232585 := by
        calc
          (2 : ZMod 107763845443) ^ 17128 = (2 : ZMod 107763845443) ^ (8564 + 8564) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 8564 * (2 : ZMod 107763845443) ^ 8564 := by rw [pow_add]
          _ = 15075232585 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 107763845443) ^ 34257 = 32232167743 := by
        calc
          (2 : ZMod 107763845443) ^ 34257 = (2 : ZMod 107763845443) ^ (17128 + 17128 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 17128 * (2 : ZMod 107763845443) ^ 17128) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 32232167743 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 107763845443) ^ 68514 = 88046733486 := by
        calc
          (2 : ZMod 107763845443) ^ 68514 = (2 : ZMod 107763845443) ^ (34257 + 34257) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 34257 * (2 : ZMod 107763845443) ^ 34257 := by rw [pow_add]
          _ = 88046733486 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 107763845443) ^ 137028 = 35189986166 := by
        calc
          (2 : ZMod 107763845443) ^ 137028 = (2 : ZMod 107763845443) ^ (68514 + 68514) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 68514 * (2 : ZMod 107763845443) ^ 68514 := by rw [pow_add]
          _ = 35189986166 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 107763845443) ^ 274057 = 107090111351 := by
        calc
          (2 : ZMod 107763845443) ^ 274057 = (2 : ZMod 107763845443) ^ (137028 + 137028 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 137028 * (2 : ZMod 107763845443) ^ 137028) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 107090111351 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 107763845443) ^ 548115 = 74752973142 := by
        calc
          (2 : ZMod 107763845443) ^ 548115 = (2 : ZMod 107763845443) ^ (274057 + 274057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 274057 * (2 : ZMod 107763845443) ^ 274057) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 74752973142 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 107763845443) ^ 1096230 = 995381305 := by
        calc
          (2 : ZMod 107763845443) ^ 1096230 = (2 : ZMod 107763845443) ^ (548115 + 548115) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 548115 * (2 : ZMod 107763845443) ^ 548115 := by rw [pow_add]
          _ = 995381305 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 107763845443) ^ 2192461 = 44378086356 := by
        calc
          (2 : ZMod 107763845443) ^ 2192461 = (2 : ZMod 107763845443) ^ (1096230 + 1096230 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1096230 * (2 : ZMod 107763845443) ^ 1096230) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 44378086356 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 107763845443) ^ 4384922 = 22542665733 := by
        calc
          (2 : ZMod 107763845443) ^ 4384922 = (2 : ZMod 107763845443) ^ (2192461 + 2192461) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 2192461 * (2 : ZMod 107763845443) ^ 2192461 := by rw [pow_add]
          _ = 22542665733 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 107763845443) ^ 8769844 = 64873972180 := by
        calc
          (2 : ZMod 107763845443) ^ 8769844 = (2 : ZMod 107763845443) ^ (4384922 + 4384922) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 4384922 * (2 : ZMod 107763845443) ^ 4384922 := by rw [pow_add]
          _ = 64873972180 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 107763845443) ^ 17539688 = 104505512420 := by
        calc
          (2 : ZMod 107763845443) ^ 17539688 = (2 : ZMod 107763845443) ^ (8769844 + 8769844) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 8769844 * (2 : ZMod 107763845443) ^ 8769844 := by rw [pow_add]
          _ = 104505512420 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 107763845443) ^ 35079376 = 65038441384 := by
        calc
          (2 : ZMod 107763845443) ^ 35079376 = (2 : ZMod 107763845443) ^ (17539688 + 17539688) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 17539688 * (2 : ZMod 107763845443) ^ 17539688 := by rw [pow_add]
          _ = 65038441384 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 107763845443) ^ 70158753 = 82039225308 := by
        calc
          (2 : ZMod 107763845443) ^ 70158753 = (2 : ZMod 107763845443) ^ (35079376 + 35079376 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 35079376 * (2 : ZMod 107763845443) ^ 35079376) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 82039225308 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 107763845443) ^ 140317507 = 5329560781 := by
        calc
          (2 : ZMod 107763845443) ^ 140317507 = (2 : ZMod 107763845443) ^ (70158753 + 70158753 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 70158753 * (2 : ZMod 107763845443) ^ 70158753) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 5329560781 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 107763845443) ^ 280635014 = 38158534709 := by
        calc
          (2 : ZMod 107763845443) ^ 280635014 = (2 : ZMod 107763845443) ^ (140317507 + 140317507) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 140317507 * (2 : ZMod 107763845443) ^ 140317507 := by rw [pow_add]
          _ = 38158534709 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 107763845443) ^ 561270028 = 34394424028 := by
        calc
          (2 : ZMod 107763845443) ^ 561270028 = (2 : ZMod 107763845443) ^ (280635014 + 280635014) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 280635014 * (2 : ZMod 107763845443) ^ 280635014 := by rw [pow_add]
          _ = 34394424028 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 107763845443) ^ 1122540056 = 85440960687 := by
        calc
          (2 : ZMod 107763845443) ^ 1122540056 = (2 : ZMod 107763845443) ^ (561270028 + 561270028) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 561270028 * (2 : ZMod 107763845443) ^ 561270028 := by rw [pow_add]
          _ = 85440960687 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 107763845443) ^ 2245080113 = 105409159977 := by
        calc
          (2 : ZMod 107763845443) ^ 2245080113 = (2 : ZMod 107763845443) ^ (1122540056 + 1122540056 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1122540056 * (2 : ZMod 107763845443) ^ 1122540056) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 105409159977 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 107763845443) ^ 4490160226 = 41203751746 := by
        calc
          (2 : ZMod 107763845443) ^ 4490160226 = (2 : ZMod 107763845443) ^ (2245080113 + 2245080113) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 2245080113 * (2 : ZMod 107763845443) ^ 2245080113 := by rw [pow_add]
          _ = 41203751746 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 107763845443) ^ 8980320453 = 98788076525 := by
        calc
          (2 : ZMod 107763845443) ^ 8980320453 = (2 : ZMod 107763845443) ^ (4490160226 + 4490160226 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 4490160226 * (2 : ZMod 107763845443) ^ 4490160226) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 98788076525 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 107763845443) ^ 17960640907 = 59119282965 := by
        calc
          (2 : ZMod 107763845443) ^ 17960640907 = (2 : ZMod 107763845443) ^ (8980320453 + 8980320453 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 8980320453 * (2 : ZMod 107763845443) ^ 8980320453) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 59119282965 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 107763845443) ^ 35921281814 = 59119282964 := by
        calc
          (2 : ZMod 107763845443) ^ 35921281814 = (2 : ZMod 107763845443) ^ (17960640907 + 17960640907) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 17960640907 * (2 : ZMod 107763845443) ^ 17960640907 := by rw [pow_add]
          _ = 59119282964 := by rw [factor_1_34]; decide
      change (2 : ZMod 107763845443) ^ 35921281814 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (2 : ZMod 107763845443) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 107763845443) ^ 2 = 4 := by
        calc
          (2 : ZMod 107763845443) ^ 2 = (2 : ZMod 107763845443) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 1 * (2 : ZMod 107763845443) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 107763845443) ^ 4 = 16 := by
        calc
          (2 : ZMod 107763845443) ^ 4 = (2 : ZMod 107763845443) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 2 * (2 : ZMod 107763845443) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 107763845443) ^ 9 = 512 := by
        calc
          (2 : ZMod 107763845443) ^ 9 = (2 : ZMod 107763845443) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 4 * (2 : ZMod 107763845443) ^ 4) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 107763845443) ^ 18 = 262144 := by
        calc
          (2 : ZMod 107763845443) ^ 18 = (2 : ZMod 107763845443) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 9 * (2 : ZMod 107763845443) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 107763845443) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 107763845443) ^ 36 = (2 : ZMod 107763845443) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 18 * (2 : ZMod 107763845443) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 107763845443) ^ 72 = 57659241275 := by
        calc
          (2 : ZMod 107763845443) ^ 72 = (2 : ZMod 107763845443) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 36 * (2 : ZMod 107763845443) ^ 36 := by rw [pow_add]
          _ = 57659241275 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 107763845443) ^ 145 = 36566548981 := by
        calc
          (2 : ZMod 107763845443) ^ 145 = (2 : ZMod 107763845443) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 72 * (2 : ZMod 107763845443) ^ 72) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 36566548981 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 107763845443) ^ 291 = 4631560325 := by
        calc
          (2 : ZMod 107763845443) ^ 291 = (2 : ZMod 107763845443) ^ (145 + 145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 145 * (2 : ZMod 107763845443) ^ 145) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 4631560325 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 107763845443) ^ 583 = 38308698254 := by
        calc
          (2 : ZMod 107763845443) ^ 583 = (2 : ZMod 107763845443) ^ (291 + 291 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 291 * (2 : ZMod 107763845443) ^ 291) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 38308698254 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 107763845443) ^ 1167 = 92300073190 := by
        calc
          (2 : ZMod 107763845443) ^ 1167 = (2 : ZMod 107763845443) ^ (583 + 583 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 583 * (2 : ZMod 107763845443) ^ 583) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 92300073190 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 107763845443) ^ 2335 = 77024306392 := by
        calc
          (2 : ZMod 107763845443) ^ 2335 = (2 : ZMod 107763845443) ^ (1167 + 1167 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1167 * (2 : ZMod 107763845443) ^ 1167) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 77024306392 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 107763845443) ^ 4671 = 77746570488 := by
        calc
          (2 : ZMod 107763845443) ^ 4671 = (2 : ZMod 107763845443) ^ (2335 + 2335 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 2335 * (2 : ZMod 107763845443) ^ 2335) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 77746570488 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 107763845443) ^ 9342 = 87645455673 := by
        calc
          (2 : ZMod 107763845443) ^ 9342 = (2 : ZMod 107763845443) ^ (4671 + 4671) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 4671 * (2 : ZMod 107763845443) ^ 4671 := by rw [pow_add]
          _ = 87645455673 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 107763845443) ^ 18685 = 38414954730 := by
        calc
          (2 : ZMod 107763845443) ^ 18685 = (2 : ZMod 107763845443) ^ (9342 + 9342 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 9342 * (2 : ZMod 107763845443) ^ 9342) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 38414954730 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 107763845443) ^ 37371 = 40251359968 := by
        calc
          (2 : ZMod 107763845443) ^ 37371 = (2 : ZMod 107763845443) ^ (18685 + 18685 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 18685 * (2 : ZMod 107763845443) ^ 18685) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 40251359968 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 107763845443) ^ 74742 = 89990625594 := by
        calc
          (2 : ZMod 107763845443) ^ 74742 = (2 : ZMod 107763845443) ^ (37371 + 37371) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 37371 * (2 : ZMod 107763845443) ^ 37371 := by rw [pow_add]
          _ = 89990625594 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 107763845443) ^ 149485 = 37665672495 := by
        calc
          (2 : ZMod 107763845443) ^ 149485 = (2 : ZMod 107763845443) ^ (74742 + 74742 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 74742 * (2 : ZMod 107763845443) ^ 74742) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 37665672495 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 107763845443) ^ 298971 = 95361651148 := by
        calc
          (2 : ZMod 107763845443) ^ 298971 = (2 : ZMod 107763845443) ^ (149485 + 149485 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 149485 * (2 : ZMod 107763845443) ^ 149485) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 95361651148 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 107763845443) ^ 597943 = 100623246352 := by
        calc
          (2 : ZMod 107763845443) ^ 597943 = (2 : ZMod 107763845443) ^ (298971 + 298971 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 298971 * (2 : ZMod 107763845443) ^ 298971) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 100623246352 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 107763845443) ^ 1195887 = 7737395636 := by
        calc
          (2 : ZMod 107763845443) ^ 1195887 = (2 : ZMod 107763845443) ^ (597943 + 597943 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 597943 * (2 : ZMod 107763845443) ^ 597943) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 7737395636 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 107763845443) ^ 2391775 = 58155111513 := by
        calc
          (2 : ZMod 107763845443) ^ 2391775 = (2 : ZMod 107763845443) ^ (1195887 + 1195887 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1195887 * (2 : ZMod 107763845443) ^ 1195887) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 58155111513 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 107763845443) ^ 4783551 = 99218170950 := by
        calc
          (2 : ZMod 107763845443) ^ 4783551 = (2 : ZMod 107763845443) ^ (2391775 + 2391775 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 2391775 * (2 : ZMod 107763845443) ^ 2391775) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 99218170950 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 107763845443) ^ 9567102 = 17239112319 := by
        calc
          (2 : ZMod 107763845443) ^ 9567102 = (2 : ZMod 107763845443) ^ (4783551 + 4783551) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 4783551 * (2 : ZMod 107763845443) ^ 4783551 := by rw [pow_add]
          _ = 17239112319 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 107763845443) ^ 19134205 = 18446628554 := by
        calc
          (2 : ZMod 107763845443) ^ 19134205 = (2 : ZMod 107763845443) ^ (9567102 + 9567102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 9567102 * (2 : ZMod 107763845443) ^ 9567102) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 18446628554 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 107763845443) ^ 38268411 = 34673601785 := by
        calc
          (2 : ZMod 107763845443) ^ 38268411 = (2 : ZMod 107763845443) ^ (19134205 + 19134205 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 19134205 * (2 : ZMod 107763845443) ^ 19134205) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 34673601785 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 107763845443) ^ 76536822 = 84259192533 := by
        calc
          (2 : ZMod 107763845443) ^ 76536822 = (2 : ZMod 107763845443) ^ (38268411 + 38268411) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 38268411 * (2 : ZMod 107763845443) ^ 38268411 := by rw [pow_add]
          _ = 84259192533 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 107763845443) ^ 153073644 = 35306445608 := by
        calc
          (2 : ZMod 107763845443) ^ 153073644 = (2 : ZMod 107763845443) ^ (76536822 + 76536822) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 76536822 * (2 : ZMod 107763845443) ^ 76536822 := by rw [pow_add]
          _ = 35306445608 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 107763845443) ^ 306147288 = 12459968437 := by
        calc
          (2 : ZMod 107763845443) ^ 306147288 = (2 : ZMod 107763845443) ^ (153073644 + 153073644) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 153073644 * (2 : ZMod 107763845443) ^ 153073644 := by rw [pow_add]
          _ = 12459968437 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 107763845443) ^ 612294576 = 55259898198 := by
        calc
          (2 : ZMod 107763845443) ^ 612294576 = (2 : ZMod 107763845443) ^ (306147288 + 306147288) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 306147288 * (2 : ZMod 107763845443) ^ 306147288 := by rw [pow_add]
          _ = 55259898198 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 107763845443) ^ 1224589152 = 26327741647 := by
        calc
          (2 : ZMod 107763845443) ^ 1224589152 = (2 : ZMod 107763845443) ^ (612294576 + 612294576) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 612294576 * (2 : ZMod 107763845443) ^ 612294576 := by rw [pow_add]
          _ = 26327741647 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 107763845443) ^ 2449178305 = 29318924075 := by
        calc
          (2 : ZMod 107763845443) ^ 2449178305 = (2 : ZMod 107763845443) ^ (1224589152 + 1224589152 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 1224589152 * (2 : ZMod 107763845443) ^ 1224589152) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 29318924075 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 107763845443) ^ 4898356611 = 3507200984 := by
        calc
          (2 : ZMod 107763845443) ^ 4898356611 = (2 : ZMod 107763845443) ^ (2449178305 + 2449178305 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 2449178305 * (2 : ZMod 107763845443) ^ 2449178305) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 3507200984 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 107763845443) ^ 9796713222 = 90119252410 := by
        calc
          (2 : ZMod 107763845443) ^ 9796713222 = (2 : ZMod 107763845443) ^ (4898356611 + 4898356611) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 4898356611 * (2 : ZMod 107763845443) ^ 4898356611 := by rw [pow_add]
          _ = 90119252410 := by rw [factor_2_32]; decide
      change (2 : ZMod 107763845443) ^ 9796713222 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (2 : ZMod 107763845443) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 107763845443) ^ 2 = 4 := by
        calc
          (2 : ZMod 107763845443) ^ 2 = (2 : ZMod 107763845443) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 1 * (2 : ZMod 107763845443) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 107763845443) ^ 4 = 16 := by
        calc
          (2 : ZMod 107763845443) ^ 4 = (2 : ZMod 107763845443) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 2 * (2 : ZMod 107763845443) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 107763845443) ^ 8 = 256 := by
        calc
          (2 : ZMod 107763845443) ^ 8 = (2 : ZMod 107763845443) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 4 * (2 : ZMod 107763845443) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 107763845443) ^ 16 = 65536 := by
        calc
          (2 : ZMod 107763845443) ^ 16 = (2 : ZMod 107763845443) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 8 * (2 : ZMod 107763845443) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 107763845443) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 107763845443) ^ 33 = (2 : ZMod 107763845443) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = ((2 : ZMod 107763845443) ^ 16 * (2 : ZMod 107763845443) ^ 16) * (2 : ZMod 107763845443) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 107763845443) ^ 66 = 39628557601 := by
        calc
          (2 : ZMod 107763845443) ^ 66 = (2 : ZMod 107763845443) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 107763845443) ^ n) (by norm_num)
          _ = (2 : ZMod 107763845443) ^ 33 * (2 : ZMod 107763845443) ^ 33 := by rw [pow_add]
          _ = 39628557601 := by rw [factor_3_5]; decide
      change (2 : ZMod 107763845443) ^ 66 ≠ 1
      rw [factor_3_6]
      decide

#print axioms prime_lucas_107763845443

end TotientTailPeriodKiller
end Erdos249257
