import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_36392024419 : Nat.Prime 36392024419 := by
  apply lucas_primality 36392024419 (2 : ZMod 36392024419)
  ·
      have fermat_0 : (2 : ZMod 36392024419) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 36392024419) ^ 2 = 4 := by
        calc
          (2 : ZMod 36392024419) ^ 2 = (2 : ZMod 36392024419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1 * (2 : ZMod 36392024419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 36392024419) ^ 4 = 16 := by
        calc
          (2 : ZMod 36392024419) ^ 4 = (2 : ZMod 36392024419) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2 * (2 : ZMod 36392024419) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 36392024419) ^ 8 = 256 := by
        calc
          (2 : ZMod 36392024419) ^ 8 = (2 : ZMod 36392024419) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 4 * (2 : ZMod 36392024419) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 36392024419) ^ 16 = 65536 := by
        calc
          (2 : ZMod 36392024419) ^ 16 = (2 : ZMod 36392024419) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 8 * (2 : ZMod 36392024419) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 36392024419) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 36392024419) ^ 33 = (2 : ZMod 36392024419) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 16 * (2 : ZMod 36392024419) ^ 16) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 36392024419) ^ 67 = 3198434889 := by
        calc
          (2 : ZMod 36392024419) ^ 67 = (2 : ZMod 36392024419) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 33 * (2 : ZMod 36392024419) ^ 33) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 3198434889 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 36392024419) ^ 135 = 2643227076 := by
        calc
          (2 : ZMod 36392024419) ^ 135 = (2 : ZMod 36392024419) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 67 * (2 : ZMod 36392024419) ^ 67) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 2643227076 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 36392024419) ^ 271 = 12646144636 := by
        calc
          (2 : ZMod 36392024419) ^ 271 = (2 : ZMod 36392024419) ^ (135 + 135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 135 * (2 : ZMod 36392024419) ^ 135) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 12646144636 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 36392024419) ^ 542 = 16970554959 := by
        calc
          (2 : ZMod 36392024419) ^ 542 = (2 : ZMod 36392024419) ^ (271 + 271) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 271 * (2 : ZMod 36392024419) ^ 271 := by rw [pow_add]
          _ = 16970554959 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 36392024419) ^ 1084 = 26511821940 := by
        calc
          (2 : ZMod 36392024419) ^ 1084 = (2 : ZMod 36392024419) ^ (542 + 542) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 542 * (2 : ZMod 36392024419) ^ 542 := by rw [pow_add]
          _ = 26511821940 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 36392024419) ^ 2169 = 7168896553 := by
        calc
          (2 : ZMod 36392024419) ^ 2169 = (2 : ZMod 36392024419) ^ (1084 + 1084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 1084 * (2 : ZMod 36392024419) ^ 1084) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 7168896553 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 36392024419) ^ 4338 = 8680421998 := by
        calc
          (2 : ZMod 36392024419) ^ 4338 = (2 : ZMod 36392024419) ^ (2169 + 2169) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2169 * (2 : ZMod 36392024419) ^ 2169 := by rw [pow_add]
          _ = 8680421998 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 36392024419) ^ 8676 = 18476317389 := by
        calc
          (2 : ZMod 36392024419) ^ 8676 = (2 : ZMod 36392024419) ^ (4338 + 4338) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 4338 * (2 : ZMod 36392024419) ^ 4338 := by rw [pow_add]
          _ = 18476317389 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 36392024419) ^ 17353 = 6734994404 := by
        calc
          (2 : ZMod 36392024419) ^ 17353 = (2 : ZMod 36392024419) ^ (8676 + 8676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 8676 * (2 : ZMod 36392024419) ^ 8676) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 6734994404 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 36392024419) ^ 34706 = 13399236657 := by
        calc
          (2 : ZMod 36392024419) ^ 34706 = (2 : ZMod 36392024419) ^ (17353 + 17353) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 17353 * (2 : ZMod 36392024419) ^ 17353 := by rw [pow_add]
          _ = 13399236657 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 36392024419) ^ 69412 = 7497901649 := by
        calc
          (2 : ZMod 36392024419) ^ 69412 = (2 : ZMod 36392024419) ^ (34706 + 34706) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 34706 * (2 : ZMod 36392024419) ^ 34706 := by rw [pow_add]
          _ = 7497901649 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 36392024419) ^ 138824 = 5254616628 := by
        calc
          (2 : ZMod 36392024419) ^ 138824 = (2 : ZMod 36392024419) ^ (69412 + 69412) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 69412 * (2 : ZMod 36392024419) ^ 69412 := by rw [pow_add]
          _ = 5254616628 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 36392024419) ^ 277649 = 6769098376 := by
        calc
          (2 : ZMod 36392024419) ^ 277649 = (2 : ZMod 36392024419) ^ (138824 + 138824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 138824 * (2 : ZMod 36392024419) ^ 138824) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 6769098376 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 36392024419) ^ 555298 = 35693897515 := by
        calc
          (2 : ZMod 36392024419) ^ 555298 = (2 : ZMod 36392024419) ^ (277649 + 277649) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 277649 * (2 : ZMod 36392024419) ^ 277649 := by rw [pow_add]
          _ = 35693897515 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 36392024419) ^ 1110596 = 4472508403 := by
        calc
          (2 : ZMod 36392024419) ^ 1110596 = (2 : ZMod 36392024419) ^ (555298 + 555298) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 555298 * (2 : ZMod 36392024419) ^ 555298 := by rw [pow_add]
          _ = 4472508403 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 36392024419) ^ 2221192 = 1560827557 := by
        calc
          (2 : ZMod 36392024419) ^ 2221192 = (2 : ZMod 36392024419) ^ (1110596 + 1110596) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1110596 * (2 : ZMod 36392024419) ^ 1110596 := by rw [pow_add]
          _ = 1560827557 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 36392024419) ^ 4442385 = 30230541523 := by
        calc
          (2 : ZMod 36392024419) ^ 4442385 = (2 : ZMod 36392024419) ^ (2221192 + 2221192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 2221192 * (2 : ZMod 36392024419) ^ 2221192) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 30230541523 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 36392024419) ^ 8884771 = 21186534782 := by
        calc
          (2 : ZMod 36392024419) ^ 8884771 = (2 : ZMod 36392024419) ^ (4442385 + 4442385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 4442385 * (2 : ZMod 36392024419) ^ 4442385) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 21186534782 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 36392024419) ^ 17769543 = 17627533936 := by
        calc
          (2 : ZMod 36392024419) ^ 17769543 = (2 : ZMod 36392024419) ^ (8884771 + 8884771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 8884771 * (2 : ZMod 36392024419) ^ 8884771) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 17627533936 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 36392024419) ^ 35539086 = 11094553582 := by
        calc
          (2 : ZMod 36392024419) ^ 35539086 = (2 : ZMod 36392024419) ^ (17769543 + 17769543) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 17769543 * (2 : ZMod 36392024419) ^ 17769543 := by rw [pow_add]
          _ = 11094553582 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 36392024419) ^ 71078172 = 8065717348 := by
        calc
          (2 : ZMod 36392024419) ^ 71078172 = (2 : ZMod 36392024419) ^ (35539086 + 35539086) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 35539086 * (2 : ZMod 36392024419) ^ 35539086 := by rw [pow_add]
          _ = 8065717348 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 36392024419) ^ 142156345 = 3998613869 := by
        calc
          (2 : ZMod 36392024419) ^ 142156345 = (2 : ZMod 36392024419) ^ (71078172 + 71078172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 71078172 * (2 : ZMod 36392024419) ^ 71078172) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 3998613869 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 36392024419) ^ 284312690 = 12131877395 := by
        calc
          (2 : ZMod 36392024419) ^ 284312690 = (2 : ZMod 36392024419) ^ (142156345 + 142156345) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 142156345 * (2 : ZMod 36392024419) ^ 142156345 := by rw [pow_add]
          _ = 12131877395 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 36392024419) ^ 568625381 = 21512631558 := by
        calc
          (2 : ZMod 36392024419) ^ 568625381 = (2 : ZMod 36392024419) ^ (284312690 + 284312690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 284312690 * (2 : ZMod 36392024419) ^ 284312690) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 21512631558 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 36392024419) ^ 1137250763 = 31386842432 := by
        calc
          (2 : ZMod 36392024419) ^ 1137250763 = (2 : ZMod 36392024419) ^ (568625381 + 568625381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 568625381 * (2 : ZMod 36392024419) ^ 568625381) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 31386842432 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 36392024419) ^ 2274501526 = 24665441368 := by
        calc
          (2 : ZMod 36392024419) ^ 2274501526 = (2 : ZMod 36392024419) ^ (1137250763 + 1137250763) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1137250763 * (2 : ZMod 36392024419) ^ 1137250763 := by rw [pow_add]
          _ = 24665441368 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 36392024419) ^ 4549003052 = 14656024122 := by
        calc
          (2 : ZMod 36392024419) ^ 4549003052 = (2 : ZMod 36392024419) ^ (2274501526 + 2274501526) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2274501526 * (2 : ZMod 36392024419) ^ 2274501526 := by rw [pow_add]
          _ = 14656024122 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 36392024419) ^ 9098006104 = 11773569259 := by
        calc
          (2 : ZMod 36392024419) ^ 9098006104 = (2 : ZMod 36392024419) ^ (4549003052 + 4549003052) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 4549003052 * (2 : ZMod 36392024419) ^ 4549003052 := by rw [pow_add]
          _ = 11773569259 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 36392024419) ^ 18196012209 = 36392024418 := by
        calc
          (2 : ZMod 36392024419) ^ 18196012209 = (2 : ZMod 36392024419) ^ (9098006104 + 9098006104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 9098006104 * (2 : ZMod 36392024419) ^ 9098006104) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 36392024418 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 36392024419) ^ 36392024418 = 1 := by
        calc
          (2 : ZMod 36392024419) ^ 36392024418 = (2 : ZMod 36392024419) ^ (18196012209 + 18196012209) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 18196012209 * (2 : ZMod 36392024419) ^ 18196012209 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (233, 1), (389, 1), (66919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (233, 1), (389, 1), (66919, 1)] : List FactorBlock).map factorBlockValue).prod = 36392024419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 36392024419) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 36392024419) ^ 2 = 4 := by
        calc
          (2 : ZMod 36392024419) ^ 2 = (2 : ZMod 36392024419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1 * (2 : ZMod 36392024419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 36392024419) ^ 4 = 16 := by
        calc
          (2 : ZMod 36392024419) ^ 4 = (2 : ZMod 36392024419) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2 * (2 : ZMod 36392024419) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 36392024419) ^ 8 = 256 := by
        calc
          (2 : ZMod 36392024419) ^ 8 = (2 : ZMod 36392024419) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 4 * (2 : ZMod 36392024419) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 36392024419) ^ 16 = 65536 := by
        calc
          (2 : ZMod 36392024419) ^ 16 = (2 : ZMod 36392024419) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 8 * (2 : ZMod 36392024419) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 36392024419) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 36392024419) ^ 33 = (2 : ZMod 36392024419) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 16 * (2 : ZMod 36392024419) ^ 16) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 36392024419) ^ 67 = 3198434889 := by
        calc
          (2 : ZMod 36392024419) ^ 67 = (2 : ZMod 36392024419) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 33 * (2 : ZMod 36392024419) ^ 33) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 3198434889 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 36392024419) ^ 135 = 2643227076 := by
        calc
          (2 : ZMod 36392024419) ^ 135 = (2 : ZMod 36392024419) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 67 * (2 : ZMod 36392024419) ^ 67) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 2643227076 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 36392024419) ^ 271 = 12646144636 := by
        calc
          (2 : ZMod 36392024419) ^ 271 = (2 : ZMod 36392024419) ^ (135 + 135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 135 * (2 : ZMod 36392024419) ^ 135) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 12646144636 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 36392024419) ^ 542 = 16970554959 := by
        calc
          (2 : ZMod 36392024419) ^ 542 = (2 : ZMod 36392024419) ^ (271 + 271) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 271 * (2 : ZMod 36392024419) ^ 271 := by rw [pow_add]
          _ = 16970554959 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 36392024419) ^ 1084 = 26511821940 := by
        calc
          (2 : ZMod 36392024419) ^ 1084 = (2 : ZMod 36392024419) ^ (542 + 542) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 542 * (2 : ZMod 36392024419) ^ 542 := by rw [pow_add]
          _ = 26511821940 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 36392024419) ^ 2169 = 7168896553 := by
        calc
          (2 : ZMod 36392024419) ^ 2169 = (2 : ZMod 36392024419) ^ (1084 + 1084 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 1084 * (2 : ZMod 36392024419) ^ 1084) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 7168896553 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 36392024419) ^ 4338 = 8680421998 := by
        calc
          (2 : ZMod 36392024419) ^ 4338 = (2 : ZMod 36392024419) ^ (2169 + 2169) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2169 * (2 : ZMod 36392024419) ^ 2169 := by rw [pow_add]
          _ = 8680421998 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 36392024419) ^ 8676 = 18476317389 := by
        calc
          (2 : ZMod 36392024419) ^ 8676 = (2 : ZMod 36392024419) ^ (4338 + 4338) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 4338 * (2 : ZMod 36392024419) ^ 4338 := by rw [pow_add]
          _ = 18476317389 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 36392024419) ^ 17353 = 6734994404 := by
        calc
          (2 : ZMod 36392024419) ^ 17353 = (2 : ZMod 36392024419) ^ (8676 + 8676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 8676 * (2 : ZMod 36392024419) ^ 8676) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 6734994404 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 36392024419) ^ 34706 = 13399236657 := by
        calc
          (2 : ZMod 36392024419) ^ 34706 = (2 : ZMod 36392024419) ^ (17353 + 17353) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 17353 * (2 : ZMod 36392024419) ^ 17353 := by rw [pow_add]
          _ = 13399236657 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 36392024419) ^ 69412 = 7497901649 := by
        calc
          (2 : ZMod 36392024419) ^ 69412 = (2 : ZMod 36392024419) ^ (34706 + 34706) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 34706 * (2 : ZMod 36392024419) ^ 34706 := by rw [pow_add]
          _ = 7497901649 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 36392024419) ^ 138824 = 5254616628 := by
        calc
          (2 : ZMod 36392024419) ^ 138824 = (2 : ZMod 36392024419) ^ (69412 + 69412) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 69412 * (2 : ZMod 36392024419) ^ 69412 := by rw [pow_add]
          _ = 5254616628 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 36392024419) ^ 277649 = 6769098376 := by
        calc
          (2 : ZMod 36392024419) ^ 277649 = (2 : ZMod 36392024419) ^ (138824 + 138824 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 138824 * (2 : ZMod 36392024419) ^ 138824) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 6769098376 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 36392024419) ^ 555298 = 35693897515 := by
        calc
          (2 : ZMod 36392024419) ^ 555298 = (2 : ZMod 36392024419) ^ (277649 + 277649) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 277649 * (2 : ZMod 36392024419) ^ 277649 := by rw [pow_add]
          _ = 35693897515 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 36392024419) ^ 1110596 = 4472508403 := by
        calc
          (2 : ZMod 36392024419) ^ 1110596 = (2 : ZMod 36392024419) ^ (555298 + 555298) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 555298 * (2 : ZMod 36392024419) ^ 555298 := by rw [pow_add]
          _ = 4472508403 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 36392024419) ^ 2221192 = 1560827557 := by
        calc
          (2 : ZMod 36392024419) ^ 2221192 = (2 : ZMod 36392024419) ^ (1110596 + 1110596) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1110596 * (2 : ZMod 36392024419) ^ 1110596 := by rw [pow_add]
          _ = 1560827557 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 36392024419) ^ 4442385 = 30230541523 := by
        calc
          (2 : ZMod 36392024419) ^ 4442385 = (2 : ZMod 36392024419) ^ (2221192 + 2221192 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 2221192 * (2 : ZMod 36392024419) ^ 2221192) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 30230541523 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 36392024419) ^ 8884771 = 21186534782 := by
        calc
          (2 : ZMod 36392024419) ^ 8884771 = (2 : ZMod 36392024419) ^ (4442385 + 4442385 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 4442385 * (2 : ZMod 36392024419) ^ 4442385) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 21186534782 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 36392024419) ^ 17769543 = 17627533936 := by
        calc
          (2 : ZMod 36392024419) ^ 17769543 = (2 : ZMod 36392024419) ^ (8884771 + 8884771 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 8884771 * (2 : ZMod 36392024419) ^ 8884771) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 17627533936 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 36392024419) ^ 35539086 = 11094553582 := by
        calc
          (2 : ZMod 36392024419) ^ 35539086 = (2 : ZMod 36392024419) ^ (17769543 + 17769543) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 17769543 * (2 : ZMod 36392024419) ^ 17769543 := by rw [pow_add]
          _ = 11094553582 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 36392024419) ^ 71078172 = 8065717348 := by
        calc
          (2 : ZMod 36392024419) ^ 71078172 = (2 : ZMod 36392024419) ^ (35539086 + 35539086) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 35539086 * (2 : ZMod 36392024419) ^ 35539086 := by rw [pow_add]
          _ = 8065717348 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 36392024419) ^ 142156345 = 3998613869 := by
        calc
          (2 : ZMod 36392024419) ^ 142156345 = (2 : ZMod 36392024419) ^ (71078172 + 71078172 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 71078172 * (2 : ZMod 36392024419) ^ 71078172) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 3998613869 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 36392024419) ^ 284312690 = 12131877395 := by
        calc
          (2 : ZMod 36392024419) ^ 284312690 = (2 : ZMod 36392024419) ^ (142156345 + 142156345) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 142156345 * (2 : ZMod 36392024419) ^ 142156345 := by rw [pow_add]
          _ = 12131877395 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 36392024419) ^ 568625381 = 21512631558 := by
        calc
          (2 : ZMod 36392024419) ^ 568625381 = (2 : ZMod 36392024419) ^ (284312690 + 284312690 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 284312690 * (2 : ZMod 36392024419) ^ 284312690) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 21512631558 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 36392024419) ^ 1137250763 = 31386842432 := by
        calc
          (2 : ZMod 36392024419) ^ 1137250763 = (2 : ZMod 36392024419) ^ (568625381 + 568625381 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 568625381 * (2 : ZMod 36392024419) ^ 568625381) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 31386842432 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 36392024419) ^ 2274501526 = 24665441368 := by
        calc
          (2 : ZMod 36392024419) ^ 2274501526 = (2 : ZMod 36392024419) ^ (1137250763 + 1137250763) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1137250763 * (2 : ZMod 36392024419) ^ 1137250763 := by rw [pow_add]
          _ = 24665441368 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 36392024419) ^ 4549003052 = 14656024122 := by
        calc
          (2 : ZMod 36392024419) ^ 4549003052 = (2 : ZMod 36392024419) ^ (2274501526 + 2274501526) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2274501526 * (2 : ZMod 36392024419) ^ 2274501526 := by rw [pow_add]
          _ = 14656024122 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 36392024419) ^ 9098006104 = 11773569259 := by
        calc
          (2 : ZMod 36392024419) ^ 9098006104 = (2 : ZMod 36392024419) ^ (4549003052 + 4549003052) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 4549003052 * (2 : ZMod 36392024419) ^ 4549003052 := by rw [pow_add]
          _ = 11773569259 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 36392024419) ^ 18196012209 = 36392024418 := by
        calc
          (2 : ZMod 36392024419) ^ 18196012209 = (2 : ZMod 36392024419) ^ (9098006104 + 9098006104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 9098006104 * (2 : ZMod 36392024419) ^ 9098006104) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 36392024418 := by rw [factor_0_33]; decide
      change (2 : ZMod 36392024419) ^ 18196012209 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (2 : ZMod 36392024419) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 36392024419) ^ 2 = 4 := by
        calc
          (2 : ZMod 36392024419) ^ 2 = (2 : ZMod 36392024419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1 * (2 : ZMod 36392024419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 36392024419) ^ 5 = 32 := by
        calc
          (2 : ZMod 36392024419) ^ 5 = (2 : ZMod 36392024419) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 2 * (2 : ZMod 36392024419) ^ 2) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 36392024419) ^ 11 = 2048 := by
        calc
          (2 : ZMod 36392024419) ^ 11 = (2 : ZMod 36392024419) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 5 * (2 : ZMod 36392024419) ^ 5) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 36392024419) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 36392024419) ^ 22 = (2 : ZMod 36392024419) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 11 * (2 : ZMod 36392024419) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 36392024419) ^ 45 = 29676500078 := by
        calc
          (2 : ZMod 36392024419) ^ 45 = (2 : ZMod 36392024419) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 22 * (2 : ZMod 36392024419) ^ 22) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 29676500078 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 36392024419) ^ 90 = 32574192572 := by
        calc
          (2 : ZMod 36392024419) ^ 90 = (2 : ZMod 36392024419) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 45 * (2 : ZMod 36392024419) ^ 45 := by rw [pow_add]
          _ = 32574192572 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 36392024419) ^ 180 = 17782174672 := by
        calc
          (2 : ZMod 36392024419) ^ 180 = (2 : ZMod 36392024419) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 90 * (2 : ZMod 36392024419) ^ 90 := by rw [pow_add]
          _ = 17782174672 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 36392024419) ^ 361 = 25531657357 := by
        calc
          (2 : ZMod 36392024419) ^ 361 = (2 : ZMod 36392024419) ^ (180 + 180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 180 * (2 : ZMod 36392024419) ^ 180) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 25531657357 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 36392024419) ^ 723 = 1364067771 := by
        calc
          (2 : ZMod 36392024419) ^ 723 = (2 : ZMod 36392024419) ^ (361 + 361 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 361 * (2 : ZMod 36392024419) ^ 361) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 1364067771 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 36392024419) ^ 1446 = 18238521470 := by
        calc
          (2 : ZMod 36392024419) ^ 1446 = (2 : ZMod 36392024419) ^ (723 + 723) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 723 * (2 : ZMod 36392024419) ^ 723 := by rw [pow_add]
          _ = 18238521470 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 36392024419) ^ 2892 = 353737520 := by
        calc
          (2 : ZMod 36392024419) ^ 2892 = (2 : ZMod 36392024419) ^ (1446 + 1446) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1446 * (2 : ZMod 36392024419) ^ 1446 := by rw [pow_add]
          _ = 353737520 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 36392024419) ^ 5784 = 5469534057 := by
        calc
          (2 : ZMod 36392024419) ^ 5784 = (2 : ZMod 36392024419) ^ (2892 + 2892) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2892 * (2 : ZMod 36392024419) ^ 2892 := by rw [pow_add]
          _ = 5469534057 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 36392024419) ^ 11568 = 21466989060 := by
        calc
          (2 : ZMod 36392024419) ^ 11568 = (2 : ZMod 36392024419) ^ (5784 + 5784) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 5784 * (2 : ZMod 36392024419) ^ 5784 := by rw [pow_add]
          _ = 21466989060 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 36392024419) ^ 23137 = 28303683419 := by
        calc
          (2 : ZMod 36392024419) ^ 23137 = (2 : ZMod 36392024419) ^ (11568 + 11568 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 11568 * (2 : ZMod 36392024419) ^ 11568) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 28303683419 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 36392024419) ^ 46274 = 2742434155 := by
        calc
          (2 : ZMod 36392024419) ^ 46274 = (2 : ZMod 36392024419) ^ (23137 + 23137) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 23137 * (2 : ZMod 36392024419) ^ 23137 := by rw [pow_add]
          _ = 2742434155 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 36392024419) ^ 92549 = 28372829255 := by
        calc
          (2 : ZMod 36392024419) ^ 92549 = (2 : ZMod 36392024419) ^ (46274 + 46274 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 46274 * (2 : ZMod 36392024419) ^ 46274) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 28372829255 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 36392024419) ^ 185099 = 25727964468 := by
        calc
          (2 : ZMod 36392024419) ^ 185099 = (2 : ZMod 36392024419) ^ (92549 + 92549 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 92549 * (2 : ZMod 36392024419) ^ 92549) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 25727964468 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 36392024419) ^ 370198 = 10822146947 := by
        calc
          (2 : ZMod 36392024419) ^ 370198 = (2 : ZMod 36392024419) ^ (185099 + 185099) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 185099 * (2 : ZMod 36392024419) ^ 185099 := by rw [pow_add]
          _ = 10822146947 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 36392024419) ^ 740397 = 22894072625 := by
        calc
          (2 : ZMod 36392024419) ^ 740397 = (2 : ZMod 36392024419) ^ (370198 + 370198 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 370198 * (2 : ZMod 36392024419) ^ 370198) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 22894072625 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 36392024419) ^ 1480795 = 10409185437 := by
        calc
          (2 : ZMod 36392024419) ^ 1480795 = (2 : ZMod 36392024419) ^ (740397 + 740397 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 740397 * (2 : ZMod 36392024419) ^ 740397) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 10409185437 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 36392024419) ^ 2961590 = 30549039220 := by
        calc
          (2 : ZMod 36392024419) ^ 2961590 = (2 : ZMod 36392024419) ^ (1480795 + 1480795) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1480795 * (2 : ZMod 36392024419) ^ 1480795 := by rw [pow_add]
          _ = 30549039220 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 36392024419) ^ 5923181 = 3342084680 := by
        calc
          (2 : ZMod 36392024419) ^ 5923181 = (2 : ZMod 36392024419) ^ (2961590 + 2961590 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 2961590 * (2 : ZMod 36392024419) ^ 2961590) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 3342084680 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 36392024419) ^ 11846362 = 21702931889 := by
        calc
          (2 : ZMod 36392024419) ^ 11846362 = (2 : ZMod 36392024419) ^ (5923181 + 5923181) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 5923181 * (2 : ZMod 36392024419) ^ 5923181 := by rw [pow_add]
          _ = 21702931889 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 36392024419) ^ 23692724 = 23142886336 := by
        calc
          (2 : ZMod 36392024419) ^ 23692724 = (2 : ZMod 36392024419) ^ (11846362 + 11846362) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 11846362 * (2 : ZMod 36392024419) ^ 11846362 := by rw [pow_add]
          _ = 23142886336 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 36392024419) ^ 47385448 = 27682501509 := by
        calc
          (2 : ZMod 36392024419) ^ 47385448 = (2 : ZMod 36392024419) ^ (23692724 + 23692724) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 23692724 * (2 : ZMod 36392024419) ^ 23692724 := by rw [pow_add]
          _ = 27682501509 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 36392024419) ^ 94770896 = 4833092089 := by
        calc
          (2 : ZMod 36392024419) ^ 94770896 = (2 : ZMod 36392024419) ^ (47385448 + 47385448) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 47385448 * (2 : ZMod 36392024419) ^ 47385448 := by rw [pow_add]
          _ = 4833092089 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 36392024419) ^ 189541793 = 27529292922 := by
        calc
          (2 : ZMod 36392024419) ^ 189541793 = (2 : ZMod 36392024419) ^ (94770896 + 94770896 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 94770896 * (2 : ZMod 36392024419) ^ 94770896) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 27529292922 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 36392024419) ^ 379083587 = 18187734825 := by
        calc
          (2 : ZMod 36392024419) ^ 379083587 = (2 : ZMod 36392024419) ^ (189541793 + 189541793 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 189541793 * (2 : ZMod 36392024419) ^ 189541793) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 18187734825 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 36392024419) ^ 758167175 = 32412396355 := by
        calc
          (2 : ZMod 36392024419) ^ 758167175 = (2 : ZMod 36392024419) ^ (379083587 + 379083587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 379083587 * (2 : ZMod 36392024419) ^ 379083587) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 32412396355 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 36392024419) ^ 1516334350 = 25243538622 := by
        calc
          (2 : ZMod 36392024419) ^ 1516334350 = (2 : ZMod 36392024419) ^ (758167175 + 758167175) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 758167175 * (2 : ZMod 36392024419) ^ 758167175 := by rw [pow_add]
          _ = 25243538622 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 36392024419) ^ 3032668701 = 28596837239 := by
        calc
          (2 : ZMod 36392024419) ^ 3032668701 = (2 : ZMod 36392024419) ^ (1516334350 + 1516334350 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 1516334350 * (2 : ZMod 36392024419) ^ 1516334350) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 28596837239 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 36392024419) ^ 6065337403 = 11272557069 := by
        calc
          (2 : ZMod 36392024419) ^ 6065337403 = (2 : ZMod 36392024419) ^ (3032668701 + 3032668701 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 3032668701 * (2 : ZMod 36392024419) ^ 3032668701) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 11272557069 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 36392024419) ^ 12130674806 = 11272557068 := by
        calc
          (2 : ZMod 36392024419) ^ 12130674806 = (2 : ZMod 36392024419) ^ (6065337403 + 6065337403) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 6065337403 * (2 : ZMod 36392024419) ^ 6065337403 := by rw [pow_add]
          _ = 11272557068 := by rw [factor_1_32]; decide
      change (2 : ZMod 36392024419) ^ 12130674806 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (2 : ZMod 36392024419) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 36392024419) ^ 2 = 4 := by
        calc
          (2 : ZMod 36392024419) ^ 2 = (2 : ZMod 36392024419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1 * (2 : ZMod 36392024419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 36392024419) ^ 4 = 16 := by
        calc
          (2 : ZMod 36392024419) ^ 4 = (2 : ZMod 36392024419) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2 * (2 : ZMod 36392024419) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 36392024419) ^ 9 = 512 := by
        calc
          (2 : ZMod 36392024419) ^ 9 = (2 : ZMod 36392024419) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 4 * (2 : ZMod 36392024419) ^ 4) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 36392024419) ^ 18 = 262144 := by
        calc
          (2 : ZMod 36392024419) ^ 18 = (2 : ZMod 36392024419) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 9 * (2 : ZMod 36392024419) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 36392024419) ^ 37 = 28262880215 := by
        calc
          (2 : ZMod 36392024419) ^ 37 = (2 : ZMod 36392024419) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 18 * (2 : ZMod 36392024419) ^ 18) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 28262880215 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 36392024419) ^ 74 = 9087397183 := by
        calc
          (2 : ZMod 36392024419) ^ 74 = (2 : ZMod 36392024419) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 37 * (2 : ZMod 36392024419) ^ 37 := by rw [pow_add]
          _ = 9087397183 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 36392024419) ^ 148 = 61677287 := by
        calc
          (2 : ZMod 36392024419) ^ 148 = (2 : ZMod 36392024419) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 74 * (2 : ZMod 36392024419) ^ 74 := by rw [pow_add]
          _ = 61677287 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 36392024419) ^ 297 = 22446300179 := by
        calc
          (2 : ZMod 36392024419) ^ 297 = (2 : ZMod 36392024419) ^ (148 + 148 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 148 * (2 : ZMod 36392024419) ^ 148) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 22446300179 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 36392024419) ^ 595 = 14292932712 := by
        calc
          (2 : ZMod 36392024419) ^ 595 = (2 : ZMod 36392024419) ^ (297 + 297 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 297 * (2 : ZMod 36392024419) ^ 297) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 14292932712 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 36392024419) ^ 1191 = 8450544976 := by
        calc
          (2 : ZMod 36392024419) ^ 1191 = (2 : ZMod 36392024419) ^ (595 + 595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 595 * (2 : ZMod 36392024419) ^ 595) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 8450544976 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 36392024419) ^ 2383 = 17376238955 := by
        calc
          (2 : ZMod 36392024419) ^ 2383 = (2 : ZMod 36392024419) ^ (1191 + 1191 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 1191 * (2 : ZMod 36392024419) ^ 1191) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 17376238955 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 36392024419) ^ 4766 = 10233507454 := by
        calc
          (2 : ZMod 36392024419) ^ 4766 = (2 : ZMod 36392024419) ^ (2383 + 2383) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2383 * (2 : ZMod 36392024419) ^ 2383 := by rw [pow_add]
          _ = 10233507454 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 36392024419) ^ 9533 = 28432020997 := by
        calc
          (2 : ZMod 36392024419) ^ 9533 = (2 : ZMod 36392024419) ^ (4766 + 4766 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 4766 * (2 : ZMod 36392024419) ^ 4766) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 28432020997 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 36392024419) ^ 19066 = 24513814345 := by
        calc
          (2 : ZMod 36392024419) ^ 19066 = (2 : ZMod 36392024419) ^ (9533 + 9533) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 9533 * (2 : ZMod 36392024419) ^ 9533 := by rw [pow_add]
          _ = 24513814345 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 36392024419) ^ 38132 = 1910844823 := by
        calc
          (2 : ZMod 36392024419) ^ 38132 = (2 : ZMod 36392024419) ^ (19066 + 19066) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 19066 * (2 : ZMod 36392024419) ^ 19066 := by rw [pow_add]
          _ = 1910844823 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 36392024419) ^ 76264 = 677710300 := by
        calc
          (2 : ZMod 36392024419) ^ 76264 = (2 : ZMod 36392024419) ^ (38132 + 38132) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 38132 * (2 : ZMod 36392024419) ^ 38132 := by rw [pow_add]
          _ = 677710300 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 36392024419) ^ 152528 = 29390291136 := by
        calc
          (2 : ZMod 36392024419) ^ 152528 = (2 : ZMod 36392024419) ^ (76264 + 76264) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 76264 * (2 : ZMod 36392024419) ^ 76264 := by rw [pow_add]
          _ = 29390291136 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 36392024419) ^ 305056 = 24578678610 := by
        calc
          (2 : ZMod 36392024419) ^ 305056 = (2 : ZMod 36392024419) ^ (152528 + 152528) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 152528 * (2 : ZMod 36392024419) ^ 152528 := by rw [pow_add]
          _ = 24578678610 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 36392024419) ^ 610113 = 21490025022 := by
        calc
          (2 : ZMod 36392024419) ^ 610113 = (2 : ZMod 36392024419) ^ (305056 + 305056 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 305056 * (2 : ZMod 36392024419) ^ 305056) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 21490025022 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 36392024419) ^ 1220226 = 6119396230 := by
        calc
          (2 : ZMod 36392024419) ^ 1220226 = (2 : ZMod 36392024419) ^ (610113 + 610113) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 610113 * (2 : ZMod 36392024419) ^ 610113 := by rw [pow_add]
          _ = 6119396230 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 36392024419) ^ 2440452 = 9468149618 := by
        calc
          (2 : ZMod 36392024419) ^ 2440452 = (2 : ZMod 36392024419) ^ (1220226 + 1220226) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1220226 * (2 : ZMod 36392024419) ^ 1220226 := by rw [pow_add]
          _ = 9468149618 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 36392024419) ^ 4880904 = 31094582058 := by
        calc
          (2 : ZMod 36392024419) ^ 4880904 = (2 : ZMod 36392024419) ^ (2440452 + 2440452) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2440452 * (2 : ZMod 36392024419) ^ 2440452 := by rw [pow_add]
          _ = 31094582058 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 36392024419) ^ 9761809 = 17591290283 := by
        calc
          (2 : ZMod 36392024419) ^ 9761809 = (2 : ZMod 36392024419) ^ (4880904 + 4880904 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 4880904 * (2 : ZMod 36392024419) ^ 4880904) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 17591290283 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 36392024419) ^ 19523618 = 12047309459 := by
        calc
          (2 : ZMod 36392024419) ^ 19523618 = (2 : ZMod 36392024419) ^ (9761809 + 9761809) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 9761809 * (2 : ZMod 36392024419) ^ 9761809 := by rw [pow_add]
          _ = 12047309459 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 36392024419) ^ 39047236 = 16450502221 := by
        calc
          (2 : ZMod 36392024419) ^ 39047236 = (2 : ZMod 36392024419) ^ (19523618 + 19523618) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 19523618 * (2 : ZMod 36392024419) ^ 19523618 := by rw [pow_add]
          _ = 16450502221 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 36392024419) ^ 78094473 = 24602187577 := by
        calc
          (2 : ZMod 36392024419) ^ 78094473 = (2 : ZMod 36392024419) ^ (39047236 + 39047236 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 39047236 * (2 : ZMod 36392024419) ^ 39047236) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 24602187577 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 36392024419) ^ 156188946 = 14843748600 := by
        calc
          (2 : ZMod 36392024419) ^ 156188946 = (2 : ZMod 36392024419) ^ (78094473 + 78094473) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 78094473 * (2 : ZMod 36392024419) ^ 78094473 := by rw [pow_add]
          _ = 14843748600 := by rw [factor_2_26]; decide
      change (2 : ZMod 36392024419) ^ 156188946 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (2 : ZMod 36392024419) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 36392024419) ^ 2 = 4 := by
        calc
          (2 : ZMod 36392024419) ^ 2 = (2 : ZMod 36392024419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1 * (2 : ZMod 36392024419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 36392024419) ^ 5 = 32 := by
        calc
          (2 : ZMod 36392024419) ^ 5 = (2 : ZMod 36392024419) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 2 * (2 : ZMod 36392024419) ^ 2) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 36392024419) ^ 11 = 2048 := by
        calc
          (2 : ZMod 36392024419) ^ 11 = (2 : ZMod 36392024419) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 5 * (2 : ZMod 36392024419) ^ 5) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 36392024419) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 36392024419) ^ 22 = (2 : ZMod 36392024419) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 11 * (2 : ZMod 36392024419) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 36392024419) ^ 44 = 14838250039 := by
        calc
          (2 : ZMod 36392024419) ^ 44 = (2 : ZMod 36392024419) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 22 * (2 : ZMod 36392024419) ^ 22 := by rw [pow_add]
          _ = 14838250039 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 36392024419) ^ 89 = 16287096286 := by
        calc
          (2 : ZMod 36392024419) ^ 89 = (2 : ZMod 36392024419) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 44 * (2 : ZMod 36392024419) ^ 44) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 16287096286 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 36392024419) ^ 178 = 4445543668 := by
        calc
          (2 : ZMod 36392024419) ^ 178 = (2 : ZMod 36392024419) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 89 * (2 : ZMod 36392024419) ^ 89 := by rw [pow_add]
          _ = 4445543668 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 36392024419) ^ 356 = 20131127265 := by
        calc
          (2 : ZMod 36392024419) ^ 356 = (2 : ZMod 36392024419) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 178 * (2 : ZMod 36392024419) ^ 178 := by rw [pow_add]
          _ = 20131127265 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 36392024419) ^ 713 = 20151994056 := by
        calc
          (2 : ZMod 36392024419) ^ 713 = (2 : ZMod 36392024419) ^ (356 + 356 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 356 * (2 : ZMod 36392024419) ^ 356) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 20151994056 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 36392024419) ^ 1427 = 30618484745 := by
        calc
          (2 : ZMod 36392024419) ^ 1427 = (2 : ZMod 36392024419) ^ (713 + 713 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 713 * (2 : ZMod 36392024419) ^ 713) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 30618484745 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 36392024419) ^ 2855 = 7382282699 := by
        calc
          (2 : ZMod 36392024419) ^ 2855 = (2 : ZMod 36392024419) ^ (1427 + 1427 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 1427 * (2 : ZMod 36392024419) ^ 1427) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 7382282699 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 36392024419) ^ 5710 = 31899548173 := by
        calc
          (2 : ZMod 36392024419) ^ 5710 = (2 : ZMod 36392024419) ^ (2855 + 2855) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2855 * (2 : ZMod 36392024419) ^ 2855 := by rw [pow_add]
          _ = 31899548173 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 36392024419) ^ 11420 = 21997067977 := by
        calc
          (2 : ZMod 36392024419) ^ 11420 = (2 : ZMod 36392024419) ^ (5710 + 5710) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 5710 * (2 : ZMod 36392024419) ^ 5710 := by rw [pow_add]
          _ = 21997067977 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 36392024419) ^ 22840 = 11745491492 := by
        calc
          (2 : ZMod 36392024419) ^ 22840 = (2 : ZMod 36392024419) ^ (11420 + 11420) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 11420 * (2 : ZMod 36392024419) ^ 11420 := by rw [pow_add]
          _ = 11745491492 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 36392024419) ^ 45680 = 34601099163 := by
        calc
          (2 : ZMod 36392024419) ^ 45680 = (2 : ZMod 36392024419) ^ (22840 + 22840) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 22840 * (2 : ZMod 36392024419) ^ 22840 := by rw [pow_add]
          _ = 34601099163 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 36392024419) ^ 91360 = 16888635396 := by
        calc
          (2 : ZMod 36392024419) ^ 91360 = (2 : ZMod 36392024419) ^ (45680 + 45680) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 45680 * (2 : ZMod 36392024419) ^ 45680 := by rw [pow_add]
          _ = 16888635396 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 36392024419) ^ 182720 = 32057604919 := by
        calc
          (2 : ZMod 36392024419) ^ 182720 = (2 : ZMod 36392024419) ^ (91360 + 91360) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 91360 * (2 : ZMod 36392024419) ^ 91360 := by rw [pow_add]
          _ = 32057604919 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 36392024419) ^ 365440 = 16783138113 := by
        calc
          (2 : ZMod 36392024419) ^ 365440 = (2 : ZMod 36392024419) ^ (182720 + 182720) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 182720 * (2 : ZMod 36392024419) ^ 182720 := by rw [pow_add]
          _ = 16783138113 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 36392024419) ^ 730880 = 14130289238 := by
        calc
          (2 : ZMod 36392024419) ^ 730880 = (2 : ZMod 36392024419) ^ (365440 + 365440) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 365440 * (2 : ZMod 36392024419) ^ 365440 := by rw [pow_add]
          _ = 14130289238 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 36392024419) ^ 1461761 = 23862947876 := by
        calc
          (2 : ZMod 36392024419) ^ 1461761 = (2 : ZMod 36392024419) ^ (730880 + 730880 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 730880 * (2 : ZMod 36392024419) ^ 730880) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 23862947876 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 36392024419) ^ 2923523 = 7850482358 := by
        calc
          (2 : ZMod 36392024419) ^ 2923523 = (2 : ZMod 36392024419) ^ (1461761 + 1461761 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 1461761 * (2 : ZMod 36392024419) ^ 1461761) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 7850482358 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 36392024419) ^ 5847047 = 27832074094 := by
        calc
          (2 : ZMod 36392024419) ^ 5847047 = (2 : ZMod 36392024419) ^ (2923523 + 2923523 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 2923523 * (2 : ZMod 36392024419) ^ 2923523) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 27832074094 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 36392024419) ^ 11694095 = 4484136163 := by
        calc
          (2 : ZMod 36392024419) ^ 11694095 = (2 : ZMod 36392024419) ^ (5847047 + 5847047 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 5847047 * (2 : ZMod 36392024419) ^ 5847047) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 4484136163 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 36392024419) ^ 23388190 = 2081944830 := by
        calc
          (2 : ZMod 36392024419) ^ 23388190 = (2 : ZMod 36392024419) ^ (11694095 + 11694095) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 11694095 * (2 : ZMod 36392024419) ^ 11694095 := by rw [pow_add]
          _ = 2081944830 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 36392024419) ^ 46776381 = 15207676620 := by
        calc
          (2 : ZMod 36392024419) ^ 46776381 = (2 : ZMod 36392024419) ^ (23388190 + 23388190 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 23388190 * (2 : ZMod 36392024419) ^ 23388190) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 15207676620 := by rw [factor_3_24]; decide
      have factor_3_26 : (2 : ZMod 36392024419) ^ 93552762 = 2027808422 := by
        calc
          (2 : ZMod 36392024419) ^ 93552762 = (2 : ZMod 36392024419) ^ (46776381 + 46776381) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 46776381 * (2 : ZMod 36392024419) ^ 46776381 := by rw [pow_add]
          _ = 2027808422 := by rw [factor_3_25]; decide
      change (2 : ZMod 36392024419) ^ 93552762 ≠ 1
      rw [factor_3_26]
      decide
    ·
      have factor_4_0 : (2 : ZMod 36392024419) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 36392024419) ^ 2 = 4 := by
        calc
          (2 : ZMod 36392024419) ^ 2 = (2 : ZMod 36392024419) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1 * (2 : ZMod 36392024419) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 36392024419) ^ 4 = 16 := by
        calc
          (2 : ZMod 36392024419) ^ 4 = (2 : ZMod 36392024419) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2 * (2 : ZMod 36392024419) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 36392024419) ^ 8 = 256 := by
        calc
          (2 : ZMod 36392024419) ^ 8 = (2 : ZMod 36392024419) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 4 * (2 : ZMod 36392024419) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 36392024419) ^ 16 = 65536 := by
        calc
          (2 : ZMod 36392024419) ^ 16 = (2 : ZMod 36392024419) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 8 * (2 : ZMod 36392024419) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 36392024419) ^ 33 = 8589934592 := by
        calc
          (2 : ZMod 36392024419) ^ 33 = (2 : ZMod 36392024419) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 16 * (2 : ZMod 36392024419) ^ 16) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 8589934592 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 36392024419) ^ 66 = 19795229654 := by
        calc
          (2 : ZMod 36392024419) ^ 66 = (2 : ZMod 36392024419) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 33 * (2 : ZMod 36392024419) ^ 33 := by rw [pow_add]
          _ = 19795229654 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 36392024419) ^ 132 = 18526415594 := by
        calc
          (2 : ZMod 36392024419) ^ 132 = (2 : ZMod 36392024419) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 66 * (2 : ZMod 36392024419) ^ 66 := by rw [pow_add]
          _ = 18526415594 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 36392024419) ^ 265 = 25217112798 := by
        calc
          (2 : ZMod 36392024419) ^ 265 = (2 : ZMod 36392024419) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 132 * (2 : ZMod 36392024419) ^ 132) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 25217112798 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 36392024419) ^ 531 = 31193834673 := by
        calc
          (2 : ZMod 36392024419) ^ 531 = (2 : ZMod 36392024419) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 265 * (2 : ZMod 36392024419) ^ 265) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 31193834673 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 36392024419) ^ 1062 = 27493966702 := by
        calc
          (2 : ZMod 36392024419) ^ 1062 = (2 : ZMod 36392024419) ^ (531 + 531) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 531 * (2 : ZMod 36392024419) ^ 531 := by rw [pow_add]
          _ = 27493966702 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 36392024419) ^ 2124 = 910229056 := by
        calc
          (2 : ZMod 36392024419) ^ 2124 = (2 : ZMod 36392024419) ^ (1062 + 1062) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 1062 * (2 : ZMod 36392024419) ^ 1062 := by rw [pow_add]
          _ = 910229056 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 36392024419) ^ 4248 = 21188903938 := by
        calc
          (2 : ZMod 36392024419) ^ 4248 = (2 : ZMod 36392024419) ^ (2124 + 2124) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 2124 * (2 : ZMod 36392024419) ^ 2124 := by rw [pow_add]
          _ = 21188903938 := by rw [factor_4_11]; decide
      have factor_4_13 : (2 : ZMod 36392024419) ^ 8497 = 22003263060 := by
        calc
          (2 : ZMod 36392024419) ^ 8497 = (2 : ZMod 36392024419) ^ (4248 + 4248 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 4248 * (2 : ZMod 36392024419) ^ 4248) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 22003263060 := by rw [factor_4_12]; decide
      have factor_4_14 : (2 : ZMod 36392024419) ^ 16994 = 26114548042 := by
        calc
          (2 : ZMod 36392024419) ^ 16994 = (2 : ZMod 36392024419) ^ (8497 + 8497) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 8497 * (2 : ZMod 36392024419) ^ 8497 := by rw [pow_add]
          _ = 26114548042 := by rw [factor_4_13]; decide
      have factor_4_15 : (2 : ZMod 36392024419) ^ 33988 = 4922109417 := by
        calc
          (2 : ZMod 36392024419) ^ 33988 = (2 : ZMod 36392024419) ^ (16994 + 16994) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 16994 * (2 : ZMod 36392024419) ^ 16994 := by rw [pow_add]
          _ = 4922109417 := by rw [factor_4_14]; decide
      have factor_4_16 : (2 : ZMod 36392024419) ^ 67977 = 23710384770 := by
        calc
          (2 : ZMod 36392024419) ^ 67977 = (2 : ZMod 36392024419) ^ (33988 + 33988 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 33988 * (2 : ZMod 36392024419) ^ 33988) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 23710384770 := by rw [factor_4_15]; decide
      have factor_4_17 : (2 : ZMod 36392024419) ^ 135955 = 3442557870 := by
        calc
          (2 : ZMod 36392024419) ^ 135955 = (2 : ZMod 36392024419) ^ (67977 + 67977 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 67977 * (2 : ZMod 36392024419) ^ 67977) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 3442557870 := by rw [factor_4_16]; decide
      have factor_4_18 : (2 : ZMod 36392024419) ^ 271911 = 14712705600 := by
        calc
          (2 : ZMod 36392024419) ^ 271911 = (2 : ZMod 36392024419) ^ (135955 + 135955 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = ((2 : ZMod 36392024419) ^ 135955 * (2 : ZMod 36392024419) ^ 135955) * (2 : ZMod 36392024419) := by rw [pow_succ, pow_add]
          _ = 14712705600 := by rw [factor_4_17]; decide
      have factor_4_19 : (2 : ZMod 36392024419) ^ 543822 = 5396389238 := by
        calc
          (2 : ZMod 36392024419) ^ 543822 = (2 : ZMod 36392024419) ^ (271911 + 271911) :=
            congrArg (fun n : ℕ => (2 : ZMod 36392024419) ^ n) (by norm_num)
          _ = (2 : ZMod 36392024419) ^ 271911 * (2 : ZMod 36392024419) ^ 271911 := by rw [pow_add]
          _ = 5396389238 := by rw [factor_4_18]; decide
      change (2 : ZMod 36392024419) ^ 543822 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_36392024419

end TotientTailPeriodKiller
end Erdos249257
