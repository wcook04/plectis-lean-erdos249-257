import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_255550753 : Nat.Prime 255550753 := by
  apply lucas_primality 255550753 (7 : ZMod 255550753)
  ·
      have fermat_0 : (7 : ZMod 255550753) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 255550753) ^ 3 = 343 := by
        calc
          (7 : ZMod 255550753) ^ 3 = (7 : ZMod 255550753) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1 * (7 : ZMod 255550753) ^ 1) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 255550753) ^ 7 = 823543 := by
        calc
          (7 : ZMod 255550753) ^ 7 = (7 : ZMod 255550753) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 3 * (7 : ZMod 255550753) ^ 3) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 255550753) ^ 15 = 195171462 := by
        calc
          (7 : ZMod 255550753) ^ 15 = (7 : ZMod 255550753) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 7 * (7 : ZMod 255550753) ^ 7) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 195171462 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 255550753) ^ 30 = 105498264 := by
        calc
          (7 : ZMod 255550753) ^ 30 = (7 : ZMod 255550753) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 15 * (7 : ZMod 255550753) ^ 15 := by rw [pow_add]
          _ = 105498264 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 255550753) ^ 60 = 81603335 := by
        calc
          (7 : ZMod 255550753) ^ 60 = (7 : ZMod 255550753) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 30 * (7 : ZMod 255550753) ^ 30 := by rw [pow_add]
          _ = 81603335 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 255550753) ^ 121 = 247456388 := by
        calc
          (7 : ZMod 255550753) ^ 121 = (7 : ZMod 255550753) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 60 * (7 : ZMod 255550753) ^ 60) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 247456388 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 255550753) ^ 243 = 154530794 := by
        calc
          (7 : ZMod 255550753) ^ 243 = (7 : ZMod 255550753) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 121 * (7 : ZMod 255550753) ^ 121) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 154530794 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 255550753) ^ 487 = 193983838 := by
        calc
          (7 : ZMod 255550753) ^ 487 = (7 : ZMod 255550753) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 243 * (7 : ZMod 255550753) ^ 243) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 193983838 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 255550753) ^ 974 = 112611142 := by
        calc
          (7 : ZMod 255550753) ^ 974 = (7 : ZMod 255550753) ^ (487 + 487) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 487 * (7 : ZMod 255550753) ^ 487 := by rw [pow_add]
          _ = 112611142 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 255550753) ^ 1949 = 214744546 := by
        calc
          (7 : ZMod 255550753) ^ 1949 = (7 : ZMod 255550753) ^ (974 + 974 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 974 * (7 : ZMod 255550753) ^ 974) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 214744546 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 255550753) ^ 3899 = 137109767 := by
        calc
          (7 : ZMod 255550753) ^ 3899 = (7 : ZMod 255550753) ^ (1949 + 1949 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1949 * (7 : ZMod 255550753) ^ 1949) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 137109767 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 255550753) ^ 7798 = 241781946 := by
        calc
          (7 : ZMod 255550753) ^ 7798 = (7 : ZMod 255550753) ^ (3899 + 3899) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 3899 * (7 : ZMod 255550753) ^ 3899 := by rw [pow_add]
          _ = 241781946 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 255550753) ^ 15597 = 85037417 := by
        calc
          (7 : ZMod 255550753) ^ 15597 = (7 : ZMod 255550753) ^ (7798 + 7798 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 7798 * (7 : ZMod 255550753) ^ 7798) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 85037417 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 255550753) ^ 31195 = 199007472 := by
        calc
          (7 : ZMod 255550753) ^ 31195 = (7 : ZMod 255550753) ^ (15597 + 15597 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 15597 * (7 : ZMod 255550753) ^ 15597) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 199007472 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 255550753) ^ 62390 = 54467832 := by
        calc
          (7 : ZMod 255550753) ^ 62390 = (7 : ZMod 255550753) ^ (31195 + 31195) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 31195 * (7 : ZMod 255550753) ^ 31195 := by rw [pow_add]
          _ = 54467832 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 255550753) ^ 124780 = 65588317 := by
        calc
          (7 : ZMod 255550753) ^ 124780 = (7 : ZMod 255550753) ^ (62390 + 62390) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 62390 * (7 : ZMod 255550753) ^ 62390 := by rw [pow_add]
          _ = 65588317 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 255550753) ^ 249561 = 252336548 := by
        calc
          (7 : ZMod 255550753) ^ 249561 = (7 : ZMod 255550753) ^ (124780 + 124780 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 124780 * (7 : ZMod 255550753) ^ 124780) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 252336548 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 255550753) ^ 499122 = 219041247 := by
        calc
          (7 : ZMod 255550753) ^ 499122 = (7 : ZMod 255550753) ^ (249561 + 249561) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 249561 * (7 : ZMod 255550753) ^ 249561 := by rw [pow_add]
          _ = 219041247 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 255550753) ^ 998245 = 181642219 := by
        calc
          (7 : ZMod 255550753) ^ 998245 = (7 : ZMod 255550753) ^ (499122 + 499122 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 499122 * (7 : ZMod 255550753) ^ 499122) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 181642219 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 255550753) ^ 1996490 = 198486539 := by
        calc
          (7 : ZMod 255550753) ^ 1996490 = (7 : ZMod 255550753) ^ (998245 + 998245) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 998245 * (7 : ZMod 255550753) ^ 998245 := by rw [pow_add]
          _ = 198486539 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 255550753) ^ 3992980 = 226527162 := by
        calc
          (7 : ZMod 255550753) ^ 3992980 = (7 : ZMod 255550753) ^ (1996490 + 1996490) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 1996490 * (7 : ZMod 255550753) ^ 1996490 := by rw [pow_add]
          _ = 226527162 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 255550753) ^ 7985961 = 189314425 := by
        calc
          (7 : ZMod 255550753) ^ 7985961 = (7 : ZMod 255550753) ^ (3992980 + 3992980 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 3992980 * (7 : ZMod 255550753) ^ 3992980) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 189314425 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 255550753) ^ 15971922 = 29699853 := by
        calc
          (7 : ZMod 255550753) ^ 15971922 = (7 : ZMod 255550753) ^ (7985961 + 7985961) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 7985961 * (7 : ZMod 255550753) ^ 7985961 := by rw [pow_add]
          _ = 29699853 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 255550753) ^ 31943844 = 56251298 := by
        calc
          (7 : ZMod 255550753) ^ 31943844 = (7 : ZMod 255550753) ^ (15971922 + 15971922) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 15971922 * (7 : ZMod 255550753) ^ 15971922 := by rw [pow_add]
          _ = 56251298 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 255550753) ^ 63887688 = 58200550 := by
        calc
          (7 : ZMod 255550753) ^ 63887688 = (7 : ZMod 255550753) ^ (31943844 + 31943844) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 31943844 * (7 : ZMod 255550753) ^ 31943844 := by rw [pow_add]
          _ = 58200550 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 255550753) ^ 127775376 = 255550752 := by
        calc
          (7 : ZMod 255550753) ^ 127775376 = (7 : ZMod 255550753) ^ (63887688 + 63887688) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 63887688 * (7 : ZMod 255550753) ^ 63887688 := by rw [pow_add]
          _ = 255550752 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 255550753) ^ 255550752 = 1 := by
        calc
          (7 : ZMod 255550753) ^ 255550752 = (7 : ZMod 255550753) ^ (127775376 + 127775376) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 127775376 * (7 : ZMod 255550753) ^ 127775376 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (443, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (443, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod = 255550753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 255550753) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 255550753) ^ 3 = 343 := by
        calc
          (7 : ZMod 255550753) ^ 3 = (7 : ZMod 255550753) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1 * (7 : ZMod 255550753) ^ 1) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 255550753) ^ 7 = 823543 := by
        calc
          (7 : ZMod 255550753) ^ 7 = (7 : ZMod 255550753) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 3 * (7 : ZMod 255550753) ^ 3) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 255550753) ^ 15 = 195171462 := by
        calc
          (7 : ZMod 255550753) ^ 15 = (7 : ZMod 255550753) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 7 * (7 : ZMod 255550753) ^ 7) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 195171462 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 255550753) ^ 30 = 105498264 := by
        calc
          (7 : ZMod 255550753) ^ 30 = (7 : ZMod 255550753) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 15 * (7 : ZMod 255550753) ^ 15 := by rw [pow_add]
          _ = 105498264 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 255550753) ^ 60 = 81603335 := by
        calc
          (7 : ZMod 255550753) ^ 60 = (7 : ZMod 255550753) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 30 * (7 : ZMod 255550753) ^ 30 := by rw [pow_add]
          _ = 81603335 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 255550753) ^ 121 = 247456388 := by
        calc
          (7 : ZMod 255550753) ^ 121 = (7 : ZMod 255550753) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 60 * (7 : ZMod 255550753) ^ 60) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 247456388 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 255550753) ^ 243 = 154530794 := by
        calc
          (7 : ZMod 255550753) ^ 243 = (7 : ZMod 255550753) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 121 * (7 : ZMod 255550753) ^ 121) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 154530794 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 255550753) ^ 487 = 193983838 := by
        calc
          (7 : ZMod 255550753) ^ 487 = (7 : ZMod 255550753) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 243 * (7 : ZMod 255550753) ^ 243) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 193983838 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 255550753) ^ 974 = 112611142 := by
        calc
          (7 : ZMod 255550753) ^ 974 = (7 : ZMod 255550753) ^ (487 + 487) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 487 * (7 : ZMod 255550753) ^ 487 := by rw [pow_add]
          _ = 112611142 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 255550753) ^ 1949 = 214744546 := by
        calc
          (7 : ZMod 255550753) ^ 1949 = (7 : ZMod 255550753) ^ (974 + 974 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 974 * (7 : ZMod 255550753) ^ 974) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 214744546 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 255550753) ^ 3899 = 137109767 := by
        calc
          (7 : ZMod 255550753) ^ 3899 = (7 : ZMod 255550753) ^ (1949 + 1949 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1949 * (7 : ZMod 255550753) ^ 1949) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 137109767 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 255550753) ^ 7798 = 241781946 := by
        calc
          (7 : ZMod 255550753) ^ 7798 = (7 : ZMod 255550753) ^ (3899 + 3899) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 3899 * (7 : ZMod 255550753) ^ 3899 := by rw [pow_add]
          _ = 241781946 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 255550753) ^ 15597 = 85037417 := by
        calc
          (7 : ZMod 255550753) ^ 15597 = (7 : ZMod 255550753) ^ (7798 + 7798 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 7798 * (7 : ZMod 255550753) ^ 7798) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 85037417 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 255550753) ^ 31195 = 199007472 := by
        calc
          (7 : ZMod 255550753) ^ 31195 = (7 : ZMod 255550753) ^ (15597 + 15597 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 15597 * (7 : ZMod 255550753) ^ 15597) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 199007472 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 255550753) ^ 62390 = 54467832 := by
        calc
          (7 : ZMod 255550753) ^ 62390 = (7 : ZMod 255550753) ^ (31195 + 31195) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 31195 * (7 : ZMod 255550753) ^ 31195 := by rw [pow_add]
          _ = 54467832 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 255550753) ^ 124780 = 65588317 := by
        calc
          (7 : ZMod 255550753) ^ 124780 = (7 : ZMod 255550753) ^ (62390 + 62390) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 62390 * (7 : ZMod 255550753) ^ 62390 := by rw [pow_add]
          _ = 65588317 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 255550753) ^ 249561 = 252336548 := by
        calc
          (7 : ZMod 255550753) ^ 249561 = (7 : ZMod 255550753) ^ (124780 + 124780 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 124780 * (7 : ZMod 255550753) ^ 124780) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 252336548 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 255550753) ^ 499122 = 219041247 := by
        calc
          (7 : ZMod 255550753) ^ 499122 = (7 : ZMod 255550753) ^ (249561 + 249561) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 249561 * (7 : ZMod 255550753) ^ 249561 := by rw [pow_add]
          _ = 219041247 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 255550753) ^ 998245 = 181642219 := by
        calc
          (7 : ZMod 255550753) ^ 998245 = (7 : ZMod 255550753) ^ (499122 + 499122 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 499122 * (7 : ZMod 255550753) ^ 499122) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 181642219 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 255550753) ^ 1996490 = 198486539 := by
        calc
          (7 : ZMod 255550753) ^ 1996490 = (7 : ZMod 255550753) ^ (998245 + 998245) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 998245 * (7 : ZMod 255550753) ^ 998245 := by rw [pow_add]
          _ = 198486539 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 255550753) ^ 3992980 = 226527162 := by
        calc
          (7 : ZMod 255550753) ^ 3992980 = (7 : ZMod 255550753) ^ (1996490 + 1996490) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 1996490 * (7 : ZMod 255550753) ^ 1996490 := by rw [pow_add]
          _ = 226527162 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 255550753) ^ 7985961 = 189314425 := by
        calc
          (7 : ZMod 255550753) ^ 7985961 = (7 : ZMod 255550753) ^ (3992980 + 3992980 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 3992980 * (7 : ZMod 255550753) ^ 3992980) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 189314425 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 255550753) ^ 15971922 = 29699853 := by
        calc
          (7 : ZMod 255550753) ^ 15971922 = (7 : ZMod 255550753) ^ (7985961 + 7985961) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 7985961 * (7 : ZMod 255550753) ^ 7985961 := by rw [pow_add]
          _ = 29699853 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 255550753) ^ 31943844 = 56251298 := by
        calc
          (7 : ZMod 255550753) ^ 31943844 = (7 : ZMod 255550753) ^ (15971922 + 15971922) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 15971922 * (7 : ZMod 255550753) ^ 15971922 := by rw [pow_add]
          _ = 56251298 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 255550753) ^ 63887688 = 58200550 := by
        calc
          (7 : ZMod 255550753) ^ 63887688 = (7 : ZMod 255550753) ^ (31943844 + 31943844) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 31943844 * (7 : ZMod 255550753) ^ 31943844 := by rw [pow_add]
          _ = 58200550 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 255550753) ^ 127775376 = 255550752 := by
        calc
          (7 : ZMod 255550753) ^ 127775376 = (7 : ZMod 255550753) ^ (63887688 + 63887688) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 63887688 * (7 : ZMod 255550753) ^ 63887688 := by rw [pow_add]
          _ = 255550752 := by rw [factor_0_25]; decide
      change (7 : ZMod 255550753) ^ 127775376 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (7 : ZMod 255550753) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 255550753) ^ 2 = 49 := by
        calc
          (7 : ZMod 255550753) ^ 2 = (7 : ZMod 255550753) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 1 * (7 : ZMod 255550753) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 255550753) ^ 5 = 16807 := by
        calc
          (7 : ZMod 255550753) ^ 5 = (7 : ZMod 255550753) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 2 * (7 : ZMod 255550753) ^ 2) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 255550753) ^ 10 = 26924496 := by
        calc
          (7 : ZMod 255550753) ^ 10 = (7 : ZMod 255550753) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 5 * (7 : ZMod 255550753) ^ 5 := by rw [pow_add]
          _ = 26924496 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 255550753) ^ 20 = 252847079 := by
        calc
          (7 : ZMod 255550753) ^ 20 = (7 : ZMod 255550753) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 10 * (7 : ZMod 255550753) ^ 10 := by rw [pow_add]
          _ = 252847079 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 255550753) ^ 40 = 79359464 := by
        calc
          (7 : ZMod 255550753) ^ 40 = (7 : ZMod 255550753) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 20 * (7 : ZMod 255550753) ^ 20 := by rw [pow_add]
          _ = 79359464 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 255550753) ^ 81 = 103379495 := by
        calc
          (7 : ZMod 255550753) ^ 81 = (7 : ZMod 255550753) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 40 * (7 : ZMod 255550753) ^ 40) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 103379495 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 255550753) ^ 162 = 177293076 := by
        calc
          (7 : ZMod 255550753) ^ 162 = (7 : ZMod 255550753) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 81 * (7 : ZMod 255550753) ^ 81 := by rw [pow_add]
          _ = 177293076 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 255550753) ^ 324 = 180270696 := by
        calc
          (7 : ZMod 255550753) ^ 324 = (7 : ZMod 255550753) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 162 * (7 : ZMod 255550753) ^ 162 := by rw [pow_add]
          _ = 180270696 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 255550753) ^ 649 = 127351530 := by
        calc
          (7 : ZMod 255550753) ^ 649 = (7 : ZMod 255550753) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 324 * (7 : ZMod 255550753) ^ 324) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 127351530 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 255550753) ^ 1299 = 19621111 := by
        calc
          (7 : ZMod 255550753) ^ 1299 = (7 : ZMod 255550753) ^ (649 + 649 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 649 * (7 : ZMod 255550753) ^ 649) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 19621111 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 255550753) ^ 2599 = 145792934 := by
        calc
          (7 : ZMod 255550753) ^ 2599 = (7 : ZMod 255550753) ^ (1299 + 1299 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1299 * (7 : ZMod 255550753) ^ 1299) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 145792934 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 255550753) ^ 5199 = 161818269 := by
        calc
          (7 : ZMod 255550753) ^ 5199 = (7 : ZMod 255550753) ^ (2599 + 2599 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 2599 * (7 : ZMod 255550753) ^ 2599) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 161818269 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 255550753) ^ 10398 = 145386669 := by
        calc
          (7 : ZMod 255550753) ^ 10398 = (7 : ZMod 255550753) ^ (5199 + 5199) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 5199 * (7 : ZMod 255550753) ^ 5199 := by rw [pow_add]
          _ = 145386669 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 255550753) ^ 20796 = 210630322 := by
        calc
          (7 : ZMod 255550753) ^ 20796 = (7 : ZMod 255550753) ^ (10398 + 10398) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 10398 * (7 : ZMod 255550753) ^ 10398 := by rw [pow_add]
          _ = 210630322 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 255550753) ^ 41593 = 142026983 := by
        calc
          (7 : ZMod 255550753) ^ 41593 = (7 : ZMod 255550753) ^ (20796 + 20796 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 20796 * (7 : ZMod 255550753) ^ 20796) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 142026983 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 255550753) ^ 83187 = 186634319 := by
        calc
          (7 : ZMod 255550753) ^ 83187 = (7 : ZMod 255550753) ^ (41593 + 41593 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 41593 * (7 : ZMod 255550753) ^ 41593) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 186634319 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 255550753) ^ 166374 = 243083106 := by
        calc
          (7 : ZMod 255550753) ^ 166374 = (7 : ZMod 255550753) ^ (83187 + 83187) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 83187 * (7 : ZMod 255550753) ^ 83187 := by rw [pow_add]
          _ = 243083106 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 255550753) ^ 332748 = 154044570 := by
        calc
          (7 : ZMod 255550753) ^ 332748 = (7 : ZMod 255550753) ^ (166374 + 166374) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 166374 * (7 : ZMod 255550753) ^ 166374 := by rw [pow_add]
          _ = 154044570 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 255550753) ^ 665496 = 120607276 := by
        calc
          (7 : ZMod 255550753) ^ 665496 = (7 : ZMod 255550753) ^ (332748 + 332748) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 332748 * (7 : ZMod 255550753) ^ 332748 := by rw [pow_add]
          _ = 120607276 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 255550753) ^ 1330993 = 132184329 := by
        calc
          (7 : ZMod 255550753) ^ 1330993 = (7 : ZMod 255550753) ^ (665496 + 665496 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 665496 * (7 : ZMod 255550753) ^ 665496) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 132184329 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 255550753) ^ 2661987 = 11671584 := by
        calc
          (7 : ZMod 255550753) ^ 2661987 = (7 : ZMod 255550753) ^ (1330993 + 1330993 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1330993 * (7 : ZMod 255550753) ^ 1330993) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 11671584 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 255550753) ^ 5323974 = 199819605 := by
        calc
          (7 : ZMod 255550753) ^ 5323974 = (7 : ZMod 255550753) ^ (2661987 + 2661987) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 2661987 * (7 : ZMod 255550753) ^ 2661987 := by rw [pow_add]
          _ = 199819605 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 255550753) ^ 10647948 = 72044940 := by
        calc
          (7 : ZMod 255550753) ^ 10647948 = (7 : ZMod 255550753) ^ (5323974 + 5323974) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 5323974 * (7 : ZMod 255550753) ^ 5323974 := by rw [pow_add]
          _ = 72044940 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 255550753) ^ 21295896 = 179524063 := by
        calc
          (7 : ZMod 255550753) ^ 21295896 = (7 : ZMod 255550753) ^ (10647948 + 10647948) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 10647948 * (7 : ZMod 255550753) ^ 10647948 := by rw [pow_add]
          _ = 179524063 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 255550753) ^ 42591792 = 183421227 := by
        calc
          (7 : ZMod 255550753) ^ 42591792 = (7 : ZMod 255550753) ^ (21295896 + 21295896) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 21295896 * (7 : ZMod 255550753) ^ 21295896 := by rw [pow_add]
          _ = 183421227 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 255550753) ^ 85183584 = 183421226 := by
        calc
          (7 : ZMod 255550753) ^ 85183584 = (7 : ZMod 255550753) ^ (42591792 + 42591792) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 42591792 * (7 : ZMod 255550753) ^ 42591792 := by rw [pow_add]
          _ = 183421226 := by rw [factor_1_25]; decide
      change (7 : ZMod 255550753) ^ 85183584 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (7 : ZMod 255550753) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 255550753) ^ 2 = 49 := by
        calc
          (7 : ZMod 255550753) ^ 2 = (7 : ZMod 255550753) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 1 * (7 : ZMod 255550753) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 255550753) ^ 4 = 2401 := by
        calc
          (7 : ZMod 255550753) ^ 4 = (7 : ZMod 255550753) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 2 * (7 : ZMod 255550753) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 255550753) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 255550753) ^ 8 = (7 : ZMod 255550753) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 4 * (7 : ZMod 255550753) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 255550753) ^ 17 = 108023777 := by
        calc
          (7 : ZMod 255550753) ^ 17 = (7 : ZMod 255550753) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 8 * (7 : ZMod 255550753) ^ 8) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 108023777 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 255550753) ^ 35 = 98198734 := by
        calc
          (7 : ZMod 255550753) ^ 35 = (7 : ZMod 255550753) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 17 * (7 : ZMod 255550753) ^ 17) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 98198734 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 255550753) ^ 70 = 146235547 := by
        calc
          (7 : ZMod 255550753) ^ 70 = (7 : ZMod 255550753) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 35 * (7 : ZMod 255550753) ^ 35 := by rw [pow_add]
          _ = 146235547 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 255550753) ^ 140 = 135223623 := by
        calc
          (7 : ZMod 255550753) ^ 140 = (7 : ZMod 255550753) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 70 * (7 : ZMod 255550753) ^ 70 := by rw [pow_add]
          _ = 135223623 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 255550753) ^ 281 = 26652977 := by
        calc
          (7 : ZMod 255550753) ^ 281 = (7 : ZMod 255550753) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 140 * (7 : ZMod 255550753) ^ 140) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 26652977 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 255550753) ^ 563 = 220787807 := by
        calc
          (7 : ZMod 255550753) ^ 563 = (7 : ZMod 255550753) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 281 * (7 : ZMod 255550753) ^ 281) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 220787807 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 255550753) ^ 1126 = 214071854 := by
        calc
          (7 : ZMod 255550753) ^ 1126 = (7 : ZMod 255550753) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 563 * (7 : ZMod 255550753) ^ 563 := by rw [pow_add]
          _ = 214071854 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 255550753) ^ 2253 = 24233360 := by
        calc
          (7 : ZMod 255550753) ^ 2253 = (7 : ZMod 255550753) ^ (1126 + 1126 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1126 * (7 : ZMod 255550753) ^ 1126) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 24233360 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 255550753) ^ 4506 = 106495600 := by
        calc
          (7 : ZMod 255550753) ^ 4506 = (7 : ZMod 255550753) ^ (2253 + 2253) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 2253 * (7 : ZMod 255550753) ^ 2253 := by rw [pow_add]
          _ = 106495600 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 255550753) ^ 9013 = 60200683 := by
        calc
          (7 : ZMod 255550753) ^ 9013 = (7 : ZMod 255550753) ^ (4506 + 4506 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 4506 * (7 : ZMod 255550753) ^ 4506) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 60200683 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 255550753) ^ 18027 = 169376523 := by
        calc
          (7 : ZMod 255550753) ^ 18027 = (7 : ZMod 255550753) ^ (9013 + 9013 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 9013 * (7 : ZMod 255550753) ^ 9013) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 169376523 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 255550753) ^ 36054 = 205918006 := by
        calc
          (7 : ZMod 255550753) ^ 36054 = (7 : ZMod 255550753) ^ (18027 + 18027) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 18027 * (7 : ZMod 255550753) ^ 18027 := by rw [pow_add]
          _ = 205918006 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 255550753) ^ 72108 = 236190432 := by
        calc
          (7 : ZMod 255550753) ^ 72108 = (7 : ZMod 255550753) ^ (36054 + 36054) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 36054 * (7 : ZMod 255550753) ^ 36054 := by rw [pow_add]
          _ = 236190432 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 255550753) ^ 144216 = 117681375 := by
        calc
          (7 : ZMod 255550753) ^ 144216 = (7 : ZMod 255550753) ^ (72108 + 72108) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 72108 * (7 : ZMod 255550753) ^ 72108 := by rw [pow_add]
          _ = 117681375 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 255550753) ^ 288432 = 206071708 := by
        calc
          (7 : ZMod 255550753) ^ 288432 = (7 : ZMod 255550753) ^ (144216 + 144216) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 144216 * (7 : ZMod 255550753) ^ 144216 := by rw [pow_add]
          _ = 206071708 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 255550753) ^ 576864 = 191473531 := by
        calc
          (7 : ZMod 255550753) ^ 576864 = (7 : ZMod 255550753) ^ (288432 + 288432) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 288432 * (7 : ZMod 255550753) ^ 288432 := by rw [pow_add]
          _ = 191473531 := by rw [factor_2_18]; decide
      change (7 : ZMod 255550753) ^ 576864 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (7 : ZMod 255550753) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 255550753) ^ 3 = 343 := by
        calc
          (7 : ZMod 255550753) ^ 3 = (7 : ZMod 255550753) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1 * (7 : ZMod 255550753) ^ 1) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 255550753) ^ 7 = 823543 := by
        calc
          (7 : ZMod 255550753) ^ 7 = (7 : ZMod 255550753) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 3 * (7 : ZMod 255550753) ^ 3) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 255550753) ^ 15 = 195171462 := by
        calc
          (7 : ZMod 255550753) ^ 15 = (7 : ZMod 255550753) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 7 * (7 : ZMod 255550753) ^ 7) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 195171462 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 255550753) ^ 31 = 227386342 := by
        calc
          (7 : ZMod 255550753) ^ 31 = (7 : ZMod 255550753) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 15 * (7 : ZMod 255550753) ^ 15) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 227386342 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 255550753) ^ 62 = 165302120 := by
        calc
          (7 : ZMod 255550753) ^ 62 = (7 : ZMod 255550753) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 31 * (7 : ZMod 255550753) ^ 31 := by rw [pow_add]
          _ = 165302120 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 255550753) ^ 124 = 34691088 := by
        calc
          (7 : ZMod 255550753) ^ 124 = (7 : ZMod 255550753) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 62 * (7 : ZMod 255550753) ^ 62 := by rw [pow_add]
          _ = 34691088 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 255550753) ^ 249 = 1713380 := by
        calc
          (7 : ZMod 255550753) ^ 249 = (7 : ZMod 255550753) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 124 * (7 : ZMod 255550753) ^ 124) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 1713380 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 255550753) ^ 498 = 159524689 := by
        calc
          (7 : ZMod 255550753) ^ 498 = (7 : ZMod 255550753) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 249 * (7 : ZMod 255550753) ^ 249 := by rw [pow_add]
          _ = 159524689 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 255550753) ^ 996 = 112880233 := by
        calc
          (7 : ZMod 255550753) ^ 996 = (7 : ZMod 255550753) ^ (498 + 498) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 498 * (7 : ZMod 255550753) ^ 498 := by rw [pow_add]
          _ = 112880233 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 255550753) ^ 1993 = 105184452 := by
        calc
          (7 : ZMod 255550753) ^ 1993 = (7 : ZMod 255550753) ^ (996 + 996 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 996 * (7 : ZMod 255550753) ^ 996) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 105184452 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 255550753) ^ 3987 = 144694107 := by
        calc
          (7 : ZMod 255550753) ^ 3987 = (7 : ZMod 255550753) ^ (1993 + 1993 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = ((7 : ZMod 255550753) ^ 1993 * (7 : ZMod 255550753) ^ 1993) * (7 : ZMod 255550753) := by rw [pow_succ, pow_add]
          _ = 144694107 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 255550753) ^ 7974 = 212756383 := by
        calc
          (7 : ZMod 255550753) ^ 7974 = (7 : ZMod 255550753) ^ (3987 + 3987) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 3987 * (7 : ZMod 255550753) ^ 3987 := by rw [pow_add]
          _ = 212756383 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 255550753) ^ 15948 = 142559446 := by
        calc
          (7 : ZMod 255550753) ^ 15948 = (7 : ZMod 255550753) ^ (7974 + 7974) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 7974 * (7 : ZMod 255550753) ^ 7974 := by rw [pow_add]
          _ = 142559446 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 255550753) ^ 31896 = 176864290 := by
        calc
          (7 : ZMod 255550753) ^ 31896 = (7 : ZMod 255550753) ^ (15948 + 15948) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 15948 * (7 : ZMod 255550753) ^ 15948 := by rw [pow_add]
          _ = 176864290 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 255550753) ^ 63792 = 172743481 := by
        calc
          (7 : ZMod 255550753) ^ 63792 = (7 : ZMod 255550753) ^ (31896 + 31896) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 31896 * (7 : ZMod 255550753) ^ 31896 := by rw [pow_add]
          _ = 172743481 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 255550753) ^ 127584 = 182472736 := by
        calc
          (7 : ZMod 255550753) ^ 127584 = (7 : ZMod 255550753) ^ (63792 + 63792) :=
            congrArg (fun n : ℕ => (7 : ZMod 255550753) ^ n) (by norm_num)
          _ = (7 : ZMod 255550753) ^ 63792 * (7 : ZMod 255550753) ^ 63792 := by rw [pow_add]
          _ = 182472736 := by rw [factor_3_15]; decide
      change (7 : ZMod 255550753) ^ 127584 ≠ 1
      rw [factor_3_16]
      decide

#print axioms prime_lucas_255550753

end TotientTailPeriodKiller
end Erdos249257
