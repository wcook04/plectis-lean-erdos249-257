import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_60753047 : Nat.Prime 60753047 := by
  apply lucas_primality 60753047 (5 : ZMod 60753047)
  ·
      have fermat_0 : (5 : ZMod 60753047) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 60753047) ^ 3 = 125 := by
        calc
          (5 : ZMod 60753047) ^ 3 = (5 : ZMod 60753047) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 1 * (5 : ZMod 60753047) ^ 1) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 60753047) ^ 7 = 78125 := by
        calc
          (5 : ZMod 60753047) ^ 7 = (5 : ZMod 60753047) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 3 * (5 : ZMod 60753047) ^ 3) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 60753047) ^ 14 = 28210925 := by
        calc
          (5 : ZMod 60753047) ^ 14 = (5 : ZMod 60753047) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 7 * (5 : ZMod 60753047) ^ 7 := by rw [pow_add]
          _ = 28210925 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 60753047) ^ 28 = 588299 := by
        calc
          (5 : ZMod 60753047) ^ 28 = (5 : ZMod 60753047) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 14 * (5 : ZMod 60753047) ^ 14 := by rw [pow_add]
          _ = 588299 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 60753047) ^ 57 = 49529304 := by
        calc
          (5 : ZMod 60753047) ^ 57 = (5 : ZMod 60753047) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 28 * (5 : ZMod 60753047) ^ 28) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 49529304 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 60753047) ^ 115 = 20387032 := by
        calc
          (5 : ZMod 60753047) ^ 115 = (5 : ZMod 60753047) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 57 * (5 : ZMod 60753047) ^ 57) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 20387032 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 60753047) ^ 231 = 9075779 := by
        calc
          (5 : ZMod 60753047) ^ 231 = (5 : ZMod 60753047) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 115 * (5 : ZMod 60753047) ^ 115) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 9075779 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 60753047) ^ 463 = 28476197 := by
        calc
          (5 : ZMod 60753047) ^ 463 = (5 : ZMod 60753047) ^ (231 + 231 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 231 * (5 : ZMod 60753047) ^ 231) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 28476197 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 60753047) ^ 927 = 49134591 := by
        calc
          (5 : ZMod 60753047) ^ 927 = (5 : ZMod 60753047) ^ (463 + 463 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 463 * (5 : ZMod 60753047) ^ 463) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 49134591 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 60753047) ^ 1854 = 48880649 := by
        calc
          (5 : ZMod 60753047) ^ 1854 = (5 : ZMod 60753047) ^ (927 + 927) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 927 * (5 : ZMod 60753047) ^ 927 := by rw [pow_add]
          _ = 48880649 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 60753047) ^ 3708 = 21642187 := by
        calc
          (5 : ZMod 60753047) ^ 3708 = (5 : ZMod 60753047) ^ (1854 + 1854) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 1854 * (5 : ZMod 60753047) ^ 1854 := by rw [pow_add]
          _ = 21642187 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 60753047) ^ 7416 = 15363795 := by
        calc
          (5 : ZMod 60753047) ^ 7416 = (5 : ZMod 60753047) ^ (3708 + 3708) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 3708 * (5 : ZMod 60753047) ^ 3708 := by rw [pow_add]
          _ = 15363795 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 60753047) ^ 14832 = 13924092 := by
        calc
          (5 : ZMod 60753047) ^ 14832 = (5 : ZMod 60753047) ^ (7416 + 7416) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 7416 * (5 : ZMod 60753047) ^ 7416 := by rw [pow_add]
          _ = 13924092 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 60753047) ^ 29664 = 50429069 := by
        calc
          (5 : ZMod 60753047) ^ 29664 = (5 : ZMod 60753047) ^ (14832 + 14832) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 14832 * (5 : ZMod 60753047) ^ 14832 := by rw [pow_add]
          _ = 50429069 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 60753047) ^ 59329 = 39596864 := by
        calc
          (5 : ZMod 60753047) ^ 59329 = (5 : ZMod 60753047) ^ (29664 + 29664 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 29664 * (5 : ZMod 60753047) ^ 29664) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 39596864 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 60753047) ^ 118658 = 39310846 := by
        calc
          (5 : ZMod 60753047) ^ 118658 = (5 : ZMod 60753047) ^ (59329 + 59329) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 59329 * (5 : ZMod 60753047) ^ 59329 := by rw [pow_add]
          _ = 39310846 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 60753047) ^ 237316 = 41836002 := by
        calc
          (5 : ZMod 60753047) ^ 237316 = (5 : ZMod 60753047) ^ (118658 + 118658) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 118658 * (5 : ZMod 60753047) ^ 118658 := by rw [pow_add]
          _ = 41836002 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 60753047) ^ 474633 = 37461100 := by
        calc
          (5 : ZMod 60753047) ^ 474633 = (5 : ZMod 60753047) ^ (237316 + 237316 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 237316 * (5 : ZMod 60753047) ^ 237316) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 37461100 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 60753047) ^ 949266 = 48840517 := by
        calc
          (5 : ZMod 60753047) ^ 949266 = (5 : ZMod 60753047) ^ (474633 + 474633) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 474633 * (5 : ZMod 60753047) ^ 474633 := by rw [pow_add]
          _ = 48840517 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 60753047) ^ 1898532 = 6498219 := by
        calc
          (5 : ZMod 60753047) ^ 1898532 = (5 : ZMod 60753047) ^ (949266 + 949266) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 949266 * (5 : ZMod 60753047) ^ 949266 := by rw [pow_add]
          _ = 6498219 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 60753047) ^ 3797065 = 37163363 := by
        calc
          (5 : ZMod 60753047) ^ 3797065 = (5 : ZMod 60753047) ^ (1898532 + 1898532 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 1898532 * (5 : ZMod 60753047) ^ 1898532) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 37163363 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 60753047) ^ 7594130 = 7189985 := by
        calc
          (5 : ZMod 60753047) ^ 7594130 = (5 : ZMod 60753047) ^ (3797065 + 3797065) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 3797065 * (5 : ZMod 60753047) ^ 3797065 := by rw [pow_add]
          _ = 7189985 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 60753047) ^ 15188261 = 54512348 := by
        calc
          (5 : ZMod 60753047) ^ 15188261 = (5 : ZMod 60753047) ^ (7594130 + 7594130 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 7594130 * (5 : ZMod 60753047) ^ 7594130) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 54512348 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 60753047) ^ 30376523 = 60753046 := by
        calc
          (5 : ZMod 60753047) ^ 30376523 = (5 : ZMod 60753047) ^ (15188261 + 15188261 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 15188261 * (5 : ZMod 60753047) ^ 15188261) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 60753046 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 60753047) ^ 60753046 = 1 := by
        calc
          (5 : ZMod 60753047) ^ 60753046 = (5 : ZMod 60753047) ^ (30376523 + 30376523) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 30376523 * (5 : ZMod 60753047) ^ 30376523 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (47, 1), (646309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (47, 1), (646309, 1)] : List FactorBlock).map factorBlockValue).prod = 60753047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 60753047) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 60753047) ^ 3 = 125 := by
        calc
          (5 : ZMod 60753047) ^ 3 = (5 : ZMod 60753047) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 1 * (5 : ZMod 60753047) ^ 1) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 60753047) ^ 7 = 78125 := by
        calc
          (5 : ZMod 60753047) ^ 7 = (5 : ZMod 60753047) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 3 * (5 : ZMod 60753047) ^ 3) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 60753047) ^ 14 = 28210925 := by
        calc
          (5 : ZMod 60753047) ^ 14 = (5 : ZMod 60753047) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 7 * (5 : ZMod 60753047) ^ 7 := by rw [pow_add]
          _ = 28210925 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 60753047) ^ 28 = 588299 := by
        calc
          (5 : ZMod 60753047) ^ 28 = (5 : ZMod 60753047) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 14 * (5 : ZMod 60753047) ^ 14 := by rw [pow_add]
          _ = 588299 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 60753047) ^ 57 = 49529304 := by
        calc
          (5 : ZMod 60753047) ^ 57 = (5 : ZMod 60753047) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 28 * (5 : ZMod 60753047) ^ 28) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 49529304 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 60753047) ^ 115 = 20387032 := by
        calc
          (5 : ZMod 60753047) ^ 115 = (5 : ZMod 60753047) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 57 * (5 : ZMod 60753047) ^ 57) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 20387032 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 60753047) ^ 231 = 9075779 := by
        calc
          (5 : ZMod 60753047) ^ 231 = (5 : ZMod 60753047) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 115 * (5 : ZMod 60753047) ^ 115) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 9075779 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 60753047) ^ 463 = 28476197 := by
        calc
          (5 : ZMod 60753047) ^ 463 = (5 : ZMod 60753047) ^ (231 + 231 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 231 * (5 : ZMod 60753047) ^ 231) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 28476197 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 60753047) ^ 927 = 49134591 := by
        calc
          (5 : ZMod 60753047) ^ 927 = (5 : ZMod 60753047) ^ (463 + 463 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 463 * (5 : ZMod 60753047) ^ 463) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 49134591 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 60753047) ^ 1854 = 48880649 := by
        calc
          (5 : ZMod 60753047) ^ 1854 = (5 : ZMod 60753047) ^ (927 + 927) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 927 * (5 : ZMod 60753047) ^ 927 := by rw [pow_add]
          _ = 48880649 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 60753047) ^ 3708 = 21642187 := by
        calc
          (5 : ZMod 60753047) ^ 3708 = (5 : ZMod 60753047) ^ (1854 + 1854) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 1854 * (5 : ZMod 60753047) ^ 1854 := by rw [pow_add]
          _ = 21642187 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 60753047) ^ 7416 = 15363795 := by
        calc
          (5 : ZMod 60753047) ^ 7416 = (5 : ZMod 60753047) ^ (3708 + 3708) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 3708 * (5 : ZMod 60753047) ^ 3708 := by rw [pow_add]
          _ = 15363795 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 60753047) ^ 14832 = 13924092 := by
        calc
          (5 : ZMod 60753047) ^ 14832 = (5 : ZMod 60753047) ^ (7416 + 7416) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 7416 * (5 : ZMod 60753047) ^ 7416 := by rw [pow_add]
          _ = 13924092 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 60753047) ^ 29664 = 50429069 := by
        calc
          (5 : ZMod 60753047) ^ 29664 = (5 : ZMod 60753047) ^ (14832 + 14832) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 14832 * (5 : ZMod 60753047) ^ 14832 := by rw [pow_add]
          _ = 50429069 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 60753047) ^ 59329 = 39596864 := by
        calc
          (5 : ZMod 60753047) ^ 59329 = (5 : ZMod 60753047) ^ (29664 + 29664 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 29664 * (5 : ZMod 60753047) ^ 29664) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 39596864 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 60753047) ^ 118658 = 39310846 := by
        calc
          (5 : ZMod 60753047) ^ 118658 = (5 : ZMod 60753047) ^ (59329 + 59329) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 59329 * (5 : ZMod 60753047) ^ 59329 := by rw [pow_add]
          _ = 39310846 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 60753047) ^ 237316 = 41836002 := by
        calc
          (5 : ZMod 60753047) ^ 237316 = (5 : ZMod 60753047) ^ (118658 + 118658) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 118658 * (5 : ZMod 60753047) ^ 118658 := by rw [pow_add]
          _ = 41836002 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 60753047) ^ 474633 = 37461100 := by
        calc
          (5 : ZMod 60753047) ^ 474633 = (5 : ZMod 60753047) ^ (237316 + 237316 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 237316 * (5 : ZMod 60753047) ^ 237316) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 37461100 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 60753047) ^ 949266 = 48840517 := by
        calc
          (5 : ZMod 60753047) ^ 949266 = (5 : ZMod 60753047) ^ (474633 + 474633) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 474633 * (5 : ZMod 60753047) ^ 474633 := by rw [pow_add]
          _ = 48840517 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 60753047) ^ 1898532 = 6498219 := by
        calc
          (5 : ZMod 60753047) ^ 1898532 = (5 : ZMod 60753047) ^ (949266 + 949266) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 949266 * (5 : ZMod 60753047) ^ 949266 := by rw [pow_add]
          _ = 6498219 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 60753047) ^ 3797065 = 37163363 := by
        calc
          (5 : ZMod 60753047) ^ 3797065 = (5 : ZMod 60753047) ^ (1898532 + 1898532 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 1898532 * (5 : ZMod 60753047) ^ 1898532) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 37163363 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 60753047) ^ 7594130 = 7189985 := by
        calc
          (5 : ZMod 60753047) ^ 7594130 = (5 : ZMod 60753047) ^ (3797065 + 3797065) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 3797065 * (5 : ZMod 60753047) ^ 3797065 := by rw [pow_add]
          _ = 7189985 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 60753047) ^ 15188261 = 54512348 := by
        calc
          (5 : ZMod 60753047) ^ 15188261 = (5 : ZMod 60753047) ^ (7594130 + 7594130 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 7594130 * (5 : ZMod 60753047) ^ 7594130) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 54512348 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 60753047) ^ 30376523 = 60753046 := by
        calc
          (5 : ZMod 60753047) ^ 30376523 = (5 : ZMod 60753047) ^ (15188261 + 15188261 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 15188261 * (5 : ZMod 60753047) ^ 15188261) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 60753046 := by rw [factor_0_23]; decide
      change (5 : ZMod 60753047) ^ 30376523 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (5 : ZMod 60753047) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 60753047) ^ 2 = 25 := by
        calc
          (5 : ZMod 60753047) ^ 2 = (5 : ZMod 60753047) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 1 * (5 : ZMod 60753047) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 60753047) ^ 4 = 625 := by
        calc
          (5 : ZMod 60753047) ^ 4 = (5 : ZMod 60753047) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 2 * (5 : ZMod 60753047) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 60753047) ^ 9 = 1953125 := by
        calc
          (5 : ZMod 60753047) ^ 9 = (5 : ZMod 60753047) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 4 * (5 : ZMod 60753047) ^ 4) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 1953125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 60753047) ^ 19 = 6469428 := by
        calc
          (5 : ZMod 60753047) ^ 19 = (5 : ZMod 60753047) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 9 * (5 : ZMod 60753047) ^ 9) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 6469428 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 60753047) ^ 39 = 38414647 := by
        calc
          (5 : ZMod 60753047) ^ 39 = (5 : ZMod 60753047) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 19 * (5 : ZMod 60753047) ^ 19) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 38414647 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 60753047) ^ 78 = 32327591 := by
        calc
          (5 : ZMod 60753047) ^ 78 = (5 : ZMod 60753047) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 39 * (5 : ZMod 60753047) ^ 39 := by rw [pow_add]
          _ = 32327591 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 60753047) ^ 157 = 15041413 := by
        calc
          (5 : ZMod 60753047) ^ 157 = (5 : ZMod 60753047) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 78 * (5 : ZMod 60753047) ^ 78) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 15041413 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 60753047) ^ 315 = 5103785 := by
        calc
          (5 : ZMod 60753047) ^ 315 = (5 : ZMod 60753047) ^ (157 + 157 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 157 * (5 : ZMod 60753047) ^ 157) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 5103785 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 60753047) ^ 631 = 56189008 := by
        calc
          (5 : ZMod 60753047) ^ 631 = (5 : ZMod 60753047) ^ (315 + 315 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 315 * (5 : ZMod 60753047) ^ 315) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 56189008 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 60753047) ^ 1262 = 54768631 := by
        calc
          (5 : ZMod 60753047) ^ 1262 = (5 : ZMod 60753047) ^ (631 + 631) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 631 * (5 : ZMod 60753047) ^ 631 := by rw [pow_add]
          _ = 54768631 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 60753047) ^ 2524 = 42691120 := by
        calc
          (5 : ZMod 60753047) ^ 2524 = (5 : ZMod 60753047) ^ (1262 + 1262) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 1262 * (5 : ZMod 60753047) ^ 1262 := by rw [pow_add]
          _ = 42691120 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 60753047) ^ 5049 = 3238864 := by
        calc
          (5 : ZMod 60753047) ^ 5049 = (5 : ZMod 60753047) ^ (2524 + 2524 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 2524 * (5 : ZMod 60753047) ^ 2524) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 3238864 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 60753047) ^ 10098 = 11385006 := by
        calc
          (5 : ZMod 60753047) ^ 10098 = (5 : ZMod 60753047) ^ (5049 + 5049) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 5049 * (5 : ZMod 60753047) ^ 5049 := by rw [pow_add]
          _ = 11385006 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 60753047) ^ 20197 = 52295006 := by
        calc
          (5 : ZMod 60753047) ^ 20197 = (5 : ZMod 60753047) ^ (10098 + 10098 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 10098 * (5 : ZMod 60753047) ^ 10098) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 52295006 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 60753047) ^ 40394 = 43629865 := by
        calc
          (5 : ZMod 60753047) ^ 40394 = (5 : ZMod 60753047) ^ (20197 + 20197) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 20197 * (5 : ZMod 60753047) ^ 20197 := by rw [pow_add]
          _ = 43629865 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 60753047) ^ 80788 = 44026074 := by
        calc
          (5 : ZMod 60753047) ^ 80788 = (5 : ZMod 60753047) ^ (40394 + 40394) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 40394 * (5 : ZMod 60753047) ^ 40394 := by rw [pow_add]
          _ = 44026074 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 60753047) ^ 161577 = 24060431 := by
        calc
          (5 : ZMod 60753047) ^ 161577 = (5 : ZMod 60753047) ^ (80788 + 80788 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 80788 * (5 : ZMod 60753047) ^ 80788) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 24060431 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 60753047) ^ 323154 = 37368644 := by
        calc
          (5 : ZMod 60753047) ^ 323154 = (5 : ZMod 60753047) ^ (161577 + 161577) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 161577 * (5 : ZMod 60753047) ^ 161577 := by rw [pow_add]
          _ = 37368644 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 60753047) ^ 646309 = 6071501 := by
        calc
          (5 : ZMod 60753047) ^ 646309 = (5 : ZMod 60753047) ^ (323154 + 323154 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 323154 * (5 : ZMod 60753047) ^ 323154) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 6071501 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 60753047) ^ 1292618 = 58817858 := by
        calc
          (5 : ZMod 60753047) ^ 1292618 = (5 : ZMod 60753047) ^ (646309 + 646309) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 646309 * (5 : ZMod 60753047) ^ 646309 := by rw [pow_add]
          _ = 58817858 := by rw [factor_1_19]; decide
      change (5 : ZMod 60753047) ^ 1292618 ≠ 1
      rw [factor_1_20]
      decide
    ·
      have factor_2_0 : (5 : ZMod 60753047) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 60753047) ^ 2 = 25 := by
        calc
          (5 : ZMod 60753047) ^ 2 = (5 : ZMod 60753047) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 1 * (5 : ZMod 60753047) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 60753047) ^ 5 = 3125 := by
        calc
          (5 : ZMod 60753047) ^ 5 = (5 : ZMod 60753047) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 2 * (5 : ZMod 60753047) ^ 2) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 60753047) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 60753047) ^ 11 = (5 : ZMod 60753047) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 5 * (5 : ZMod 60753047) ^ 5) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 60753047) ^ 23 = 33691398 := by
        calc
          (5 : ZMod 60753047) ^ 23 = (5 : ZMod 60753047) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 11 * (5 : ZMod 60753047) ^ 11) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 33691398 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 60753047) ^ 47 = 22640610 := by
        calc
          (5 : ZMod 60753047) ^ 47 = (5 : ZMod 60753047) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = ((5 : ZMod 60753047) ^ 23 * (5 : ZMod 60753047) ^ 23) * (5 : ZMod 60753047) := by rw [pow_succ, pow_add]
          _ = 22640610 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 60753047) ^ 94 = 9191723 := by
        calc
          (5 : ZMod 60753047) ^ 94 = (5 : ZMod 60753047) ^ (47 + 47) :=
            congrArg (fun n : ℕ => (5 : ZMod 60753047) ^ n) (by norm_num)
          _ = (5 : ZMod 60753047) ^ 47 * (5 : ZMod 60753047) ^ 47 := by rw [pow_add]
          _ = 9191723 := by rw [factor_2_5]; decide
      change (5 : ZMod 60753047) ^ 94 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_60753047

end TotientTailPeriodKiller
end Erdos249257
