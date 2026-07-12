import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_16731745181 : Nat.Prime 16731745181 := by
  apply lucas_primality 16731745181 (3 : ZMod 16731745181)
  ·
      have fermat_0 : (3 : ZMod 16731745181) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 16731745181) ^ 3 = 27 := by
        calc
          (3 : ZMod 16731745181) ^ 3 = (3 : ZMod 16731745181) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1 * (3 : ZMod 16731745181) ^ 1) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 16731745181) ^ 7 = 2187 := by
        calc
          (3 : ZMod 16731745181) ^ 7 = (3 : ZMod 16731745181) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 3 * (3 : ZMod 16731745181) ^ 3) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 16731745181) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 16731745181) ^ 15 = (3 : ZMod 16731745181) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 7 * (3 : ZMod 16731745181) ^ 7) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 16731745181) ^ 31 = 4291182151 := by
        calc
          (3 : ZMod 16731745181) ^ 31 = (3 : ZMod 16731745181) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 15 * (3 : ZMod 16731745181) ^ 15) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 4291182151 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 16731745181) ^ 62 = 2566851044 := by
        calc
          (3 : ZMod 16731745181) ^ 62 = (3 : ZMod 16731745181) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 31 * (3 : ZMod 16731745181) ^ 31 := by rw [pow_add]
          _ = 2566851044 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 16731745181) ^ 124 = 1513088439 := by
        calc
          (3 : ZMod 16731745181) ^ 124 = (3 : ZMod 16731745181) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 62 * (3 : ZMod 16731745181) ^ 62 := by rw [pow_add]
          _ = 1513088439 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 16731745181) ^ 249 = 4116518938 := by
        calc
          (3 : ZMod 16731745181) ^ 249 = (3 : ZMod 16731745181) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 124 * (3 : ZMod 16731745181) ^ 124) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 4116518938 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 16731745181) ^ 498 = 10791286423 := by
        calc
          (3 : ZMod 16731745181) ^ 498 = (3 : ZMod 16731745181) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 249 * (3 : ZMod 16731745181) ^ 249 := by rw [pow_add]
          _ = 10791286423 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 16731745181) ^ 997 = 6774702612 := by
        calc
          (3 : ZMod 16731745181) ^ 997 = (3 : ZMod 16731745181) ^ (498 + 498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 498 * (3 : ZMod 16731745181) ^ 498) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 6774702612 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 16731745181) ^ 1994 = 15858903269 := by
        calc
          (3 : ZMod 16731745181) ^ 1994 = (3 : ZMod 16731745181) ^ (997 + 997) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 997 * (3 : ZMod 16731745181) ^ 997 := by rw [pow_add]
          _ = 15858903269 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 16731745181) ^ 3989 = 8154598996 := by
        calc
          (3 : ZMod 16731745181) ^ 3989 = (3 : ZMod 16731745181) ^ (1994 + 1994 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1994 * (3 : ZMod 16731745181) ^ 1994) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 8154598996 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 16731745181) ^ 7978 = 12781517041 := by
        calc
          (3 : ZMod 16731745181) ^ 7978 = (3 : ZMod 16731745181) ^ (3989 + 3989) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 3989 * (3 : ZMod 16731745181) ^ 3989 := by rw [pow_add]
          _ = 12781517041 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 16731745181) ^ 15956 = 8986730317 := by
        calc
          (3 : ZMod 16731745181) ^ 15956 = (3 : ZMod 16731745181) ^ (7978 + 7978) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 7978 * (3 : ZMod 16731745181) ^ 7978 := by rw [pow_add]
          _ = 8986730317 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 16731745181) ^ 31913 = 3077141554 := by
        calc
          (3 : ZMod 16731745181) ^ 31913 = (3 : ZMod 16731745181) ^ (15956 + 15956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 15956 * (3 : ZMod 16731745181) ^ 15956) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 3077141554 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 16731745181) ^ 63826 = 7026884675 := by
        calc
          (3 : ZMod 16731745181) ^ 63826 = (3 : ZMod 16731745181) ^ (31913 + 31913) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 31913 * (3 : ZMod 16731745181) ^ 31913 := by rw [pow_add]
          _ = 7026884675 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 16731745181) ^ 127653 = 4172565948 := by
        calc
          (3 : ZMod 16731745181) ^ 127653 = (3 : ZMod 16731745181) ^ (63826 + 63826 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 63826 * (3 : ZMod 16731745181) ^ 63826) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 4172565948 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 16731745181) ^ 255306 = 12313009517 := by
        calc
          (3 : ZMod 16731745181) ^ 255306 = (3 : ZMod 16731745181) ^ (127653 + 127653) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 127653 * (3 : ZMod 16731745181) ^ 127653 := by rw [pow_add]
          _ = 12313009517 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 16731745181) ^ 510612 = 16102138874 := by
        calc
          (3 : ZMod 16731745181) ^ 510612 = (3 : ZMod 16731745181) ^ (255306 + 255306) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 255306 * (3 : ZMod 16731745181) ^ 255306 := by rw [pow_add]
          _ = 16102138874 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 16731745181) ^ 1021224 = 12166654033 := by
        calc
          (3 : ZMod 16731745181) ^ 1021224 = (3 : ZMod 16731745181) ^ (510612 + 510612) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 510612 * (3 : ZMod 16731745181) ^ 510612 := by rw [pow_add]
          _ = 12166654033 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 16731745181) ^ 2042449 = 15347291699 := by
        calc
          (3 : ZMod 16731745181) ^ 2042449 = (3 : ZMod 16731745181) ^ (1021224 + 1021224 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1021224 * (3 : ZMod 16731745181) ^ 1021224) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 15347291699 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 16731745181) ^ 4084898 = 16549300544 := by
        calc
          (3 : ZMod 16731745181) ^ 4084898 = (3 : ZMod 16731745181) ^ (2042449 + 2042449) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 2042449 * (3 : ZMod 16731745181) ^ 2042449 := by rw [pow_add]
          _ = 16549300544 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 16731745181) ^ 8169797 = 2828864003 := by
        calc
          (3 : ZMod 16731745181) ^ 8169797 = (3 : ZMod 16731745181) ^ (4084898 + 4084898 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 4084898 * (3 : ZMod 16731745181) ^ 4084898) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 2828864003 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 16731745181) ^ 16339594 = 13882089345 := by
        calc
          (3 : ZMod 16731745181) ^ 16339594 = (3 : ZMod 16731745181) ^ (8169797 + 8169797) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 8169797 * (3 : ZMod 16731745181) ^ 8169797 := by rw [pow_add]
          _ = 13882089345 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 16731745181) ^ 32679189 = 12239496364 := by
        calc
          (3 : ZMod 16731745181) ^ 32679189 = (3 : ZMod 16731745181) ^ (16339594 + 16339594 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 16339594 * (3 : ZMod 16731745181) ^ 16339594) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 12239496364 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 16731745181) ^ 65358379 = 11213469144 := by
        calc
          (3 : ZMod 16731745181) ^ 65358379 = (3 : ZMod 16731745181) ^ (32679189 + 32679189 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 32679189 * (3 : ZMod 16731745181) ^ 32679189) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 11213469144 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 16731745181) ^ 130716759 = 8568136029 := by
        calc
          (3 : ZMod 16731745181) ^ 130716759 = (3 : ZMod 16731745181) ^ (65358379 + 65358379 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 65358379 * (3 : ZMod 16731745181) ^ 65358379) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 8568136029 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 16731745181) ^ 261433518 = 5400257145 := by
        calc
          (3 : ZMod 16731745181) ^ 261433518 = (3 : ZMod 16731745181) ^ (130716759 + 130716759) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 130716759 * (3 : ZMod 16731745181) ^ 130716759 := by rw [pow_add]
          _ = 5400257145 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 16731745181) ^ 522867036 = 11170757650 := by
        calc
          (3 : ZMod 16731745181) ^ 522867036 = (3 : ZMod 16731745181) ^ (261433518 + 261433518) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 261433518 * (3 : ZMod 16731745181) ^ 261433518 := by rw [pow_add]
          _ = 11170757650 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 16731745181) ^ 1045734073 = 502209765 := by
        calc
          (3 : ZMod 16731745181) ^ 1045734073 = (3 : ZMod 16731745181) ^ (522867036 + 522867036 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 522867036 * (3 : ZMod 16731745181) ^ 522867036) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 502209765 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 16731745181) ^ 2091468147 = 9899408358 := by
        calc
          (3 : ZMod 16731745181) ^ 2091468147 = (3 : ZMod 16731745181) ^ (1045734073 + 1045734073 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1045734073 * (3 : ZMod 16731745181) ^ 1045734073) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 9899408358 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 16731745181) ^ 4182936295 = 5470814594 := by
        calc
          (3 : ZMod 16731745181) ^ 4182936295 = (3 : ZMod 16731745181) ^ (2091468147 + 2091468147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 2091468147 * (3 : ZMod 16731745181) ^ 2091468147) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 5470814594 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 16731745181) ^ 8365872590 = 16731745180 := by
        calc
          (3 : ZMod 16731745181) ^ 8365872590 = (3 : ZMod 16731745181) ^ (4182936295 + 4182936295) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 4182936295 * (3 : ZMod 16731745181) ^ 4182936295 := by rw [pow_add]
          _ = 16731745180 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 16731745181) ^ 16731745180 = 1 := by
        calc
          (3 : ZMod 16731745181) ^ 16731745180 = (3 : ZMod 16731745181) ^ (8365872590 + 8365872590) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 8365872590 * (3 : ZMod 16731745181) ^ 8365872590 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (67, 1), (12486377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (67, 1), (12486377, 1)] : List FactorBlock).map factorBlockValue).prod = 16731745181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 16731745181) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 16731745181) ^ 3 = 27 := by
        calc
          (3 : ZMod 16731745181) ^ 3 = (3 : ZMod 16731745181) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1 * (3 : ZMod 16731745181) ^ 1) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 16731745181) ^ 7 = 2187 := by
        calc
          (3 : ZMod 16731745181) ^ 7 = (3 : ZMod 16731745181) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 3 * (3 : ZMod 16731745181) ^ 3) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 16731745181) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 16731745181) ^ 15 = (3 : ZMod 16731745181) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 7 * (3 : ZMod 16731745181) ^ 7) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 16731745181) ^ 31 = 4291182151 := by
        calc
          (3 : ZMod 16731745181) ^ 31 = (3 : ZMod 16731745181) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 15 * (3 : ZMod 16731745181) ^ 15) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 4291182151 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 16731745181) ^ 62 = 2566851044 := by
        calc
          (3 : ZMod 16731745181) ^ 62 = (3 : ZMod 16731745181) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 31 * (3 : ZMod 16731745181) ^ 31 := by rw [pow_add]
          _ = 2566851044 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 16731745181) ^ 124 = 1513088439 := by
        calc
          (3 : ZMod 16731745181) ^ 124 = (3 : ZMod 16731745181) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 62 * (3 : ZMod 16731745181) ^ 62 := by rw [pow_add]
          _ = 1513088439 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 16731745181) ^ 249 = 4116518938 := by
        calc
          (3 : ZMod 16731745181) ^ 249 = (3 : ZMod 16731745181) ^ (124 + 124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 124 * (3 : ZMod 16731745181) ^ 124) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 4116518938 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 16731745181) ^ 498 = 10791286423 := by
        calc
          (3 : ZMod 16731745181) ^ 498 = (3 : ZMod 16731745181) ^ (249 + 249) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 249 * (3 : ZMod 16731745181) ^ 249 := by rw [pow_add]
          _ = 10791286423 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 16731745181) ^ 997 = 6774702612 := by
        calc
          (3 : ZMod 16731745181) ^ 997 = (3 : ZMod 16731745181) ^ (498 + 498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 498 * (3 : ZMod 16731745181) ^ 498) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 6774702612 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 16731745181) ^ 1994 = 15858903269 := by
        calc
          (3 : ZMod 16731745181) ^ 1994 = (3 : ZMod 16731745181) ^ (997 + 997) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 997 * (3 : ZMod 16731745181) ^ 997 := by rw [pow_add]
          _ = 15858903269 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 16731745181) ^ 3989 = 8154598996 := by
        calc
          (3 : ZMod 16731745181) ^ 3989 = (3 : ZMod 16731745181) ^ (1994 + 1994 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1994 * (3 : ZMod 16731745181) ^ 1994) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 8154598996 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 16731745181) ^ 7978 = 12781517041 := by
        calc
          (3 : ZMod 16731745181) ^ 7978 = (3 : ZMod 16731745181) ^ (3989 + 3989) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 3989 * (3 : ZMod 16731745181) ^ 3989 := by rw [pow_add]
          _ = 12781517041 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 16731745181) ^ 15956 = 8986730317 := by
        calc
          (3 : ZMod 16731745181) ^ 15956 = (3 : ZMod 16731745181) ^ (7978 + 7978) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 7978 * (3 : ZMod 16731745181) ^ 7978 := by rw [pow_add]
          _ = 8986730317 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 16731745181) ^ 31913 = 3077141554 := by
        calc
          (3 : ZMod 16731745181) ^ 31913 = (3 : ZMod 16731745181) ^ (15956 + 15956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 15956 * (3 : ZMod 16731745181) ^ 15956) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 3077141554 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 16731745181) ^ 63826 = 7026884675 := by
        calc
          (3 : ZMod 16731745181) ^ 63826 = (3 : ZMod 16731745181) ^ (31913 + 31913) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 31913 * (3 : ZMod 16731745181) ^ 31913 := by rw [pow_add]
          _ = 7026884675 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 16731745181) ^ 127653 = 4172565948 := by
        calc
          (3 : ZMod 16731745181) ^ 127653 = (3 : ZMod 16731745181) ^ (63826 + 63826 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 63826 * (3 : ZMod 16731745181) ^ 63826) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 4172565948 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 16731745181) ^ 255306 = 12313009517 := by
        calc
          (3 : ZMod 16731745181) ^ 255306 = (3 : ZMod 16731745181) ^ (127653 + 127653) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 127653 * (3 : ZMod 16731745181) ^ 127653 := by rw [pow_add]
          _ = 12313009517 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 16731745181) ^ 510612 = 16102138874 := by
        calc
          (3 : ZMod 16731745181) ^ 510612 = (3 : ZMod 16731745181) ^ (255306 + 255306) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 255306 * (3 : ZMod 16731745181) ^ 255306 := by rw [pow_add]
          _ = 16102138874 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 16731745181) ^ 1021224 = 12166654033 := by
        calc
          (3 : ZMod 16731745181) ^ 1021224 = (3 : ZMod 16731745181) ^ (510612 + 510612) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 510612 * (3 : ZMod 16731745181) ^ 510612 := by rw [pow_add]
          _ = 12166654033 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 16731745181) ^ 2042449 = 15347291699 := by
        calc
          (3 : ZMod 16731745181) ^ 2042449 = (3 : ZMod 16731745181) ^ (1021224 + 1021224 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1021224 * (3 : ZMod 16731745181) ^ 1021224) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 15347291699 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 16731745181) ^ 4084898 = 16549300544 := by
        calc
          (3 : ZMod 16731745181) ^ 4084898 = (3 : ZMod 16731745181) ^ (2042449 + 2042449) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 2042449 * (3 : ZMod 16731745181) ^ 2042449 := by rw [pow_add]
          _ = 16549300544 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 16731745181) ^ 8169797 = 2828864003 := by
        calc
          (3 : ZMod 16731745181) ^ 8169797 = (3 : ZMod 16731745181) ^ (4084898 + 4084898 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 4084898 * (3 : ZMod 16731745181) ^ 4084898) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 2828864003 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 16731745181) ^ 16339594 = 13882089345 := by
        calc
          (3 : ZMod 16731745181) ^ 16339594 = (3 : ZMod 16731745181) ^ (8169797 + 8169797) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 8169797 * (3 : ZMod 16731745181) ^ 8169797 := by rw [pow_add]
          _ = 13882089345 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 16731745181) ^ 32679189 = 12239496364 := by
        calc
          (3 : ZMod 16731745181) ^ 32679189 = (3 : ZMod 16731745181) ^ (16339594 + 16339594 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 16339594 * (3 : ZMod 16731745181) ^ 16339594) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 12239496364 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 16731745181) ^ 65358379 = 11213469144 := by
        calc
          (3 : ZMod 16731745181) ^ 65358379 = (3 : ZMod 16731745181) ^ (32679189 + 32679189 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 32679189 * (3 : ZMod 16731745181) ^ 32679189) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 11213469144 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 16731745181) ^ 130716759 = 8568136029 := by
        calc
          (3 : ZMod 16731745181) ^ 130716759 = (3 : ZMod 16731745181) ^ (65358379 + 65358379 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 65358379 * (3 : ZMod 16731745181) ^ 65358379) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 8568136029 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 16731745181) ^ 261433518 = 5400257145 := by
        calc
          (3 : ZMod 16731745181) ^ 261433518 = (3 : ZMod 16731745181) ^ (130716759 + 130716759) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 130716759 * (3 : ZMod 16731745181) ^ 130716759 := by rw [pow_add]
          _ = 5400257145 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 16731745181) ^ 522867036 = 11170757650 := by
        calc
          (3 : ZMod 16731745181) ^ 522867036 = (3 : ZMod 16731745181) ^ (261433518 + 261433518) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 261433518 * (3 : ZMod 16731745181) ^ 261433518 := by rw [pow_add]
          _ = 11170757650 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 16731745181) ^ 1045734073 = 502209765 := by
        calc
          (3 : ZMod 16731745181) ^ 1045734073 = (3 : ZMod 16731745181) ^ (522867036 + 522867036 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 522867036 * (3 : ZMod 16731745181) ^ 522867036) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 502209765 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 16731745181) ^ 2091468147 = 9899408358 := by
        calc
          (3 : ZMod 16731745181) ^ 2091468147 = (3 : ZMod 16731745181) ^ (1045734073 + 1045734073 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1045734073 * (3 : ZMod 16731745181) ^ 1045734073) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 9899408358 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 16731745181) ^ 4182936295 = 5470814594 := by
        calc
          (3 : ZMod 16731745181) ^ 4182936295 = (3 : ZMod 16731745181) ^ (2091468147 + 2091468147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 2091468147 * (3 : ZMod 16731745181) ^ 2091468147) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 5470814594 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 16731745181) ^ 8365872590 = 16731745180 := by
        calc
          (3 : ZMod 16731745181) ^ 8365872590 = (3 : ZMod 16731745181) ^ (4182936295 + 4182936295) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 4182936295 * (3 : ZMod 16731745181) ^ 4182936295 := by rw [pow_add]
          _ = 16731745180 := by rw [factor_0_31]; decide
      change (3 : ZMod 16731745181) ^ 8365872590 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (3 : ZMod 16731745181) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 16731745181) ^ 3 = 27 := by
        calc
          (3 : ZMod 16731745181) ^ 3 = (3 : ZMod 16731745181) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1 * (3 : ZMod 16731745181) ^ 1) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 16731745181) ^ 6 = 729 := by
        calc
          (3 : ZMod 16731745181) ^ 6 = (3 : ZMod 16731745181) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 3 * (3 : ZMod 16731745181) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 16731745181) ^ 12 = 531441 := by
        calc
          (3 : ZMod 16731745181) ^ 12 = (3 : ZMod 16731745181) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 6 * (3 : ZMod 16731745181) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 16731745181) ^ 24 = 14721613585 := by
        calc
          (3 : ZMod 16731745181) ^ 24 = (3 : ZMod 16731745181) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 12 * (3 : ZMod 16731745181) ^ 12 := by rw [pow_add]
          _ = 14721613585 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 16731745181) ^ 49 = 2915479004 := by
        calc
          (3 : ZMod 16731745181) ^ 49 = (3 : ZMod 16731745181) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 24 * (3 : ZMod 16731745181) ^ 24) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 2915479004 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 16731745181) ^ 99 = 13790163504 := by
        calc
          (3 : ZMod 16731745181) ^ 99 = (3 : ZMod 16731745181) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 49 * (3 : ZMod 16731745181) ^ 49) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 13790163504 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 16731745181) ^ 199 = 848961650 := by
        calc
          (3 : ZMod 16731745181) ^ 199 = (3 : ZMod 16731745181) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 99 * (3 : ZMod 16731745181) ^ 99) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 848961650 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 16731745181) ^ 398 = 14145990007 := by
        calc
          (3 : ZMod 16731745181) ^ 398 = (3 : ZMod 16731745181) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 199 * (3 : ZMod 16731745181) ^ 199 := by rw [pow_add]
          _ = 14145990007 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 16731745181) ^ 797 = 1190287175 := by
        calc
          (3 : ZMod 16731745181) ^ 797 = (3 : ZMod 16731745181) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 398 * (3 : ZMod 16731745181) ^ 398) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 1190287175 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 16731745181) ^ 1595 = 5197319345 := by
        calc
          (3 : ZMod 16731745181) ^ 1595 = (3 : ZMod 16731745181) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 797 * (3 : ZMod 16731745181) ^ 797) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 5197319345 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 16731745181) ^ 3191 = 5918199783 := by
        calc
          (3 : ZMod 16731745181) ^ 3191 = (3 : ZMod 16731745181) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1595 * (3 : ZMod 16731745181) ^ 1595) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 5918199783 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 16731745181) ^ 6382 = 3020081743 := by
        calc
          (3 : ZMod 16731745181) ^ 6382 = (3 : ZMod 16731745181) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 3191 * (3 : ZMod 16731745181) ^ 3191 := by rw [pow_add]
          _ = 3020081743 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 16731745181) ^ 12765 = 14551862223 := by
        calc
          (3 : ZMod 16731745181) ^ 12765 = (3 : ZMod 16731745181) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 6382 * (3 : ZMod 16731745181) ^ 6382) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 14551862223 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 16731745181) ^ 25530 = 7738913477 := by
        calc
          (3 : ZMod 16731745181) ^ 25530 = (3 : ZMod 16731745181) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 12765 * (3 : ZMod 16731745181) ^ 12765 := by rw [pow_add]
          _ = 7738913477 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 16731745181) ^ 51061 = 5776352590 := by
        calc
          (3 : ZMod 16731745181) ^ 51061 = (3 : ZMod 16731745181) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 25530 * (3 : ZMod 16731745181) ^ 25530) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 5776352590 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 16731745181) ^ 102122 = 3617269194 := by
        calc
          (3 : ZMod 16731745181) ^ 102122 = (3 : ZMod 16731745181) ^ (51061 + 51061) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 51061 * (3 : ZMod 16731745181) ^ 51061 := by rw [pow_add]
          _ = 3617269194 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 16731745181) ^ 204244 = 5729231131 := by
        calc
          (3 : ZMod 16731745181) ^ 204244 = (3 : ZMod 16731745181) ^ (102122 + 102122) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 102122 * (3 : ZMod 16731745181) ^ 102122 := by rw [pow_add]
          _ = 5729231131 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 16731745181) ^ 408489 = 150637051 := by
        calc
          (3 : ZMod 16731745181) ^ 408489 = (3 : ZMod 16731745181) ^ (204244 + 204244 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 204244 * (3 : ZMod 16731745181) ^ 204244) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 150637051 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 16731745181) ^ 816979 = 2471200556 := by
        calc
          (3 : ZMod 16731745181) ^ 816979 = (3 : ZMod 16731745181) ^ (408489 + 408489 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 408489 * (3 : ZMod 16731745181) ^ 408489) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 2471200556 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 16731745181) ^ 1633959 = 13971211755 := by
        calc
          (3 : ZMod 16731745181) ^ 1633959 = (3 : ZMod 16731745181) ^ (816979 + 816979 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 816979 * (3 : ZMod 16731745181) ^ 816979) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 13971211755 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 16731745181) ^ 3267918 = 8824924606 := by
        calc
          (3 : ZMod 16731745181) ^ 3267918 = (3 : ZMod 16731745181) ^ (1633959 + 1633959) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 1633959 * (3 : ZMod 16731745181) ^ 1633959 := by rw [pow_add]
          _ = 8824924606 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 16731745181) ^ 6535837 = 9764388995 := by
        calc
          (3 : ZMod 16731745181) ^ 6535837 = (3 : ZMod 16731745181) ^ (3267918 + 3267918 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 3267918 * (3 : ZMod 16731745181) ^ 3267918) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 9764388995 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 16731745181) ^ 13071675 = 3925558349 := by
        calc
          (3 : ZMod 16731745181) ^ 13071675 = (3 : ZMod 16731745181) ^ (6535837 + 6535837 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 6535837 * (3 : ZMod 16731745181) ^ 6535837) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 3925558349 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 16731745181) ^ 26143351 = 6869447006 := by
        calc
          (3 : ZMod 16731745181) ^ 26143351 = (3 : ZMod 16731745181) ^ (13071675 + 13071675 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 13071675 * (3 : ZMod 16731745181) ^ 13071675) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 6869447006 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 16731745181) ^ 52286703 = 3636182599 := by
        calc
          (3 : ZMod 16731745181) ^ 52286703 = (3 : ZMod 16731745181) ^ (26143351 + 26143351 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 26143351 * (3 : ZMod 16731745181) ^ 26143351) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 3636182599 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 16731745181) ^ 104573407 = 16439455550 := by
        calc
          (3 : ZMod 16731745181) ^ 104573407 = (3 : ZMod 16731745181) ^ (52286703 + 52286703 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 52286703 * (3 : ZMod 16731745181) ^ 52286703) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 16439455550 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 16731745181) ^ 209146814 = 518200025 := by
        calc
          (3 : ZMod 16731745181) ^ 209146814 = (3 : ZMod 16731745181) ^ (104573407 + 104573407) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 104573407 * (3 : ZMod 16731745181) ^ 104573407 := by rw [pow_add]
          _ = 518200025 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 16731745181) ^ 418293629 = 5159656750 := by
        calc
          (3 : ZMod 16731745181) ^ 418293629 = (3 : ZMod 16731745181) ^ (209146814 + 209146814 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 209146814 * (3 : ZMod 16731745181) ^ 209146814) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 5159656750 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 16731745181) ^ 836587259 = 419955161 := by
        calc
          (3 : ZMod 16731745181) ^ 836587259 = (3 : ZMod 16731745181) ^ (418293629 + 418293629 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 418293629 * (3 : ZMod 16731745181) ^ 418293629) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 419955161 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 16731745181) ^ 1673174518 = 5167100579 := by
        calc
          (3 : ZMod 16731745181) ^ 1673174518 = (3 : ZMod 16731745181) ^ (836587259 + 836587259) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 836587259 * (3 : ZMod 16731745181) ^ 836587259 := by rw [pow_add]
          _ = 5167100579 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 16731745181) ^ 3346349036 = 3554476644 := by
        calc
          (3 : ZMod 16731745181) ^ 3346349036 = (3 : ZMod 16731745181) ^ (1673174518 + 1673174518) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 1673174518 * (3 : ZMod 16731745181) ^ 1673174518 := by rw [pow_add]
          _ = 3554476644 := by rw [factor_1_30]; decide
      change (3 : ZMod 16731745181) ^ 3346349036 ≠ 1
      rw [factor_1_31]
      decide
    ·
      have factor_2_0 : (3 : ZMod 16731745181) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 16731745181) ^ 3 = 27 := by
        calc
          (3 : ZMod 16731745181) ^ 3 = (3 : ZMod 16731745181) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 1 * (3 : ZMod 16731745181) ^ 1) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 16731745181) ^ 7 = 2187 := by
        calc
          (3 : ZMod 16731745181) ^ 7 = (3 : ZMod 16731745181) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 3 * (3 : ZMod 16731745181) ^ 3) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 16731745181) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 16731745181) ^ 14 = (3 : ZMod 16731745181) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 7 * (3 : ZMod 16731745181) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 16731745181) ^ 29 = 13490377602 := by
        calc
          (3 : ZMod 16731745181) ^ 29 = (3 : ZMod 16731745181) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 14 * (3 : ZMod 16731745181) ^ 14) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 13490377602 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 16731745181) ^ 59 = 3193539887 := by
        calc
          (3 : ZMod 16731745181) ^ 59 = (3 : ZMod 16731745181) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 29 * (3 : ZMod 16731745181) ^ 29) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 3193539887 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 16731745181) ^ 119 = 1039050478 := by
        calc
          (3 : ZMod 16731745181) ^ 119 = (3 : ZMod 16731745181) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 59 * (3 : ZMod 16731745181) ^ 59) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 1039050478 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 16731745181) ^ 238 = 15712640065 := by
        calc
          (3 : ZMod 16731745181) ^ 238 = (3 : ZMod 16731745181) ^ (119 + 119) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 119 * (3 : ZMod 16731745181) ^ 119 := by rw [pow_add]
          _ = 15712640065 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 16731745181) ^ 476 = 8138016116 := by
        calc
          (3 : ZMod 16731745181) ^ 476 = (3 : ZMod 16731745181) ^ (238 + 238) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 238 * (3 : ZMod 16731745181) ^ 238 := by rw [pow_add]
          _ = 8138016116 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 16731745181) ^ 952 = 13687225398 := by
        calc
          (3 : ZMod 16731745181) ^ 952 = (3 : ZMod 16731745181) ^ (476 + 476) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 476 * (3 : ZMod 16731745181) ^ 476 := by rw [pow_add]
          _ = 13687225398 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 16731745181) ^ 1905 = 8404376929 := by
        calc
          (3 : ZMod 16731745181) ^ 1905 = (3 : ZMod 16731745181) ^ (952 + 952 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 952 * (3 : ZMod 16731745181) ^ 952) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 8404376929 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 16731745181) ^ 3810 = 13423388239 := by
        calc
          (3 : ZMod 16731745181) ^ 3810 = (3 : ZMod 16731745181) ^ (1905 + 1905) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 1905 * (3 : ZMod 16731745181) ^ 1905 := by rw [pow_add]
          _ = 13423388239 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 16731745181) ^ 7621 = 16658103763 := by
        calc
          (3 : ZMod 16731745181) ^ 7621 = (3 : ZMod 16731745181) ^ (3810 + 3810 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 3810 * (3 : ZMod 16731745181) ^ 3810) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 16658103763 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 16731745181) ^ 15242 = 15392220547 := by
        calc
          (3 : ZMod 16731745181) ^ 15242 = (3 : ZMod 16731745181) ^ (7621 + 7621) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 7621 * (3 : ZMod 16731745181) ^ 7621 := by rw [pow_add]
          _ = 15392220547 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 16731745181) ^ 30484 = 4533893726 := by
        calc
          (3 : ZMod 16731745181) ^ 30484 = (3 : ZMod 16731745181) ^ (15242 + 15242) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 15242 * (3 : ZMod 16731745181) ^ 15242 := by rw [pow_add]
          _ = 4533893726 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 16731745181) ^ 60968 = 11087517785 := by
        calc
          (3 : ZMod 16731745181) ^ 60968 = (3 : ZMod 16731745181) ^ (30484 + 30484) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 30484 * (3 : ZMod 16731745181) ^ 30484 := by rw [pow_add]
          _ = 11087517785 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 16731745181) ^ 121937 = 1771477897 := by
        calc
          (3 : ZMod 16731745181) ^ 121937 = (3 : ZMod 16731745181) ^ (60968 + 60968 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 60968 * (3 : ZMod 16731745181) ^ 60968) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 1771477897 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 16731745181) ^ 243874 = 10891638624 := by
        calc
          (3 : ZMod 16731745181) ^ 243874 = (3 : ZMod 16731745181) ^ (121937 + 121937) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 121937 * (3 : ZMod 16731745181) ^ 121937 := by rw [pow_add]
          _ = 10891638624 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 16731745181) ^ 487749 = 14685928207 := by
        calc
          (3 : ZMod 16731745181) ^ 487749 = (3 : ZMod 16731745181) ^ (243874 + 243874 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 243874 * (3 : ZMod 16731745181) ^ 243874) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 14685928207 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 16731745181) ^ 975498 = 7916620996 := by
        calc
          (3 : ZMod 16731745181) ^ 975498 = (3 : ZMod 16731745181) ^ (487749 + 487749) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 487749 * (3 : ZMod 16731745181) ^ 487749 := by rw [pow_add]
          _ = 7916620996 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 16731745181) ^ 1950996 = 13560630377 := by
        calc
          (3 : ZMod 16731745181) ^ 1950996 = (3 : ZMod 16731745181) ^ (975498 + 975498) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 975498 * (3 : ZMod 16731745181) ^ 975498 := by rw [pow_add]
          _ = 13560630377 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 16731745181) ^ 3901992 = 6424250446 := by
        calc
          (3 : ZMod 16731745181) ^ 3901992 = (3 : ZMod 16731745181) ^ (1950996 + 1950996) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 1950996 * (3 : ZMod 16731745181) ^ 1950996 := by rw [pow_add]
          _ = 6424250446 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 16731745181) ^ 7803985 = 7719122135 := by
        calc
          (3 : ZMod 16731745181) ^ 7803985 = (3 : ZMod 16731745181) ^ (3901992 + 3901992 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 3901992 * (3 : ZMod 16731745181) ^ 3901992) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 7719122135 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 16731745181) ^ 15607971 = 7946596457 := by
        calc
          (3 : ZMod 16731745181) ^ 15607971 = (3 : ZMod 16731745181) ^ (7803985 + 7803985 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 7803985 * (3 : ZMod 16731745181) ^ 7803985) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 7946596457 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 16731745181) ^ 31215942 = 6365457864 := by
        calc
          (3 : ZMod 16731745181) ^ 31215942 = (3 : ZMod 16731745181) ^ (15607971 + 15607971) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 15607971 * (3 : ZMod 16731745181) ^ 15607971 := by rw [pow_add]
          _ = 6365457864 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 16731745181) ^ 62431885 = 15069010987 := by
        calc
          (3 : ZMod 16731745181) ^ 62431885 = (3 : ZMod 16731745181) ^ (31215942 + 31215942 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 31215942 * (3 : ZMod 16731745181) ^ 31215942) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 15069010987 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 16731745181) ^ 124863770 = 9611886555 := by
        calc
          (3 : ZMod 16731745181) ^ 124863770 = (3 : ZMod 16731745181) ^ (62431885 + 62431885) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 62431885 * (3 : ZMod 16731745181) ^ 62431885 := by rw [pow_add]
          _ = 9611886555 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 16731745181) ^ 249727540 = 12954079559 := by
        calc
          (3 : ZMod 16731745181) ^ 249727540 = (3 : ZMod 16731745181) ^ (124863770 + 124863770) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 124863770 * (3 : ZMod 16731745181) ^ 124863770 := by rw [pow_add]
          _ = 12954079559 := by rw [factor_2_26]; decide
      change (3 : ZMod 16731745181) ^ 249727540 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (3 : ZMod 16731745181) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 16731745181) ^ 2 = 9 := by
        calc
          (3 : ZMod 16731745181) ^ 2 = (3 : ZMod 16731745181) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 1 * (3 : ZMod 16731745181) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 16731745181) ^ 5 = 243 := by
        calc
          (3 : ZMod 16731745181) ^ 5 = (3 : ZMod 16731745181) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 2 * (3 : ZMod 16731745181) ^ 2) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 16731745181) ^ 10 = 59049 := by
        calc
          (3 : ZMod 16731745181) ^ 10 = (3 : ZMod 16731745181) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 5 * (3 : ZMod 16731745181) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 16731745181) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 16731745181) ^ 20 = (3 : ZMod 16731745181) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 10 * (3 : ZMod 16731745181) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 16731745181) ^ 41 = 4465813335 := by
        calc
          (3 : ZMod 16731745181) ^ 41 = (3 : ZMod 16731745181) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 20 * (3 : ZMod 16731745181) ^ 20) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 4465813335 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 16731745181) ^ 83 = 14403370882 := by
        calc
          (3 : ZMod 16731745181) ^ 83 = (3 : ZMod 16731745181) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 41 * (3 : ZMod 16731745181) ^ 41) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 14403370882 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 16731745181) ^ 167 = 12282083894 := by
        calc
          (3 : ZMod 16731745181) ^ 167 = (3 : ZMod 16731745181) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 83 * (3 : ZMod 16731745181) ^ 83) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 12282083894 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 16731745181) ^ 335 = 3392008426 := by
        calc
          (3 : ZMod 16731745181) ^ 335 = (3 : ZMod 16731745181) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = ((3 : ZMod 16731745181) ^ 167 * (3 : ZMod 16731745181) ^ 167) * (3 : ZMod 16731745181) := by rw [pow_succ, pow_add]
          _ = 3392008426 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 16731745181) ^ 670 = 7104434973 := by
        calc
          (3 : ZMod 16731745181) ^ 670 = (3 : ZMod 16731745181) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 335 * (3 : ZMod 16731745181) ^ 335 := by rw [pow_add]
          _ = 7104434973 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 16731745181) ^ 1340 = 2354626766 := by
        calc
          (3 : ZMod 16731745181) ^ 1340 = (3 : ZMod 16731745181) ^ (670 + 670) :=
            congrArg (fun n : ℕ => (3 : ZMod 16731745181) ^ n) (by norm_num)
          _ = (3 : ZMod 16731745181) ^ 670 * (3 : ZMod 16731745181) ^ 670 := by rw [pow_add]
          _ = 2354626766 := by rw [factor_3_9]; decide
      change (3 : ZMod 16731745181) ^ 1340 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_16731745181

end TotientTailPeriodKiller
end Erdos249257
