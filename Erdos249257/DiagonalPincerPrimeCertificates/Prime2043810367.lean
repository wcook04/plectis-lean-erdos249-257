import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2043810367 : Nat.Prime 2043810367 := by
  apply lucas_primality 2043810367 (3 : ZMod 2043810367)
  ·
      have fermat_0 : (3 : ZMod 2043810367) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 2043810367) ^ 3 = 27 := by
        calc
          (3 : ZMod 2043810367) ^ 3 = (3 : ZMod 2043810367) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1 * (3 : ZMod 2043810367) ^ 1) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 2043810367) ^ 7 = 2187 := by
        calc
          (3 : ZMod 2043810367) ^ 7 = (3 : ZMod 2043810367) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 3 * (3 : ZMod 2043810367) ^ 3) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 2043810367) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 2043810367) ^ 15 = (3 : ZMod 2043810367) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 7 * (3 : ZMod 2043810367) ^ 7) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 2043810367) ^ 30 = 1763343803 := by
        calc
          (3 : ZMod 2043810367) ^ 30 = (3 : ZMod 2043810367) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 15 * (3 : ZMod 2043810367) ^ 15 := by rw [pow_add]
          _ = 1763343803 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 2043810367) ^ 60 = 705722307 := by
        calc
          (3 : ZMod 2043810367) ^ 60 = (3 : ZMod 2043810367) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 30 * (3 : ZMod 2043810367) ^ 30 := by rw [pow_add]
          _ = 705722307 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 2043810367) ^ 121 = 1680775037 := by
        calc
          (3 : ZMod 2043810367) ^ 121 = (3 : ZMod 2043810367) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 60 * (3 : ZMod 2043810367) ^ 60) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1680775037 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 2043810367) ^ 243 = 1596260159 := by
        calc
          (3 : ZMod 2043810367) ^ 243 = (3 : ZMod 2043810367) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 121 * (3 : ZMod 2043810367) ^ 121) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1596260159 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 2043810367) ^ 487 = 312052689 := by
        calc
          (3 : ZMod 2043810367) ^ 487 = (3 : ZMod 2043810367) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 243 * (3 : ZMod 2043810367) ^ 243) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 312052689 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 2043810367) ^ 974 = 1765179397 := by
        calc
          (3 : ZMod 2043810367) ^ 974 = (3 : ZMod 2043810367) ^ (487 + 487) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 487 * (3 : ZMod 2043810367) ^ 487 := by rw [pow_add]
          _ = 1765179397 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 2043810367) ^ 1949 = 474695638 := by
        calc
          (3 : ZMod 2043810367) ^ 1949 = (3 : ZMod 2043810367) ^ (974 + 974 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 974 * (3 : ZMod 2043810367) ^ 974) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 474695638 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 2043810367) ^ 3898 = 257775589 := by
        calc
          (3 : ZMod 2043810367) ^ 3898 = (3 : ZMod 2043810367) ^ (1949 + 1949) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1949 * (3 : ZMod 2043810367) ^ 1949 := by rw [pow_add]
          _ = 257775589 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 2043810367) ^ 7796 = 1998152739 := by
        calc
          (3 : ZMod 2043810367) ^ 7796 = (3 : ZMod 2043810367) ^ (3898 + 3898) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3898 * (3 : ZMod 2043810367) ^ 3898 := by rw [pow_add]
          _ = 1998152739 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 2043810367) ^ 15593 = 1641775852 := by
        calc
          (3 : ZMod 2043810367) ^ 15593 = (3 : ZMod 2043810367) ^ (7796 + 7796 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 7796 * (3 : ZMod 2043810367) ^ 7796) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1641775852 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 2043810367) ^ 31186 = 515467513 := by
        calc
          (3 : ZMod 2043810367) ^ 31186 = (3 : ZMod 2043810367) ^ (15593 + 15593) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 15593 * (3 : ZMod 2043810367) ^ 15593 := by rw [pow_add]
          _ = 515467513 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 2043810367) ^ 62372 = 698936575 := by
        calc
          (3 : ZMod 2043810367) ^ 62372 = (3 : ZMod 2043810367) ^ (31186 + 31186) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 31186 * (3 : ZMod 2043810367) ^ 31186 := by rw [pow_add]
          _ = 698936575 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 2043810367) ^ 124744 = 1216830431 := by
        calc
          (3 : ZMod 2043810367) ^ 124744 = (3 : ZMod 2043810367) ^ (62372 + 62372) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 62372 * (3 : ZMod 2043810367) ^ 62372 := by rw [pow_add]
          _ = 1216830431 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 2043810367) ^ 249488 = 1540774517 := by
        calc
          (3 : ZMod 2043810367) ^ 249488 = (3 : ZMod 2043810367) ^ (124744 + 124744) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 124744 * (3 : ZMod 2043810367) ^ 124744 := by rw [pow_add]
          _ = 1540774517 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 2043810367) ^ 498977 = 360690124 := by
        calc
          (3 : ZMod 2043810367) ^ 498977 = (3 : ZMod 2043810367) ^ (249488 + 249488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 249488 * (3 : ZMod 2043810367) ^ 249488) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 360690124 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 2043810367) ^ 997954 = 299368835 := by
        calc
          (3 : ZMod 2043810367) ^ 997954 = (3 : ZMod 2043810367) ^ (498977 + 498977) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 498977 * (3 : ZMod 2043810367) ^ 498977 := by rw [pow_add]
          _ = 299368835 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 2043810367) ^ 1995908 = 1633197125 := by
        calc
          (3 : ZMod 2043810367) ^ 1995908 = (3 : ZMod 2043810367) ^ (997954 + 997954) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 997954 * (3 : ZMod 2043810367) ^ 997954 := by rw [pow_add]
          _ = 1633197125 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 2043810367) ^ 3991817 = 845182600 := by
        calc
          (3 : ZMod 2043810367) ^ 3991817 = (3 : ZMod 2043810367) ^ (1995908 + 1995908 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1995908 * (3 : ZMod 2043810367) ^ 1995908) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 845182600 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 2043810367) ^ 7983634 = 560556861 := by
        calc
          (3 : ZMod 2043810367) ^ 7983634 = (3 : ZMod 2043810367) ^ (3991817 + 3991817) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3991817 * (3 : ZMod 2043810367) ^ 3991817 := by rw [pow_add]
          _ = 560556861 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 2043810367) ^ 15967268 = 500431187 := by
        calc
          (3 : ZMod 2043810367) ^ 15967268 = (3 : ZMod 2043810367) ^ (7983634 + 7983634) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 7983634 * (3 : ZMod 2043810367) ^ 7983634 := by rw [pow_add]
          _ = 500431187 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 2043810367) ^ 31934536 = 162838466 := by
        calc
          (3 : ZMod 2043810367) ^ 31934536 = (3 : ZMod 2043810367) ^ (15967268 + 15967268) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 15967268 * (3 : ZMod 2043810367) ^ 15967268 := by rw [pow_add]
          _ = 162838466 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 2043810367) ^ 63869073 = 850981616 := by
        calc
          (3 : ZMod 2043810367) ^ 63869073 = (3 : ZMod 2043810367) ^ (31934536 + 31934536 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 31934536 * (3 : ZMod 2043810367) ^ 31934536) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 850981616 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 2043810367) ^ 127738147 = 1974199964 := by
        calc
          (3 : ZMod 2043810367) ^ 127738147 = (3 : ZMod 2043810367) ^ (63869073 + 63869073 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 63869073 * (3 : ZMod 2043810367) ^ 63869073) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1974199964 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 2043810367) ^ 255476295 = 606849724 := by
        calc
          (3 : ZMod 2043810367) ^ 255476295 = (3 : ZMod 2043810367) ^ (127738147 + 127738147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 127738147 * (3 : ZMod 2043810367) ^ 127738147) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 606849724 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 2043810367) ^ 510952591 = 1391134248 := by
        calc
          (3 : ZMod 2043810367) ^ 510952591 = (3 : ZMod 2043810367) ^ (255476295 + 255476295 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 255476295 * (3 : ZMod 2043810367) ^ 255476295) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1391134248 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 2043810367) ^ 1021905183 = 2043810366 := by
        calc
          (3 : ZMod 2043810367) ^ 1021905183 = (3 : ZMod 2043810367) ^ (510952591 + 510952591 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 510952591 * (3 : ZMod 2043810367) ^ 510952591) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 2043810366 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 2043810367) ^ 2043810366 = 1 := by
        calc
          (3 : ZMod 2043810367) ^ 2043810366 = (3 : ZMod 2043810367) ^ (1021905183 + 1021905183) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1021905183 * (3 : ZMod 2043810367) ^ 1021905183 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (37, 1), (293, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (37, 1), (293, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod = 2043810367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 2043810367) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 2043810367) ^ 3 = 27 := by
        calc
          (3 : ZMod 2043810367) ^ 3 = (3 : ZMod 2043810367) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1 * (3 : ZMod 2043810367) ^ 1) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 2043810367) ^ 7 = 2187 := by
        calc
          (3 : ZMod 2043810367) ^ 7 = (3 : ZMod 2043810367) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 3 * (3 : ZMod 2043810367) ^ 3) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 2043810367) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 2043810367) ^ 15 = (3 : ZMod 2043810367) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 7 * (3 : ZMod 2043810367) ^ 7) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 2043810367) ^ 30 = 1763343803 := by
        calc
          (3 : ZMod 2043810367) ^ 30 = (3 : ZMod 2043810367) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 15 * (3 : ZMod 2043810367) ^ 15 := by rw [pow_add]
          _ = 1763343803 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 2043810367) ^ 60 = 705722307 := by
        calc
          (3 : ZMod 2043810367) ^ 60 = (3 : ZMod 2043810367) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 30 * (3 : ZMod 2043810367) ^ 30 := by rw [pow_add]
          _ = 705722307 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 2043810367) ^ 121 = 1680775037 := by
        calc
          (3 : ZMod 2043810367) ^ 121 = (3 : ZMod 2043810367) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 60 * (3 : ZMod 2043810367) ^ 60) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1680775037 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 2043810367) ^ 243 = 1596260159 := by
        calc
          (3 : ZMod 2043810367) ^ 243 = (3 : ZMod 2043810367) ^ (121 + 121 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 121 * (3 : ZMod 2043810367) ^ 121) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1596260159 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 2043810367) ^ 487 = 312052689 := by
        calc
          (3 : ZMod 2043810367) ^ 487 = (3 : ZMod 2043810367) ^ (243 + 243 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 243 * (3 : ZMod 2043810367) ^ 243) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 312052689 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 2043810367) ^ 974 = 1765179397 := by
        calc
          (3 : ZMod 2043810367) ^ 974 = (3 : ZMod 2043810367) ^ (487 + 487) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 487 * (3 : ZMod 2043810367) ^ 487 := by rw [pow_add]
          _ = 1765179397 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 2043810367) ^ 1949 = 474695638 := by
        calc
          (3 : ZMod 2043810367) ^ 1949 = (3 : ZMod 2043810367) ^ (974 + 974 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 974 * (3 : ZMod 2043810367) ^ 974) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 474695638 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 2043810367) ^ 3898 = 257775589 := by
        calc
          (3 : ZMod 2043810367) ^ 3898 = (3 : ZMod 2043810367) ^ (1949 + 1949) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1949 * (3 : ZMod 2043810367) ^ 1949 := by rw [pow_add]
          _ = 257775589 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 2043810367) ^ 7796 = 1998152739 := by
        calc
          (3 : ZMod 2043810367) ^ 7796 = (3 : ZMod 2043810367) ^ (3898 + 3898) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3898 * (3 : ZMod 2043810367) ^ 3898 := by rw [pow_add]
          _ = 1998152739 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 2043810367) ^ 15593 = 1641775852 := by
        calc
          (3 : ZMod 2043810367) ^ 15593 = (3 : ZMod 2043810367) ^ (7796 + 7796 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 7796 * (3 : ZMod 2043810367) ^ 7796) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1641775852 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 2043810367) ^ 31186 = 515467513 := by
        calc
          (3 : ZMod 2043810367) ^ 31186 = (3 : ZMod 2043810367) ^ (15593 + 15593) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 15593 * (3 : ZMod 2043810367) ^ 15593 := by rw [pow_add]
          _ = 515467513 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 2043810367) ^ 62372 = 698936575 := by
        calc
          (3 : ZMod 2043810367) ^ 62372 = (3 : ZMod 2043810367) ^ (31186 + 31186) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 31186 * (3 : ZMod 2043810367) ^ 31186 := by rw [pow_add]
          _ = 698936575 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 2043810367) ^ 124744 = 1216830431 := by
        calc
          (3 : ZMod 2043810367) ^ 124744 = (3 : ZMod 2043810367) ^ (62372 + 62372) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 62372 * (3 : ZMod 2043810367) ^ 62372 := by rw [pow_add]
          _ = 1216830431 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 2043810367) ^ 249488 = 1540774517 := by
        calc
          (3 : ZMod 2043810367) ^ 249488 = (3 : ZMod 2043810367) ^ (124744 + 124744) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 124744 * (3 : ZMod 2043810367) ^ 124744 := by rw [pow_add]
          _ = 1540774517 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 2043810367) ^ 498977 = 360690124 := by
        calc
          (3 : ZMod 2043810367) ^ 498977 = (3 : ZMod 2043810367) ^ (249488 + 249488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 249488 * (3 : ZMod 2043810367) ^ 249488) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 360690124 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 2043810367) ^ 997954 = 299368835 := by
        calc
          (3 : ZMod 2043810367) ^ 997954 = (3 : ZMod 2043810367) ^ (498977 + 498977) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 498977 * (3 : ZMod 2043810367) ^ 498977 := by rw [pow_add]
          _ = 299368835 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 2043810367) ^ 1995908 = 1633197125 := by
        calc
          (3 : ZMod 2043810367) ^ 1995908 = (3 : ZMod 2043810367) ^ (997954 + 997954) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 997954 * (3 : ZMod 2043810367) ^ 997954 := by rw [pow_add]
          _ = 1633197125 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 2043810367) ^ 3991817 = 845182600 := by
        calc
          (3 : ZMod 2043810367) ^ 3991817 = (3 : ZMod 2043810367) ^ (1995908 + 1995908 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1995908 * (3 : ZMod 2043810367) ^ 1995908) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 845182600 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 2043810367) ^ 7983634 = 560556861 := by
        calc
          (3 : ZMod 2043810367) ^ 7983634 = (3 : ZMod 2043810367) ^ (3991817 + 3991817) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3991817 * (3 : ZMod 2043810367) ^ 3991817 := by rw [pow_add]
          _ = 560556861 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 2043810367) ^ 15967268 = 500431187 := by
        calc
          (3 : ZMod 2043810367) ^ 15967268 = (3 : ZMod 2043810367) ^ (7983634 + 7983634) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 7983634 * (3 : ZMod 2043810367) ^ 7983634 := by rw [pow_add]
          _ = 500431187 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 2043810367) ^ 31934536 = 162838466 := by
        calc
          (3 : ZMod 2043810367) ^ 31934536 = (3 : ZMod 2043810367) ^ (15967268 + 15967268) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 15967268 * (3 : ZMod 2043810367) ^ 15967268 := by rw [pow_add]
          _ = 162838466 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 2043810367) ^ 63869073 = 850981616 := by
        calc
          (3 : ZMod 2043810367) ^ 63869073 = (3 : ZMod 2043810367) ^ (31934536 + 31934536 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 31934536 * (3 : ZMod 2043810367) ^ 31934536) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 850981616 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 2043810367) ^ 127738147 = 1974199964 := by
        calc
          (3 : ZMod 2043810367) ^ 127738147 = (3 : ZMod 2043810367) ^ (63869073 + 63869073 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 63869073 * (3 : ZMod 2043810367) ^ 63869073) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1974199964 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 2043810367) ^ 255476295 = 606849724 := by
        calc
          (3 : ZMod 2043810367) ^ 255476295 = (3 : ZMod 2043810367) ^ (127738147 + 127738147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 127738147 * (3 : ZMod 2043810367) ^ 127738147) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 606849724 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 2043810367) ^ 510952591 = 1391134248 := by
        calc
          (3 : ZMod 2043810367) ^ 510952591 = (3 : ZMod 2043810367) ^ (255476295 + 255476295 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 255476295 * (3 : ZMod 2043810367) ^ 255476295) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1391134248 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 2043810367) ^ 1021905183 = 2043810366 := by
        calc
          (3 : ZMod 2043810367) ^ 1021905183 = (3 : ZMod 2043810367) ^ (510952591 + 510952591 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 510952591 * (3 : ZMod 2043810367) ^ 510952591) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 2043810366 := by rw [factor_0_28]; decide
      change (3 : ZMod 2043810367) ^ 1021905183 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (3 : ZMod 2043810367) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 2043810367) ^ 2 = 9 := by
        calc
          (3 : ZMod 2043810367) ^ 2 = (3 : ZMod 2043810367) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1 * (3 : ZMod 2043810367) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 2043810367) ^ 5 = 243 := by
        calc
          (3 : ZMod 2043810367) ^ 5 = (3 : ZMod 2043810367) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 2 * (3 : ZMod 2043810367) ^ 2) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 2043810367) ^ 10 = 59049 := by
        calc
          (3 : ZMod 2043810367) ^ 10 = (3 : ZMod 2043810367) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 5 * (3 : ZMod 2043810367) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 2043810367) ^ 20 = 1442974034 := by
        calc
          (3 : ZMod 2043810367) ^ 20 = (3 : ZMod 2043810367) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 10 * (3 : ZMod 2043810367) ^ 10 := by rw [pow_add]
          _ = 1442974034 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 2043810367) ^ 40 = 1769076532 := by
        calc
          (3 : ZMod 2043810367) ^ 40 = (3 : ZMod 2043810367) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 20 * (3 : ZMod 2043810367) ^ 20 := by rw [pow_add]
          _ = 1769076532 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 2043810367) ^ 81 = 653880635 := by
        calc
          (3 : ZMod 2043810367) ^ 81 = (3 : ZMod 2043810367) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 40 * (3 : ZMod 2043810367) ^ 40) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 653880635 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 2043810367) ^ 162 = 469004947 := by
        calc
          (3 : ZMod 2043810367) ^ 162 = (3 : ZMod 2043810367) ^ (81 + 81) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 81 * (3 : ZMod 2043810367) ^ 81 := by rw [pow_add]
          _ = 469004947 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 2043810367) ^ 324 = 1820919453 := by
        calc
          (3 : ZMod 2043810367) ^ 324 = (3 : ZMod 2043810367) ^ (162 + 162) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 162 * (3 : ZMod 2043810367) ^ 162 := by rw [pow_add]
          _ = 1820919453 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 2043810367) ^ 649 = 929832340 := by
        calc
          (3 : ZMod 2043810367) ^ 649 = (3 : ZMod 2043810367) ^ (324 + 324 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 324 * (3 : ZMod 2043810367) ^ 324) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 929832340 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 2043810367) ^ 1299 = 1228256907 := by
        calc
          (3 : ZMod 2043810367) ^ 1299 = (3 : ZMod 2043810367) ^ (649 + 649 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 649 * (3 : ZMod 2043810367) ^ 649) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1228256907 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 2043810367) ^ 2598 = 939033297 := by
        calc
          (3 : ZMod 2043810367) ^ 2598 = (3 : ZMod 2043810367) ^ (1299 + 1299) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1299 * (3 : ZMod 2043810367) ^ 1299 := by rw [pow_add]
          _ = 939033297 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 2043810367) ^ 5197 = 569979721 := by
        calc
          (3 : ZMod 2043810367) ^ 5197 = (3 : ZMod 2043810367) ^ (2598 + 2598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 2598 * (3 : ZMod 2043810367) ^ 2598) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 569979721 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 2043810367) ^ 10395 = 1146729686 := by
        calc
          (3 : ZMod 2043810367) ^ 10395 = (3 : ZMod 2043810367) ^ (5197 + 5197 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 5197 * (3 : ZMod 2043810367) ^ 5197) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1146729686 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 2043810367) ^ 20790 = 1010050504 := by
        calc
          (3 : ZMod 2043810367) ^ 20790 = (3 : ZMod 2043810367) ^ (10395 + 10395) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 10395 * (3 : ZMod 2043810367) ^ 10395 := by rw [pow_add]
          _ = 1010050504 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 2043810367) ^ 41581 = 520875442 := by
        calc
          (3 : ZMod 2043810367) ^ 41581 = (3 : ZMod 2043810367) ^ (20790 + 20790 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 20790 * (3 : ZMod 2043810367) ^ 20790) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 520875442 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 2043810367) ^ 83162 = 476581481 := by
        calc
          (3 : ZMod 2043810367) ^ 83162 = (3 : ZMod 2043810367) ^ (41581 + 41581) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 41581 * (3 : ZMod 2043810367) ^ 41581 := by rw [pow_add]
          _ = 476581481 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 2043810367) ^ 166325 = 705530399 := by
        calc
          (3 : ZMod 2043810367) ^ 166325 = (3 : ZMod 2043810367) ^ (83162 + 83162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 83162 * (3 : ZMod 2043810367) ^ 83162) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 705530399 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 2043810367) ^ 332651 = 1913542339 := by
        calc
          (3 : ZMod 2043810367) ^ 332651 = (3 : ZMod 2043810367) ^ (166325 + 166325 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 166325 * (3 : ZMod 2043810367) ^ 166325) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1913542339 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 2043810367) ^ 665302 = 1641807784 := by
        calc
          (3 : ZMod 2043810367) ^ 665302 = (3 : ZMod 2043810367) ^ (332651 + 332651) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 332651 * (3 : ZMod 2043810367) ^ 332651 := by rw [pow_add]
          _ = 1641807784 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 2043810367) ^ 1330605 = 1046053293 := by
        calc
          (3 : ZMod 2043810367) ^ 1330605 = (3 : ZMod 2043810367) ^ (665302 + 665302 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 665302 * (3 : ZMod 2043810367) ^ 665302) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1046053293 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 2043810367) ^ 2661211 = 1757927197 := by
        calc
          (3 : ZMod 2043810367) ^ 2661211 = (3 : ZMod 2043810367) ^ (1330605 + 1330605 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1330605 * (3 : ZMod 2043810367) ^ 1330605) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1757927197 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 2043810367) ^ 5322422 = 114069855 := by
        calc
          (3 : ZMod 2043810367) ^ 5322422 = (3 : ZMod 2043810367) ^ (2661211 + 2661211) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 2661211 * (3 : ZMod 2043810367) ^ 2661211 := by rw [pow_add]
          _ = 114069855 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 2043810367) ^ 10644845 = 522249602 := by
        calc
          (3 : ZMod 2043810367) ^ 10644845 = (3 : ZMod 2043810367) ^ (5322422 + 5322422 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 5322422 * (3 : ZMod 2043810367) ^ 5322422) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 522249602 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 2043810367) ^ 21289691 = 708930149 := by
        calc
          (3 : ZMod 2043810367) ^ 21289691 = (3 : ZMod 2043810367) ^ (10644845 + 10644845 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 10644845 * (3 : ZMod 2043810367) ^ 10644845) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 708930149 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 2043810367) ^ 42579382 = 281678502 := by
        calc
          (3 : ZMod 2043810367) ^ 42579382 = (3 : ZMod 2043810367) ^ (21289691 + 21289691) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 21289691 * (3 : ZMod 2043810367) ^ 21289691 := by rw [pow_add]
          _ = 281678502 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 2043810367) ^ 85158765 = 1687332571 := by
        calc
          (3 : ZMod 2043810367) ^ 85158765 = (3 : ZMod 2043810367) ^ (42579382 + 42579382 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 42579382 * (3 : ZMod 2043810367) ^ 42579382) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1687332571 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 2043810367) ^ 170317530 = 1717472307 := by
        calc
          (3 : ZMod 2043810367) ^ 170317530 = (3 : ZMod 2043810367) ^ (85158765 + 85158765) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 85158765 * (3 : ZMod 2043810367) ^ 85158765 := by rw [pow_add]
          _ = 1717472307 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 2043810367) ^ 340635061 = 979014179 := by
        calc
          (3 : ZMod 2043810367) ^ 340635061 = (3 : ZMod 2043810367) ^ (170317530 + 170317530 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 170317530 * (3 : ZMod 2043810367) ^ 170317530) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 979014179 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 2043810367) ^ 681270122 = 979014178 := by
        calc
          (3 : ZMod 2043810367) ^ 681270122 = (3 : ZMod 2043810367) ^ (340635061 + 340635061) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 340635061 * (3 : ZMod 2043810367) ^ 340635061 := by rw [pow_add]
          _ = 979014178 := by rw [factor_1_28]; decide
      change (3 : ZMod 2043810367) ^ 681270122 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (3 : ZMod 2043810367) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 2043810367) ^ 2 = 9 := by
        calc
          (3 : ZMod 2043810367) ^ 2 = (3 : ZMod 2043810367) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1 * (3 : ZMod 2043810367) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 2043810367) ^ 4 = 81 := by
        calc
          (3 : ZMod 2043810367) ^ 4 = (3 : ZMod 2043810367) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 2 * (3 : ZMod 2043810367) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 2043810367) ^ 9 = 19683 := by
        calc
          (3 : ZMod 2043810367) ^ 9 = (3 : ZMod 2043810367) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 4 * (3 : ZMod 2043810367) ^ 4) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 2043810367) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 2043810367) ^ 18 = (3 : ZMod 2043810367) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 9 * (3 : ZMod 2043810367) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 2043810367) ^ 37 = 1806544999 := by
        calc
          (3 : ZMod 2043810367) ^ 37 = (3 : ZMod 2043810367) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 18 * (3 : ZMod 2043810367) ^ 18) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1806544999 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 2043810367) ^ 74 = 1080612101 := by
        calc
          (3 : ZMod 2043810367) ^ 74 = (3 : ZMod 2043810367) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 37 * (3 : ZMod 2043810367) ^ 37 := by rw [pow_add]
          _ = 1080612101 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 2043810367) ^ 149 = 133313315 := by
        calc
          (3 : ZMod 2043810367) ^ 149 = (3 : ZMod 2043810367) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 74 * (3 : ZMod 2043810367) ^ 74) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 133313315 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 2043810367) ^ 299 = 1449520137 := by
        calc
          (3 : ZMod 2043810367) ^ 299 = (3 : ZMod 2043810367) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 149 * (3 : ZMod 2043810367) ^ 149) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1449520137 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 2043810367) ^ 599 = 423201489 := by
        calc
          (3 : ZMod 2043810367) ^ 599 = (3 : ZMod 2043810367) ^ (299 + 299 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 299 * (3 : ZMod 2043810367) ^ 299) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 423201489 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 2043810367) ^ 1199 = 1953377402 := by
        calc
          (3 : ZMod 2043810367) ^ 1199 = (3 : ZMod 2043810367) ^ (599 + 599 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 599 * (3 : ZMod 2043810367) ^ 599) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1953377402 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 2043810367) ^ 2398 = 2005694489 := by
        calc
          (3 : ZMod 2043810367) ^ 2398 = (3 : ZMod 2043810367) ^ (1199 + 1199) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1199 * (3 : ZMod 2043810367) ^ 1199 := by rw [pow_add]
          _ = 2005694489 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 2043810367) ^ 4797 = 114728913 := by
        calc
          (3 : ZMod 2043810367) ^ 4797 = (3 : ZMod 2043810367) ^ (2398 + 2398 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 2398 * (3 : ZMod 2043810367) ^ 2398) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 114728913 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 2043810367) ^ 9595 = 554749821 := by
        calc
          (3 : ZMod 2043810367) ^ 9595 = (3 : ZMod 2043810367) ^ (4797 + 4797 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 4797 * (3 : ZMod 2043810367) ^ 4797) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 554749821 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 2043810367) ^ 19191 = 1973328621 := by
        calc
          (3 : ZMod 2043810367) ^ 19191 = (3 : ZMod 2043810367) ^ (9595 + 9595 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 9595 * (3 : ZMod 2043810367) ^ 9595) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1973328621 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 2043810367) ^ 38382 = 1260230151 := by
        calc
          (3 : ZMod 2043810367) ^ 38382 = (3 : ZMod 2043810367) ^ (19191 + 19191) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 19191 * (3 : ZMod 2043810367) ^ 19191 := by rw [pow_add]
          _ = 1260230151 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 2043810367) ^ 76765 = 3705341 := by
        calc
          (3 : ZMod 2043810367) ^ 76765 = (3 : ZMod 2043810367) ^ (38382 + 38382 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 38382 * (3 : ZMod 2043810367) ^ 38382) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 3705341 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 2043810367) ^ 153531 = 1789263059 := by
        calc
          (3 : ZMod 2043810367) ^ 153531 = (3 : ZMod 2043810367) ^ (76765 + 76765 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 76765 * (3 : ZMod 2043810367) ^ 76765) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1789263059 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 2043810367) ^ 307062 = 562431560 := by
        calc
          (3 : ZMod 2043810367) ^ 307062 = (3 : ZMod 2043810367) ^ (153531 + 153531) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 153531 * (3 : ZMod 2043810367) ^ 153531 := by rw [pow_add]
          _ = 562431560 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 2043810367) ^ 614125 = 208098429 := by
        calc
          (3 : ZMod 2043810367) ^ 614125 = (3 : ZMod 2043810367) ^ (307062 + 307062 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 307062 * (3 : ZMod 2043810367) ^ 307062) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 208098429 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 2043810367) ^ 1228251 = 1164138113 := by
        calc
          (3 : ZMod 2043810367) ^ 1228251 = (3 : ZMod 2043810367) ^ (614125 + 614125 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 614125 * (3 : ZMod 2043810367) ^ 614125) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1164138113 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 2043810367) ^ 2456502 = 1509446169 := by
        calc
          (3 : ZMod 2043810367) ^ 2456502 = (3 : ZMod 2043810367) ^ (1228251 + 1228251) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1228251 * (3 : ZMod 2043810367) ^ 1228251 := by rw [pow_add]
          _ = 1509446169 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 2043810367) ^ 4913005 = 1506456684 := by
        calc
          (3 : ZMod 2043810367) ^ 4913005 = (3 : ZMod 2043810367) ^ (2456502 + 2456502 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 2456502 * (3 : ZMod 2043810367) ^ 2456502) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1506456684 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 2043810367) ^ 9826011 = 1219058902 := by
        calc
          (3 : ZMod 2043810367) ^ 9826011 = (3 : ZMod 2043810367) ^ (4913005 + 4913005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 4913005 * (3 : ZMod 2043810367) ^ 4913005) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1219058902 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 2043810367) ^ 19652022 = 1039081535 := by
        calc
          (3 : ZMod 2043810367) ^ 19652022 = (3 : ZMod 2043810367) ^ (9826011 + 9826011) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 9826011 * (3 : ZMod 2043810367) ^ 9826011 := by rw [pow_add]
          _ = 1039081535 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 2043810367) ^ 39304045 = 386931247 := by
        calc
          (3 : ZMod 2043810367) ^ 39304045 = (3 : ZMod 2043810367) ^ (19652022 + 19652022 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 19652022 * (3 : ZMod 2043810367) ^ 19652022) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 386931247 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 2043810367) ^ 78608091 = 2006026592 := by
        calc
          (3 : ZMod 2043810367) ^ 78608091 = (3 : ZMod 2043810367) ^ (39304045 + 39304045 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 39304045 * (3 : ZMod 2043810367) ^ 39304045) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 2006026592 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 2043810367) ^ 157216182 = 1892849290 := by
        calc
          (3 : ZMod 2043810367) ^ 157216182 = (3 : ZMod 2043810367) ^ (78608091 + 78608091) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 78608091 * (3 : ZMod 2043810367) ^ 78608091 := by rw [pow_add]
          _ = 1892849290 := by rw [factor_2_26]; decide
      change (3 : ZMod 2043810367) ^ 157216182 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (3 : ZMod 2043810367) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 2043810367) ^ 3 = 27 := by
        calc
          (3 : ZMod 2043810367) ^ 3 = (3 : ZMod 2043810367) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1 * (3 : ZMod 2043810367) ^ 1) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 2043810367) ^ 6 = 729 := by
        calc
          (3 : ZMod 2043810367) ^ 6 = (3 : ZMod 2043810367) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3 * (3 : ZMod 2043810367) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 2043810367) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 2043810367) ^ 13 = (3 : ZMod 2043810367) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 6 * (3 : ZMod 2043810367) ^ 6) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 2043810367) ^ 26 = 1409542148 := by
        calc
          (3 : ZMod 2043810367) ^ 26 = (3 : ZMod 2043810367) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 13 * (3 : ZMod 2043810367) ^ 13 := by rw [pow_add]
          _ = 1409542148 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 2043810367) ^ 52 = 900991511 := by
        calc
          (3 : ZMod 2043810367) ^ 52 = (3 : ZMod 2043810367) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 26 * (3 : ZMod 2043810367) ^ 26 := by rw [pow_add]
          _ = 900991511 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 2043810367) ^ 105 = 1837847615 := by
        calc
          (3 : ZMod 2043810367) ^ 105 = (3 : ZMod 2043810367) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 52 * (3 : ZMod 2043810367) ^ 52) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1837847615 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 2043810367) ^ 210 = 1691382614 := by
        calc
          (3 : ZMod 2043810367) ^ 210 = (3 : ZMod 2043810367) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 105 * (3 : ZMod 2043810367) ^ 105 := by rw [pow_add]
          _ = 1691382614 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 2043810367) ^ 421 = 583399843 := by
        calc
          (3 : ZMod 2043810367) ^ 421 = (3 : ZMod 2043810367) ^ (210 + 210 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 210 * (3 : ZMod 2043810367) ^ 210) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 583399843 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 2043810367) ^ 842 = 194159975 := by
        calc
          (3 : ZMod 2043810367) ^ 842 = (3 : ZMod 2043810367) ^ (421 + 421) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 421 * (3 : ZMod 2043810367) ^ 421 := by rw [pow_add]
          _ = 194159975 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 2043810367) ^ 1685 = 141849535 := by
        calc
          (3 : ZMod 2043810367) ^ 1685 = (3 : ZMod 2043810367) ^ (842 + 842 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 842 * (3 : ZMod 2043810367) ^ 842) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 141849535 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 2043810367) ^ 3371 = 2039356153 := by
        calc
          (3 : ZMod 2043810367) ^ 3371 = (3 : ZMod 2043810367) ^ (1685 + 1685 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1685 * (3 : ZMod 2043810367) ^ 1685) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 2039356153 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 2043810367) ^ 6742 = 755125327 := by
        calc
          (3 : ZMod 2043810367) ^ 6742 = (3 : ZMod 2043810367) ^ (3371 + 3371) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3371 * (3 : ZMod 2043810367) ^ 3371 := by rw [pow_add]
          _ = 755125327 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 2043810367) ^ 13485 = 1296789309 := by
        calc
          (3 : ZMod 2043810367) ^ 13485 = (3 : ZMod 2043810367) ^ (6742 + 6742 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 6742 * (3 : ZMod 2043810367) ^ 6742) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1296789309 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 2043810367) ^ 26971 = 1341637970 := by
        calc
          (3 : ZMod 2043810367) ^ 26971 = (3 : ZMod 2043810367) ^ (13485 + 13485 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 13485 * (3 : ZMod 2043810367) ^ 13485) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1341637970 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 2043810367) ^ 53943 = 594801800 := by
        calc
          (3 : ZMod 2043810367) ^ 53943 = (3 : ZMod 2043810367) ^ (26971 + 26971 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 26971 * (3 : ZMod 2043810367) ^ 26971) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 594801800 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 2043810367) ^ 107886 = 583703319 := by
        calc
          (3 : ZMod 2043810367) ^ 107886 = (3 : ZMod 2043810367) ^ (53943 + 53943) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 53943 * (3 : ZMod 2043810367) ^ 53943 := by rw [pow_add]
          _ = 583703319 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 2043810367) ^ 215773 = 1276922530 := by
        calc
          (3 : ZMod 2043810367) ^ 215773 = (3 : ZMod 2043810367) ^ (107886 + 107886 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 107886 * (3 : ZMod 2043810367) ^ 107886) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1276922530 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 2043810367) ^ 431547 = 1739368126 := by
        calc
          (3 : ZMod 2043810367) ^ 431547 = (3 : ZMod 2043810367) ^ (215773 + 215773 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 215773 * (3 : ZMod 2043810367) ^ 215773) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1739368126 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 2043810367) ^ 863095 = 637564019 := by
        calc
          (3 : ZMod 2043810367) ^ 863095 = (3 : ZMod 2043810367) ^ (431547 + 431547 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 431547 * (3 : ZMod 2043810367) ^ 431547) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 637564019 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 2043810367) ^ 1726191 = 1223105473 := by
        calc
          (3 : ZMod 2043810367) ^ 1726191 = (3 : ZMod 2043810367) ^ (863095 + 863095 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 863095 * (3 : ZMod 2043810367) ^ 863095) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1223105473 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 2043810367) ^ 3452382 = 1272462634 := by
        calc
          (3 : ZMod 2043810367) ^ 3452382 = (3 : ZMod 2043810367) ^ (1726191 + 1726191) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 1726191 * (3 : ZMod 2043810367) ^ 1726191 := by rw [pow_add]
          _ = 1272462634 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 2043810367) ^ 6904764 = 189156854 := by
        calc
          (3 : ZMod 2043810367) ^ 6904764 = (3 : ZMod 2043810367) ^ (3452382 + 3452382) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3452382 * (3 : ZMod 2043810367) ^ 3452382 := by rw [pow_add]
          _ = 189156854 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 2043810367) ^ 13809529 = 1244967544 := by
        calc
          (3 : ZMod 2043810367) ^ 13809529 = (3 : ZMod 2043810367) ^ (6904764 + 6904764 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 6904764 * (3 : ZMod 2043810367) ^ 6904764) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1244967544 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 2043810367) ^ 27619059 = 1097052132 := by
        calc
          (3 : ZMod 2043810367) ^ 27619059 = (3 : ZMod 2043810367) ^ (13809529 + 13809529 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 13809529 * (3 : ZMod 2043810367) ^ 13809529) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1097052132 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 2043810367) ^ 55238118 = 2029120675 := by
        calc
          (3 : ZMod 2043810367) ^ 55238118 = (3 : ZMod 2043810367) ^ (27619059 + 27619059) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 27619059 * (3 : ZMod 2043810367) ^ 27619059 := by rw [pow_add]
          _ = 2029120675 := by rw [factor_3_24]; decide
      change (3 : ZMod 2043810367) ^ 55238118 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (3 : ZMod 2043810367) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 2043810367) ^ 3 = 27 := by
        calc
          (3 : ZMod 2043810367) ^ 3 = (3 : ZMod 2043810367) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1 * (3 : ZMod 2043810367) ^ 1) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 2043810367) ^ 6 = 729 := by
        calc
          (3 : ZMod 2043810367) ^ 6 = (3 : ZMod 2043810367) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3 * (3 : ZMod 2043810367) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 2043810367) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 2043810367) ^ 13 = (3 : ZMod 2043810367) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 6 * (3 : ZMod 2043810367) ^ 6) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 2043810367) ^ 26 = 1409542148 := by
        calc
          (3 : ZMod 2043810367) ^ 26 = (3 : ZMod 2043810367) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 13 * (3 : ZMod 2043810367) ^ 13 := by rw [pow_add]
          _ = 1409542148 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 2043810367) ^ 53 = 659164166 := by
        calc
          (3 : ZMod 2043810367) ^ 53 = (3 : ZMod 2043810367) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 26 * (3 : ZMod 2043810367) ^ 26) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 659164166 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 2043810367) ^ 106 = 1425922111 := by
        calc
          (3 : ZMod 2043810367) ^ 106 = (3 : ZMod 2043810367) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 53 * (3 : ZMod 2043810367) ^ 53 := by rw [pow_add]
          _ = 1425922111 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 2043810367) ^ 212 = 915770957 := by
        calc
          (3 : ZMod 2043810367) ^ 212 = (3 : ZMod 2043810367) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 106 * (3 : ZMod 2043810367) ^ 106 := by rw [pow_add]
          _ = 915770957 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 2043810367) ^ 425 = 247748842 := by
        calc
          (3 : ZMod 2043810367) ^ 425 = (3 : ZMod 2043810367) ^ (212 + 212 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 212 * (3 : ZMod 2043810367) ^ 212) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 247748842 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 2043810367) ^ 851 = 1769212002 := by
        calc
          (3 : ZMod 2043810367) ^ 851 = (3 : ZMod 2043810367) ^ (425 + 425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 425 * (3 : ZMod 2043810367) ^ 425) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1769212002 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 2043810367) ^ 1702 = 45369171 := by
        calc
          (3 : ZMod 2043810367) ^ 1702 = (3 : ZMod 2043810367) ^ (851 + 851) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 851 * (3 : ZMod 2043810367) ^ 851 := by rw [pow_add]
          _ = 45369171 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 2043810367) ^ 3405 = 185052970 := by
        calc
          (3 : ZMod 2043810367) ^ 3405 = (3 : ZMod 2043810367) ^ (1702 + 1702 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1702 * (3 : ZMod 2043810367) ^ 1702) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 185052970 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 2043810367) ^ 6811 = 1095706760 := by
        calc
          (3 : ZMod 2043810367) ^ 6811 = (3 : ZMod 2043810367) ^ (3405 + 3405 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 3405 * (3 : ZMod 2043810367) ^ 3405) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1095706760 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 2043810367) ^ 13623 = 987592872 := by
        calc
          (3 : ZMod 2043810367) ^ 13623 = (3 : ZMod 2043810367) ^ (6811 + 6811 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 6811 * (3 : ZMod 2043810367) ^ 6811) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 987592872 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 2043810367) ^ 27247 = 939976923 := by
        calc
          (3 : ZMod 2043810367) ^ 27247 = (3 : ZMod 2043810367) ^ (13623 + 13623 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 13623 * (3 : ZMod 2043810367) ^ 13623) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 939976923 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 2043810367) ^ 54495 = 1832863910 := by
        calc
          (3 : ZMod 2043810367) ^ 54495 = (3 : ZMod 2043810367) ^ (27247 + 27247 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 27247 * (3 : ZMod 2043810367) ^ 27247) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1832863910 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 2043810367) ^ 108991 = 693740469 := by
        calc
          (3 : ZMod 2043810367) ^ 108991 = (3 : ZMod 2043810367) ^ (54495 + 54495 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 54495 * (3 : ZMod 2043810367) ^ 54495) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 693740469 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 2043810367) ^ 217983 = 1670887890 := by
        calc
          (3 : ZMod 2043810367) ^ 217983 = (3 : ZMod 2043810367) ^ (108991 + 108991 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 108991 * (3 : ZMod 2043810367) ^ 108991) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1670887890 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 2043810367) ^ 435966 = 1370213280 := by
        calc
          (3 : ZMod 2043810367) ^ 435966 = (3 : ZMod 2043810367) ^ (217983 + 217983) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 217983 * (3 : ZMod 2043810367) ^ 217983 := by rw [pow_add]
          _ = 1370213280 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 2043810367) ^ 871932 = 1242704739 := by
        calc
          (3 : ZMod 2043810367) ^ 871932 = (3 : ZMod 2043810367) ^ (435966 + 435966) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 435966 * (3 : ZMod 2043810367) ^ 435966 := by rw [pow_add]
          _ = 1242704739 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 2043810367) ^ 1743865 = 299254247 := by
        calc
          (3 : ZMod 2043810367) ^ 1743865 = (3 : ZMod 2043810367) ^ (871932 + 871932 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 871932 * (3 : ZMod 2043810367) ^ 871932) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 299254247 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 2043810367) ^ 3487731 = 881232122 := by
        calc
          (3 : ZMod 2043810367) ^ 3487731 = (3 : ZMod 2043810367) ^ (1743865 + 1743865 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1743865 * (3 : ZMod 2043810367) ^ 1743865) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 881232122 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 2043810367) ^ 6975462 = 953898887 := by
        calc
          (3 : ZMod 2043810367) ^ 6975462 = (3 : ZMod 2043810367) ^ (3487731 + 3487731) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3487731 * (3 : ZMod 2043810367) ^ 3487731 := by rw [pow_add]
          _ = 953898887 := by rw [factor_4_21]; decide
      change (3 : ZMod 2043810367) ^ 6975462 ≠ 1
      rw [factor_4_22]
      decide
    ·
      have factor_5_0 : (3 : ZMod 2043810367) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 2043810367) ^ 3 = 27 := by
        calc
          (3 : ZMod 2043810367) ^ 3 = (3 : ZMod 2043810367) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1 * (3 : ZMod 2043810367) ^ 1) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 2043810367) ^ 6 = 729 := by
        calc
          (3 : ZMod 2043810367) ^ 6 = (3 : ZMod 2043810367) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3 * (3 : ZMod 2043810367) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 2043810367) ^ 12 = 531441 := by
        calc
          (3 : ZMod 2043810367) ^ 12 = (3 : ZMod 2043810367) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 6 * (3 : ZMod 2043810367) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 2043810367) ^ 25 = 1151117505 := by
        calc
          (3 : ZMod 2043810367) ^ 25 = (3 : ZMod 2043810367) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 12 * (3 : ZMod 2043810367) ^ 12) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1151117505 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 2043810367) ^ 51 = 981600626 := by
        calc
          (3 : ZMod 2043810367) ^ 51 = (3 : ZMod 2043810367) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 25 * (3 : ZMod 2043810367) ^ 25) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 981600626 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 2043810367) ^ 103 = 1793835576 := by
        calc
          (3 : ZMod 2043810367) ^ 103 = (3 : ZMod 2043810367) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 51 * (3 : ZMod 2043810367) ^ 51) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1793835576 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 2043810367) ^ 206 = 1332957058 := by
        calc
          (3 : ZMod 2043810367) ^ 206 = (3 : ZMod 2043810367) ^ (103 + 103) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 103 * (3 : ZMod 2043810367) ^ 103 := by rw [pow_add]
          _ = 1332957058 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 2043810367) ^ 412 = 1700764792 := by
        calc
          (3 : ZMod 2043810367) ^ 412 = (3 : ZMod 2043810367) ^ (206 + 206) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 206 * (3 : ZMod 2043810367) ^ 206 := by rw [pow_add]
          _ = 1700764792 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 2043810367) ^ 825 = 923789584 := by
        calc
          (3 : ZMod 2043810367) ^ 825 = (3 : ZMod 2043810367) ^ (412 + 412 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 412 * (3 : ZMod 2043810367) ^ 412) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 923789584 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 2043810367) ^ 1651 = 789146284 := by
        calc
          (3 : ZMod 2043810367) ^ 1651 = (3 : ZMod 2043810367) ^ (825 + 825 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 825 * (3 : ZMod 2043810367) ^ 825) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 789146284 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 2043810367) ^ 3303 = 1664337046 := by
        calc
          (3 : ZMod 2043810367) ^ 3303 = (3 : ZMod 2043810367) ^ (1651 + 1651 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 1651 * (3 : ZMod 2043810367) ^ 1651) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1664337046 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 2043810367) ^ 6606 = 313833996 := by
        calc
          (3 : ZMod 2043810367) ^ 6606 = (3 : ZMod 2043810367) ^ (3303 + 3303) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 3303 * (3 : ZMod 2043810367) ^ 3303 := by rw [pow_add]
          _ = 313833996 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 2043810367) ^ 13212 = 1586988559 := by
        calc
          (3 : ZMod 2043810367) ^ 13212 = (3 : ZMod 2043810367) ^ (6606 + 6606) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 6606 * (3 : ZMod 2043810367) ^ 6606 := by rw [pow_add]
          _ = 1586988559 := by rw [factor_5_12]; decide
      have factor_5_14 : (3 : ZMod 2043810367) ^ 26424 = 443511990 := by
        calc
          (3 : ZMod 2043810367) ^ 26424 = (3 : ZMod 2043810367) ^ (13212 + 13212) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 13212 * (3 : ZMod 2043810367) ^ 13212 := by rw [pow_add]
          _ = 443511990 := by rw [factor_5_13]; decide
      have factor_5_15 : (3 : ZMod 2043810367) ^ 52849 = 1847188383 := by
        calc
          (3 : ZMod 2043810367) ^ 52849 = (3 : ZMod 2043810367) ^ (26424 + 26424 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 26424 * (3 : ZMod 2043810367) ^ 26424) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1847188383 := by rw [factor_5_14]; decide
      have factor_5_16 : (3 : ZMod 2043810367) ^ 105699 = 15168752 := by
        calc
          (3 : ZMod 2043810367) ^ 105699 = (3 : ZMod 2043810367) ^ (52849 + 52849 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 52849 * (3 : ZMod 2043810367) ^ 52849) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 15168752 := by rw [factor_5_15]; decide
      have factor_5_17 : (3 : ZMod 2043810367) ^ 211399 = 685982666 := by
        calc
          (3 : ZMod 2043810367) ^ 211399 = (3 : ZMod 2043810367) ^ (105699 + 105699 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 105699 * (3 : ZMod 2043810367) ^ 105699) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 685982666 := by rw [factor_5_16]; decide
      have factor_5_18 : (3 : ZMod 2043810367) ^ 422799 = 1435627499 := by
        calc
          (3 : ZMod 2043810367) ^ 422799 = (3 : ZMod 2043810367) ^ (211399 + 211399 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = ((3 : ZMod 2043810367) ^ 211399 * (3 : ZMod 2043810367) ^ 211399) * (3 : ZMod 2043810367) := by rw [pow_succ, pow_add]
          _ = 1435627499 := by rw [factor_5_17]; decide
      have factor_5_19 : (3 : ZMod 2043810367) ^ 845598 = 142416282 := by
        calc
          (3 : ZMod 2043810367) ^ 845598 = (3 : ZMod 2043810367) ^ (422799 + 422799) :=
            congrArg (fun n : ℕ => (3 : ZMod 2043810367) ^ n) (by norm_num)
          _ = (3 : ZMod 2043810367) ^ 422799 * (3 : ZMod 2043810367) ^ 422799 := by rw [pow_add]
          _ = 142416282 := by rw [factor_5_18]; decide
      change (3 : ZMod 2043810367) ^ 845598 ≠ 1
      rw [factor_5_19]
      decide

#print axioms prime_lucas_2043810367

end TotientTailPeriodKiller
end Erdos249257
