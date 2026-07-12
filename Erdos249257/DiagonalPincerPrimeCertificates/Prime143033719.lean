import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_143033719 : Nat.Prime 143033719 := by
  apply lucas_primality 143033719 (6 : ZMod 143033719)
  ·
      have fermat_0 : (6 : ZMod 143033719) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 143033719) ^ 2 = 36 := by
        calc
          (6 : ZMod 143033719) ^ 2 = (6 : ZMod 143033719) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 1 * (6 : ZMod 143033719) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 143033719) ^ 4 = 1296 := by
        calc
          (6 : ZMod 143033719) ^ 4 = (6 : ZMod 143033719) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 2 * (6 : ZMod 143033719) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 143033719) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 143033719) ^ 8 = (6 : ZMod 143033719) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 4 * (6 : ZMod 143033719) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 143033719) ^ 17 = 49138276 := by
        calc
          (6 : ZMod 143033719) ^ 17 = (6 : ZMod 143033719) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 8 * (6 : ZMod 143033719) ^ 8) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 49138276 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 143033719) ^ 34 = 78598301 := by
        calc
          (6 : ZMod 143033719) ^ 34 = (6 : ZMod 143033719) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 17 * (6 : ZMod 143033719) ^ 17 := by rw [pow_add]
          _ = 78598301 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 143033719) ^ 68 = 85797266 := by
        calc
          (6 : ZMod 143033719) ^ 68 = (6 : ZMod 143033719) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 34 * (6 : ZMod 143033719) ^ 34 := by rw [pow_add]
          _ = 85797266 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 143033719) ^ 136 = 6766860 := by
        calc
          (6 : ZMod 143033719) ^ 136 = (6 : ZMod 143033719) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 68 * (6 : ZMod 143033719) ^ 68 := by rw [pow_add]
          _ = 6766860 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 143033719) ^ 272 = 8560097 := by
        calc
          (6 : ZMod 143033719) ^ 272 = (6 : ZMod 143033719) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 136 * (6 : ZMod 143033719) ^ 136 := by rw [pow_add]
          _ = 8560097 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 143033719) ^ 545 = 96749295 := by
        calc
          (6 : ZMod 143033719) ^ 545 = (6 : ZMod 143033719) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 272 * (6 : ZMod 143033719) ^ 272) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 96749295 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 143033719) ^ 1091 = 137210353 := by
        calc
          (6 : ZMod 143033719) ^ 1091 = (6 : ZMod 143033719) ^ (545 + 545 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 545 * (6 : ZMod 143033719) ^ 545) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 137210353 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 143033719) ^ 2182 = 13199684 := by
        calc
          (6 : ZMod 143033719) ^ 2182 = (6 : ZMod 143033719) ^ (1091 + 1091) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 1091 * (6 : ZMod 143033719) ^ 1091 := by rw [pow_add]
          _ = 13199684 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 143033719) ^ 4365 = 119312431 := by
        calc
          (6 : ZMod 143033719) ^ 4365 = (6 : ZMod 143033719) ^ (2182 + 2182 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 2182 * (6 : ZMod 143033719) ^ 2182) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 119312431 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 143033719) ^ 8730 = 133720217 := by
        calc
          (6 : ZMod 143033719) ^ 8730 = (6 : ZMod 143033719) ^ (4365 + 4365) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 4365 * (6 : ZMod 143033719) ^ 4365 := by rw [pow_add]
          _ = 133720217 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 143033719) ^ 17460 = 93987363 := by
        calc
          (6 : ZMod 143033719) ^ 17460 = (6 : ZMod 143033719) ^ (8730 + 8730) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 8730 * (6 : ZMod 143033719) ^ 8730 := by rw [pow_add]
          _ = 93987363 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 143033719) ^ 34920 = 88826323 := by
        calc
          (6 : ZMod 143033719) ^ 34920 = (6 : ZMod 143033719) ^ (17460 + 17460) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 17460 * (6 : ZMod 143033719) ^ 17460 := by rw [pow_add]
          _ = 88826323 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 143033719) ^ 69840 = 111114235 := by
        calc
          (6 : ZMod 143033719) ^ 69840 = (6 : ZMod 143033719) ^ (34920 + 34920) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 34920 * (6 : ZMod 143033719) ^ 34920 := by rw [pow_add]
          _ = 111114235 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 143033719) ^ 139681 = 62009594 := by
        calc
          (6 : ZMod 143033719) ^ 139681 = (6 : ZMod 143033719) ^ (69840 + 69840 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 69840 * (6 : ZMod 143033719) ^ 69840) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 62009594 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 143033719) ^ 279362 = 119829655 := by
        calc
          (6 : ZMod 143033719) ^ 279362 = (6 : ZMod 143033719) ^ (139681 + 139681) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 139681 * (6 : ZMod 143033719) ^ 139681 := by rw [pow_add]
          _ = 119829655 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 143033719) ^ 558725 = 67563899 := by
        calc
          (6 : ZMod 143033719) ^ 558725 = (6 : ZMod 143033719) ^ (279362 + 279362 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 279362 * (6 : ZMod 143033719) ^ 279362) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 67563899 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 143033719) ^ 1117450 = 70807116 := by
        calc
          (6 : ZMod 143033719) ^ 1117450 = (6 : ZMod 143033719) ^ (558725 + 558725) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 558725 * (6 : ZMod 143033719) ^ 558725 := by rw [pow_add]
          _ = 70807116 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 143033719) ^ 2234901 = 41015424 := by
        calc
          (6 : ZMod 143033719) ^ 2234901 = (6 : ZMod 143033719) ^ (1117450 + 1117450 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 1117450 * (6 : ZMod 143033719) ^ 1117450) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 41015424 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 143033719) ^ 4469803 = 141209961 := by
        calc
          (6 : ZMod 143033719) ^ 4469803 = (6 : ZMod 143033719) ^ (2234901 + 2234901 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 2234901 * (6 : ZMod 143033719) ^ 2234901) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 141209961 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 143033719) ^ 8939607 = 65879347 := by
        calc
          (6 : ZMod 143033719) ^ 8939607 = (6 : ZMod 143033719) ^ (4469803 + 4469803 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 4469803 * (6 : ZMod 143033719) ^ 4469803) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 65879347 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 143033719) ^ 17879214 = 62719162 := by
        calc
          (6 : ZMod 143033719) ^ 17879214 = (6 : ZMod 143033719) ^ (8939607 + 8939607) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 8939607 * (6 : ZMod 143033719) ^ 8939607 := by rw [pow_add]
          _ = 62719162 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 143033719) ^ 35758429 = 86656862 := by
        calc
          (6 : ZMod 143033719) ^ 35758429 = (6 : ZMod 143033719) ^ (17879214 + 17879214 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 17879214 * (6 : ZMod 143033719) ^ 17879214) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 86656862 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 143033719) ^ 71516859 = 143033718 := by
        calc
          (6 : ZMod 143033719) ^ 71516859 = (6 : ZMod 143033719) ^ (35758429 + 35758429 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 35758429 * (6 : ZMod 143033719) ^ 35758429) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 143033718 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 143033719) ^ 143033718 = 1 := by
        calc
          (6 : ZMod 143033719) ^ 143033718 = (6 : ZMod 143033719) ^ (71516859 + 71516859) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 71516859 * (6 : ZMod 143033719) ^ 71516859 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (73, 1), (326561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (73, 1), (326561, 1)] : List FactorBlock).map factorBlockValue).prod = 143033719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 143033719) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 143033719) ^ 2 = 36 := by
        calc
          (6 : ZMod 143033719) ^ 2 = (6 : ZMod 143033719) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 1 * (6 : ZMod 143033719) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 143033719) ^ 4 = 1296 := by
        calc
          (6 : ZMod 143033719) ^ 4 = (6 : ZMod 143033719) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 2 * (6 : ZMod 143033719) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 143033719) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 143033719) ^ 8 = (6 : ZMod 143033719) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 4 * (6 : ZMod 143033719) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 143033719) ^ 17 = 49138276 := by
        calc
          (6 : ZMod 143033719) ^ 17 = (6 : ZMod 143033719) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 8 * (6 : ZMod 143033719) ^ 8) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 49138276 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 143033719) ^ 34 = 78598301 := by
        calc
          (6 : ZMod 143033719) ^ 34 = (6 : ZMod 143033719) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 17 * (6 : ZMod 143033719) ^ 17 := by rw [pow_add]
          _ = 78598301 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 143033719) ^ 68 = 85797266 := by
        calc
          (6 : ZMod 143033719) ^ 68 = (6 : ZMod 143033719) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 34 * (6 : ZMod 143033719) ^ 34 := by rw [pow_add]
          _ = 85797266 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 143033719) ^ 136 = 6766860 := by
        calc
          (6 : ZMod 143033719) ^ 136 = (6 : ZMod 143033719) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 68 * (6 : ZMod 143033719) ^ 68 := by rw [pow_add]
          _ = 6766860 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 143033719) ^ 272 = 8560097 := by
        calc
          (6 : ZMod 143033719) ^ 272 = (6 : ZMod 143033719) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 136 * (6 : ZMod 143033719) ^ 136 := by rw [pow_add]
          _ = 8560097 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 143033719) ^ 545 = 96749295 := by
        calc
          (6 : ZMod 143033719) ^ 545 = (6 : ZMod 143033719) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 272 * (6 : ZMod 143033719) ^ 272) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 96749295 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 143033719) ^ 1091 = 137210353 := by
        calc
          (6 : ZMod 143033719) ^ 1091 = (6 : ZMod 143033719) ^ (545 + 545 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 545 * (6 : ZMod 143033719) ^ 545) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 137210353 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 143033719) ^ 2182 = 13199684 := by
        calc
          (6 : ZMod 143033719) ^ 2182 = (6 : ZMod 143033719) ^ (1091 + 1091) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 1091 * (6 : ZMod 143033719) ^ 1091 := by rw [pow_add]
          _ = 13199684 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 143033719) ^ 4365 = 119312431 := by
        calc
          (6 : ZMod 143033719) ^ 4365 = (6 : ZMod 143033719) ^ (2182 + 2182 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 2182 * (6 : ZMod 143033719) ^ 2182) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 119312431 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 143033719) ^ 8730 = 133720217 := by
        calc
          (6 : ZMod 143033719) ^ 8730 = (6 : ZMod 143033719) ^ (4365 + 4365) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 4365 * (6 : ZMod 143033719) ^ 4365 := by rw [pow_add]
          _ = 133720217 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 143033719) ^ 17460 = 93987363 := by
        calc
          (6 : ZMod 143033719) ^ 17460 = (6 : ZMod 143033719) ^ (8730 + 8730) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 8730 * (6 : ZMod 143033719) ^ 8730 := by rw [pow_add]
          _ = 93987363 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 143033719) ^ 34920 = 88826323 := by
        calc
          (6 : ZMod 143033719) ^ 34920 = (6 : ZMod 143033719) ^ (17460 + 17460) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 17460 * (6 : ZMod 143033719) ^ 17460 := by rw [pow_add]
          _ = 88826323 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 143033719) ^ 69840 = 111114235 := by
        calc
          (6 : ZMod 143033719) ^ 69840 = (6 : ZMod 143033719) ^ (34920 + 34920) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 34920 * (6 : ZMod 143033719) ^ 34920 := by rw [pow_add]
          _ = 111114235 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 143033719) ^ 139681 = 62009594 := by
        calc
          (6 : ZMod 143033719) ^ 139681 = (6 : ZMod 143033719) ^ (69840 + 69840 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 69840 * (6 : ZMod 143033719) ^ 69840) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 62009594 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 143033719) ^ 279362 = 119829655 := by
        calc
          (6 : ZMod 143033719) ^ 279362 = (6 : ZMod 143033719) ^ (139681 + 139681) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 139681 * (6 : ZMod 143033719) ^ 139681 := by rw [pow_add]
          _ = 119829655 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 143033719) ^ 558725 = 67563899 := by
        calc
          (6 : ZMod 143033719) ^ 558725 = (6 : ZMod 143033719) ^ (279362 + 279362 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 279362 * (6 : ZMod 143033719) ^ 279362) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 67563899 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 143033719) ^ 1117450 = 70807116 := by
        calc
          (6 : ZMod 143033719) ^ 1117450 = (6 : ZMod 143033719) ^ (558725 + 558725) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 558725 * (6 : ZMod 143033719) ^ 558725 := by rw [pow_add]
          _ = 70807116 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 143033719) ^ 2234901 = 41015424 := by
        calc
          (6 : ZMod 143033719) ^ 2234901 = (6 : ZMod 143033719) ^ (1117450 + 1117450 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 1117450 * (6 : ZMod 143033719) ^ 1117450) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 41015424 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 143033719) ^ 4469803 = 141209961 := by
        calc
          (6 : ZMod 143033719) ^ 4469803 = (6 : ZMod 143033719) ^ (2234901 + 2234901 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 2234901 * (6 : ZMod 143033719) ^ 2234901) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 141209961 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 143033719) ^ 8939607 = 65879347 := by
        calc
          (6 : ZMod 143033719) ^ 8939607 = (6 : ZMod 143033719) ^ (4469803 + 4469803 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 4469803 * (6 : ZMod 143033719) ^ 4469803) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 65879347 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 143033719) ^ 17879214 = 62719162 := by
        calc
          (6 : ZMod 143033719) ^ 17879214 = (6 : ZMod 143033719) ^ (8939607 + 8939607) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 8939607 * (6 : ZMod 143033719) ^ 8939607 := by rw [pow_add]
          _ = 62719162 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 143033719) ^ 35758429 = 86656862 := by
        calc
          (6 : ZMod 143033719) ^ 35758429 = (6 : ZMod 143033719) ^ (17879214 + 17879214 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 17879214 * (6 : ZMod 143033719) ^ 17879214) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 86656862 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 143033719) ^ 71516859 = 143033718 := by
        calc
          (6 : ZMod 143033719) ^ 71516859 = (6 : ZMod 143033719) ^ (35758429 + 35758429 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 35758429 * (6 : ZMod 143033719) ^ 35758429) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 143033718 := by rw [factor_0_25]; decide
      change (6 : ZMod 143033719) ^ 71516859 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (6 : ZMod 143033719) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 143033719) ^ 2 = 36 := by
        calc
          (6 : ZMod 143033719) ^ 2 = (6 : ZMod 143033719) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 1 * (6 : ZMod 143033719) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 143033719) ^ 5 = 7776 := by
        calc
          (6 : ZMod 143033719) ^ 5 = (6 : ZMod 143033719) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 2 * (6 : ZMod 143033719) ^ 2) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 143033719) ^ 11 = 76729618 := by
        calc
          (6 : ZMod 143033719) ^ 11 = (6 : ZMod 143033719) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 5 * (6 : ZMod 143033719) ^ 5) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 76729618 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 143033719) ^ 22 = 56170727 := by
        calc
          (6 : ZMod 143033719) ^ 22 = (6 : ZMod 143033719) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 11 * (6 : ZMod 143033719) ^ 11 := by rw [pow_add]
          _ = 56170727 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 143033719) ^ 45 = 95514585 := by
        calc
          (6 : ZMod 143033719) ^ 45 = (6 : ZMod 143033719) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 22 * (6 : ZMod 143033719) ^ 22) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 95514585 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 143033719) ^ 90 = 66504559 := by
        calc
          (6 : ZMod 143033719) ^ 90 = (6 : ZMod 143033719) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 45 * (6 : ZMod 143033719) ^ 45 := by rw [pow_add]
          _ = 66504559 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 143033719) ^ 181 = 63888131 := by
        calc
          (6 : ZMod 143033719) ^ 181 = (6 : ZMod 143033719) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 90 * (6 : ZMod 143033719) ^ 90) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 63888131 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 143033719) ^ 363 = 134257970 := by
        calc
          (6 : ZMod 143033719) ^ 363 = (6 : ZMod 143033719) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 181 * (6 : ZMod 143033719) ^ 181) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 134257970 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 143033719) ^ 727 = 35970391 := by
        calc
          (6 : ZMod 143033719) ^ 727 = (6 : ZMod 143033719) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 363 * (6 : ZMod 143033719) ^ 363) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 35970391 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 143033719) ^ 1455 = 506339 := by
        calc
          (6 : ZMod 143033719) ^ 1455 = (6 : ZMod 143033719) ^ (727 + 727 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 727 * (6 : ZMod 143033719) ^ 727) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 506339 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 143033719) ^ 2910 = 62758473 := by
        calc
          (6 : ZMod 143033719) ^ 2910 = (6 : ZMod 143033719) ^ (1455 + 1455) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 1455 * (6 : ZMod 143033719) ^ 1455 := by rw [pow_add]
          _ = 62758473 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 143033719) ^ 5820 = 100274674 := by
        calc
          (6 : ZMod 143033719) ^ 5820 = (6 : ZMod 143033719) ^ (2910 + 2910) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 2910 * (6 : ZMod 143033719) ^ 2910 := by rw [pow_add]
          _ = 100274674 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 143033719) ^ 11640 = 121474856 := by
        calc
          (6 : ZMod 143033719) ^ 11640 = (6 : ZMod 143033719) ^ (5820 + 5820) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 5820 * (6 : ZMod 143033719) ^ 5820 := by rw [pow_add]
          _ = 121474856 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 143033719) ^ 23280 = 79805244 := by
        calc
          (6 : ZMod 143033719) ^ 23280 = (6 : ZMod 143033719) ^ (11640 + 11640) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 11640 * (6 : ZMod 143033719) ^ 11640 := by rw [pow_add]
          _ = 79805244 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 143033719) ^ 46560 = 117580917 := by
        calc
          (6 : ZMod 143033719) ^ 46560 = (6 : ZMod 143033719) ^ (23280 + 23280) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 23280 * (6 : ZMod 143033719) ^ 23280 := by rw [pow_add]
          _ = 117580917 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 143033719) ^ 93120 = 74611281 := by
        calc
          (6 : ZMod 143033719) ^ 93120 = (6 : ZMod 143033719) ^ (46560 + 46560) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 46560 * (6 : ZMod 143033719) ^ 46560 := by rw [pow_add]
          _ = 74611281 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 143033719) ^ 186241 = 98056665 := by
        calc
          (6 : ZMod 143033719) ^ 186241 = (6 : ZMod 143033719) ^ (93120 + 93120 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 93120 * (6 : ZMod 143033719) ^ 93120) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 98056665 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 143033719) ^ 372483 = 64791334 := by
        calc
          (6 : ZMod 143033719) ^ 372483 = (6 : ZMod 143033719) ^ (186241 + 186241 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 186241 * (6 : ZMod 143033719) ^ 186241) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 64791334 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 143033719) ^ 744967 = 47649029 := by
        calc
          (6 : ZMod 143033719) ^ 744967 = (6 : ZMod 143033719) ^ (372483 + 372483 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 372483 * (6 : ZMod 143033719) ^ 372483) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 47649029 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 143033719) ^ 1489934 = 102839150 := by
        calc
          (6 : ZMod 143033719) ^ 1489934 = (6 : ZMod 143033719) ^ (744967 + 744967) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 744967 * (6 : ZMod 143033719) ^ 744967 := by rw [pow_add]
          _ = 102839150 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 143033719) ^ 2979869 = 133904579 := by
        calc
          (6 : ZMod 143033719) ^ 2979869 = (6 : ZMod 143033719) ^ (1489934 + 1489934 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 1489934 * (6 : ZMod 143033719) ^ 1489934) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 133904579 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 143033719) ^ 5959738 = 26157308 := by
        calc
          (6 : ZMod 143033719) ^ 5959738 = (6 : ZMod 143033719) ^ (2979869 + 2979869) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 2979869 * (6 : ZMod 143033719) ^ 2979869 := by rw [pow_add]
          _ = 26157308 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 143033719) ^ 11919476 = 106295984 := by
        calc
          (6 : ZMod 143033719) ^ 11919476 = (6 : ZMod 143033719) ^ (5959738 + 5959738) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 5959738 * (6 : ZMod 143033719) ^ 5959738 := by rw [pow_add]
          _ = 106295984 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 143033719) ^ 23838953 = 39758340 := by
        calc
          (6 : ZMod 143033719) ^ 23838953 = (6 : ZMod 143033719) ^ (11919476 + 11919476 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 11919476 * (6 : ZMod 143033719) ^ 11919476) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 39758340 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 143033719) ^ 47677906 = 39758339 := by
        calc
          (6 : ZMod 143033719) ^ 47677906 = (6 : ZMod 143033719) ^ (23838953 + 23838953) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 23838953 * (6 : ZMod 143033719) ^ 23838953 := by rw [pow_add]
          _ = 39758339 := by rw [factor_1_24]; decide
      change (6 : ZMod 143033719) ^ 47677906 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (6 : ZMod 143033719) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 143033719) ^ 3 = 216 := by
        calc
          (6 : ZMod 143033719) ^ 3 = (6 : ZMod 143033719) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 1 * (6 : ZMod 143033719) ^ 1) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 143033719) ^ 7 = 279936 := by
        calc
          (6 : ZMod 143033719) ^ 7 = (6 : ZMod 143033719) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 3 * (6 : ZMod 143033719) ^ 3) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 143033719) ^ 14 = 124719803 := by
        calc
          (6 : ZMod 143033719) ^ 14 = (6 : ZMod 143033719) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 7 * (6 : ZMod 143033719) ^ 7 := by rw [pow_add]
          _ = 124719803 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 143033719) ^ 29 = 82802645 := by
        calc
          (6 : ZMod 143033719) ^ 29 = (6 : ZMod 143033719) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 14 * (6 : ZMod 143033719) ^ 14) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 82802645 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 143033719) ^ 59 = 84653573 := by
        calc
          (6 : ZMod 143033719) ^ 59 = (6 : ZMod 143033719) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 29 * (6 : ZMod 143033719) ^ 29) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 84653573 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 143033719) ^ 119 = 120846321 := by
        calc
          (6 : ZMod 143033719) ^ 119 = (6 : ZMod 143033719) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 59 * (6 : ZMod 143033719) ^ 59) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 120846321 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 143033719) ^ 239 = 7878046 := by
        calc
          (6 : ZMod 143033719) ^ 239 = (6 : ZMod 143033719) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 119 * (6 : ZMod 143033719) ^ 119) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 7878046 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 143033719) ^ 478 = 133834264 := by
        calc
          (6 : ZMod 143033719) ^ 478 = (6 : ZMod 143033719) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 239 * (6 : ZMod 143033719) ^ 239 := by rw [pow_add]
          _ = 133834264 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 143033719) ^ 956 = 67506543 := by
        calc
          (6 : ZMod 143033719) ^ 956 = (6 : ZMod 143033719) ^ (478 + 478) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 478 * (6 : ZMod 143033719) ^ 478 := by rw [pow_add]
          _ = 67506543 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 143033719) ^ 1913 = 63012890 := by
        calc
          (6 : ZMod 143033719) ^ 1913 = (6 : ZMod 143033719) ^ (956 + 956 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 956 * (6 : ZMod 143033719) ^ 956) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 63012890 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 143033719) ^ 3826 = 113790117 := by
        calc
          (6 : ZMod 143033719) ^ 3826 = (6 : ZMod 143033719) ^ (1913 + 1913) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 1913 * (6 : ZMod 143033719) ^ 1913 := by rw [pow_add]
          _ = 113790117 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 143033719) ^ 7653 = 131868189 := by
        calc
          (6 : ZMod 143033719) ^ 7653 = (6 : ZMod 143033719) ^ (3826 + 3826 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 3826 * (6 : ZMod 143033719) ^ 3826) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 131868189 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 143033719) ^ 15307 = 74989116 := by
        calc
          (6 : ZMod 143033719) ^ 15307 = (6 : ZMod 143033719) ^ (7653 + 7653 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 7653 * (6 : ZMod 143033719) ^ 7653) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 74989116 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 143033719) ^ 30615 = 16309644 := by
        calc
          (6 : ZMod 143033719) ^ 30615 = (6 : ZMod 143033719) ^ (15307 + 15307 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 15307 * (6 : ZMod 143033719) ^ 15307) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 16309644 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 143033719) ^ 61230 = 103103428 := by
        calc
          (6 : ZMod 143033719) ^ 61230 = (6 : ZMod 143033719) ^ (30615 + 30615) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 30615 * (6 : ZMod 143033719) ^ 30615 := by rw [pow_add]
          _ = 103103428 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 143033719) ^ 122460 = 92300939 := by
        calc
          (6 : ZMod 143033719) ^ 122460 = (6 : ZMod 143033719) ^ (61230 + 61230) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 61230 * (6 : ZMod 143033719) ^ 61230 := by rw [pow_add]
          _ = 92300939 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 143033719) ^ 244920 = 2230503 := by
        calc
          (6 : ZMod 143033719) ^ 244920 = (6 : ZMod 143033719) ^ (122460 + 122460) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 122460 * (6 : ZMod 143033719) ^ 122460 := by rw [pow_add]
          _ = 2230503 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 143033719) ^ 489841 = 10710192 := by
        calc
          (6 : ZMod 143033719) ^ 489841 = (6 : ZMod 143033719) ^ (244920 + 244920 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 244920 * (6 : ZMod 143033719) ^ 244920) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 10710192 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 143033719) ^ 979683 = 56078141 := by
        calc
          (6 : ZMod 143033719) ^ 979683 = (6 : ZMod 143033719) ^ (489841 + 489841 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 489841 * (6 : ZMod 143033719) ^ 489841) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 56078141 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 143033719) ^ 1959366 = 100732130 := by
        calc
          (6 : ZMod 143033719) ^ 1959366 = (6 : ZMod 143033719) ^ (979683 + 979683) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 979683 * (6 : ZMod 143033719) ^ 979683 := by rw [pow_add]
          _ = 100732130 := by rw [factor_2_19]; decide
      change (6 : ZMod 143033719) ^ 1959366 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (6 : ZMod 143033719) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 143033719) ^ 3 = 216 := by
        calc
          (6 : ZMod 143033719) ^ 3 = (6 : ZMod 143033719) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 1 * (6 : ZMod 143033719) ^ 1) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 143033719) ^ 6 = 46656 := by
        calc
          (6 : ZMod 143033719) ^ 6 = (6 : ZMod 143033719) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 3 * (6 : ZMod 143033719) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 143033719) ^ 13 = 44625587 := by
        calc
          (6 : ZMod 143033719) ^ 13 = (6 : ZMod 143033719) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 6 * (6 : ZMod 143033719) ^ 6) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 44625587 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 143033719) ^ 27 = 101629045 := by
        calc
          (6 : ZMod 143033719) ^ 27 = (6 : ZMod 143033719) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 13 * (6 : ZMod 143033719) ^ 13) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 101629045 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 143033719) ^ 54 = 84127810 := by
        calc
          (6 : ZMod 143033719) ^ 54 = (6 : ZMod 143033719) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 27 * (6 : ZMod 143033719) ^ 27 := by rw [pow_add]
          _ = 84127810 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 143033719) ^ 109 = 91078150 := by
        calc
          (6 : ZMod 143033719) ^ 109 = (6 : ZMod 143033719) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 54 * (6 : ZMod 143033719) ^ 54) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 91078150 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 143033719) ^ 219 = 40851773 := by
        calc
          (6 : ZMod 143033719) ^ 219 = (6 : ZMod 143033719) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = ((6 : ZMod 143033719) ^ 109 * (6 : ZMod 143033719) ^ 109) * (6 : ZMod 143033719) := by rw [pow_succ, pow_add]
          _ = 40851773 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 143033719) ^ 438 = 128786898 := by
        calc
          (6 : ZMod 143033719) ^ 438 = (6 : ZMod 143033719) ^ (219 + 219) :=
            congrArg (fun n : ℕ => (6 : ZMod 143033719) ^ n) (by norm_num)
          _ = (6 : ZMod 143033719) ^ 219 * (6 : ZMod 143033719) ^ 219 := by rw [pow_add]
          _ = 128786898 := by rw [factor_3_7]; decide
      change (6 : ZMod 143033719) ^ 438 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_143033719

end TotientTailPeriodKiller
end Erdos249257
