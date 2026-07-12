import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2064151171 : Nat.Prime 2064151171 := by
  apply lucas_primality 2064151171 (2 : ZMod 2064151171)
  ·
      have fermat_0 : (2 : ZMod 2064151171) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 2064151171) ^ 3 = 8 := by
        calc
          (2 : ZMod 2064151171) ^ 3 = (2 : ZMod 2064151171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1 * (2 : ZMod 2064151171) ^ 1) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 2064151171) ^ 7 = 128 := by
        calc
          (2 : ZMod 2064151171) ^ 7 = (2 : ZMod 2064151171) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 3 * (2 : ZMod 2064151171) ^ 3) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 2064151171) ^ 15 = 32768 := by
        calc
          (2 : ZMod 2064151171) ^ 15 = (2 : ZMod 2064151171) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 7 * (2 : ZMod 2064151171) ^ 7) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 2064151171) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 2064151171) ^ 30 = (2 : ZMod 2064151171) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 15 * (2 : ZMod 2064151171) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 2064151171) ^ 61 = 1925790830 := by
        calc
          (2 : ZMod 2064151171) ^ 61 = (2 : ZMod 2064151171) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 30 * (2 : ZMod 2064151171) ^ 30) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1925790830 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 2064151171) ^ 123 = 1909082687 := by
        calc
          (2 : ZMod 2064151171) ^ 123 = (2 : ZMod 2064151171) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 61 * (2 : ZMod 2064151171) ^ 61) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1909082687 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 2064151171) ^ 246 = 614447622 := by
        calc
          (2 : ZMod 2064151171) ^ 246 = (2 : ZMod 2064151171) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 123 * (2 : ZMod 2064151171) ^ 123 := by rw [pow_add]
          _ = 614447622 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 2064151171) ^ 492 = 464539535 := by
        calc
          (2 : ZMod 2064151171) ^ 492 = (2 : ZMod 2064151171) ^ (246 + 246) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 246 * (2 : ZMod 2064151171) ^ 246 := by rw [pow_add]
          _ = 464539535 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 2064151171) ^ 984 = 232203772 := by
        calc
          (2 : ZMod 2064151171) ^ 984 = (2 : ZMod 2064151171) ^ (492 + 492) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 492 * (2 : ZMod 2064151171) ^ 492 := by rw [pow_add]
          _ = 232203772 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 2064151171) ^ 1968 = 1087577599 := by
        calc
          (2 : ZMod 2064151171) ^ 1968 = (2 : ZMod 2064151171) ^ (984 + 984) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 984 * (2 : ZMod 2064151171) ^ 984 := by rw [pow_add]
          _ = 1087577599 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 2064151171) ^ 3937 = 1727658094 := by
        calc
          (2 : ZMod 2064151171) ^ 3937 = (2 : ZMod 2064151171) ^ (1968 + 1968 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1968 * (2 : ZMod 2064151171) ^ 1968) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1727658094 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 2064151171) ^ 7874 = 583879748 := by
        calc
          (2 : ZMod 2064151171) ^ 7874 = (2 : ZMod 2064151171) ^ (3937 + 3937) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 3937 * (2 : ZMod 2064151171) ^ 3937 := by rw [pow_add]
          _ = 583879748 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 2064151171) ^ 15748 = 1816484434 := by
        calc
          (2 : ZMod 2064151171) ^ 15748 = (2 : ZMod 2064151171) ^ (7874 + 7874) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 7874 * (2 : ZMod 2064151171) ^ 7874 := by rw [pow_add]
          _ = 1816484434 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 2064151171) ^ 31496 = 1022510129 := by
        calc
          (2 : ZMod 2064151171) ^ 31496 = (2 : ZMod 2064151171) ^ (15748 + 15748) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 15748 * (2 : ZMod 2064151171) ^ 15748 := by rw [pow_add]
          _ = 1022510129 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 2064151171) ^ 62992 = 845134268 := by
        calc
          (2 : ZMod 2064151171) ^ 62992 = (2 : ZMod 2064151171) ^ (31496 + 31496) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 31496 * (2 : ZMod 2064151171) ^ 31496 := by rw [pow_add]
          _ = 845134268 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 2064151171) ^ 125985 = 8128261 := by
        calc
          (2 : ZMod 2064151171) ^ 125985 = (2 : ZMod 2064151171) ^ (62992 + 62992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 62992 * (2 : ZMod 2064151171) ^ 62992) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 8128261 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 2064151171) ^ 251971 = 616556677 := by
        calc
          (2 : ZMod 2064151171) ^ 251971 = (2 : ZMod 2064151171) ^ (125985 + 125985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 125985 * (2 : ZMod 2064151171) ^ 125985) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 616556677 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 2064151171) ^ 503943 = 1903955003 := by
        calc
          (2 : ZMod 2064151171) ^ 503943 = (2 : ZMod 2064151171) ^ (251971 + 251971 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 251971 * (2 : ZMod 2064151171) ^ 251971) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1903955003 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 2064151171) ^ 1007886 = 981983862 := by
        calc
          (2 : ZMod 2064151171) ^ 1007886 = (2 : ZMod 2064151171) ^ (503943 + 503943) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 503943 * (2 : ZMod 2064151171) ^ 503943 := by rw [pow_add]
          _ = 981983862 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 2064151171) ^ 2015772 = 1179921816 := by
        calc
          (2 : ZMod 2064151171) ^ 2015772 = (2 : ZMod 2064151171) ^ (1007886 + 1007886) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1007886 * (2 : ZMod 2064151171) ^ 1007886 := by rw [pow_add]
          _ = 1179921816 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 2064151171) ^ 4031545 = 2029432263 := by
        calc
          (2 : ZMod 2064151171) ^ 4031545 = (2 : ZMod 2064151171) ^ (2015772 + 2015772 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2015772 * (2 : ZMod 2064151171) ^ 2015772) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 2029432263 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 2064151171) ^ 8063090 = 213383594 := by
        calc
          (2 : ZMod 2064151171) ^ 8063090 = (2 : ZMod 2064151171) ^ (4031545 + 4031545) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 4031545 * (2 : ZMod 2064151171) ^ 4031545 := by rw [pow_add]
          _ = 213383594 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 2064151171) ^ 16126181 = 1399563328 := by
        calc
          (2 : ZMod 2064151171) ^ 16126181 = (2 : ZMod 2064151171) ^ (8063090 + 8063090 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 8063090 * (2 : ZMod 2064151171) ^ 8063090) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1399563328 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 2064151171) ^ 32252362 = 358073616 := by
        calc
          (2 : ZMod 2064151171) ^ 32252362 = (2 : ZMod 2064151171) ^ (16126181 + 16126181) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 16126181 * (2 : ZMod 2064151171) ^ 16126181 := by rw [pow_add]
          _ = 358073616 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 2064151171) ^ 64504724 = 1480886835 := by
        calc
          (2 : ZMod 2064151171) ^ 64504724 = (2 : ZMod 2064151171) ^ (32252362 + 32252362) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 32252362 * (2 : ZMod 2064151171) ^ 32252362 := by rw [pow_add]
          _ = 1480886835 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 2064151171) ^ 129009448 = 345190551 := by
        calc
          (2 : ZMod 2064151171) ^ 129009448 = (2 : ZMod 2064151171) ^ (64504724 + 64504724) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 64504724 * (2 : ZMod 2064151171) ^ 64504724 := by rw [pow_add]
          _ = 345190551 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 2064151171) ^ 258018896 = 817485819 := by
        calc
          (2 : ZMod 2064151171) ^ 258018896 = (2 : ZMod 2064151171) ^ (129009448 + 129009448) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 129009448 * (2 : ZMod 2064151171) ^ 129009448 := by rw [pow_add]
          _ = 817485819 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 2064151171) ^ 516037792 = 1796689950 := by
        calc
          (2 : ZMod 2064151171) ^ 516037792 = (2 : ZMod 2064151171) ^ (258018896 + 258018896) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 258018896 * (2 : ZMod 2064151171) ^ 258018896 := by rw [pow_add]
          _ = 1796689950 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 2064151171) ^ 1032075585 = 2064151170 := by
        calc
          (2 : ZMod 2064151171) ^ 1032075585 = (2 : ZMod 2064151171) ^ (516037792 + 516037792 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 516037792 * (2 : ZMod 2064151171) ^ 516037792) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 2064151170 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 2064151171) ^ 2064151170 = 1 := by
        calc
          (2 : ZMod 2064151171) ^ 2064151170 = (2 : ZMod 2064151171) ^ (1032075585 + 1032075585) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1032075585 * (2 : ZMod 2064151171) ^ 1032075585 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (47, 1), (487979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (47, 1), (487979, 1)] : List FactorBlock).map factorBlockValue).prod = 2064151171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 2064151171) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 2064151171) ^ 3 = 8 := by
        calc
          (2 : ZMod 2064151171) ^ 3 = (2 : ZMod 2064151171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1 * (2 : ZMod 2064151171) ^ 1) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 2064151171) ^ 7 = 128 := by
        calc
          (2 : ZMod 2064151171) ^ 7 = (2 : ZMod 2064151171) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 3 * (2 : ZMod 2064151171) ^ 3) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 2064151171) ^ 15 = 32768 := by
        calc
          (2 : ZMod 2064151171) ^ 15 = (2 : ZMod 2064151171) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 7 * (2 : ZMod 2064151171) ^ 7) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 2064151171) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 2064151171) ^ 30 = (2 : ZMod 2064151171) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 15 * (2 : ZMod 2064151171) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 2064151171) ^ 61 = 1925790830 := by
        calc
          (2 : ZMod 2064151171) ^ 61 = (2 : ZMod 2064151171) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 30 * (2 : ZMod 2064151171) ^ 30) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1925790830 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 2064151171) ^ 123 = 1909082687 := by
        calc
          (2 : ZMod 2064151171) ^ 123 = (2 : ZMod 2064151171) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 61 * (2 : ZMod 2064151171) ^ 61) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1909082687 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 2064151171) ^ 246 = 614447622 := by
        calc
          (2 : ZMod 2064151171) ^ 246 = (2 : ZMod 2064151171) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 123 * (2 : ZMod 2064151171) ^ 123 := by rw [pow_add]
          _ = 614447622 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 2064151171) ^ 492 = 464539535 := by
        calc
          (2 : ZMod 2064151171) ^ 492 = (2 : ZMod 2064151171) ^ (246 + 246) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 246 * (2 : ZMod 2064151171) ^ 246 := by rw [pow_add]
          _ = 464539535 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 2064151171) ^ 984 = 232203772 := by
        calc
          (2 : ZMod 2064151171) ^ 984 = (2 : ZMod 2064151171) ^ (492 + 492) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 492 * (2 : ZMod 2064151171) ^ 492 := by rw [pow_add]
          _ = 232203772 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 2064151171) ^ 1968 = 1087577599 := by
        calc
          (2 : ZMod 2064151171) ^ 1968 = (2 : ZMod 2064151171) ^ (984 + 984) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 984 * (2 : ZMod 2064151171) ^ 984 := by rw [pow_add]
          _ = 1087577599 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 2064151171) ^ 3937 = 1727658094 := by
        calc
          (2 : ZMod 2064151171) ^ 3937 = (2 : ZMod 2064151171) ^ (1968 + 1968 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1968 * (2 : ZMod 2064151171) ^ 1968) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1727658094 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 2064151171) ^ 7874 = 583879748 := by
        calc
          (2 : ZMod 2064151171) ^ 7874 = (2 : ZMod 2064151171) ^ (3937 + 3937) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 3937 * (2 : ZMod 2064151171) ^ 3937 := by rw [pow_add]
          _ = 583879748 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 2064151171) ^ 15748 = 1816484434 := by
        calc
          (2 : ZMod 2064151171) ^ 15748 = (2 : ZMod 2064151171) ^ (7874 + 7874) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 7874 * (2 : ZMod 2064151171) ^ 7874 := by rw [pow_add]
          _ = 1816484434 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 2064151171) ^ 31496 = 1022510129 := by
        calc
          (2 : ZMod 2064151171) ^ 31496 = (2 : ZMod 2064151171) ^ (15748 + 15748) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 15748 * (2 : ZMod 2064151171) ^ 15748 := by rw [pow_add]
          _ = 1022510129 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 2064151171) ^ 62992 = 845134268 := by
        calc
          (2 : ZMod 2064151171) ^ 62992 = (2 : ZMod 2064151171) ^ (31496 + 31496) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 31496 * (2 : ZMod 2064151171) ^ 31496 := by rw [pow_add]
          _ = 845134268 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 2064151171) ^ 125985 = 8128261 := by
        calc
          (2 : ZMod 2064151171) ^ 125985 = (2 : ZMod 2064151171) ^ (62992 + 62992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 62992 * (2 : ZMod 2064151171) ^ 62992) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 8128261 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 2064151171) ^ 251971 = 616556677 := by
        calc
          (2 : ZMod 2064151171) ^ 251971 = (2 : ZMod 2064151171) ^ (125985 + 125985 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 125985 * (2 : ZMod 2064151171) ^ 125985) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 616556677 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 2064151171) ^ 503943 = 1903955003 := by
        calc
          (2 : ZMod 2064151171) ^ 503943 = (2 : ZMod 2064151171) ^ (251971 + 251971 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 251971 * (2 : ZMod 2064151171) ^ 251971) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1903955003 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 2064151171) ^ 1007886 = 981983862 := by
        calc
          (2 : ZMod 2064151171) ^ 1007886 = (2 : ZMod 2064151171) ^ (503943 + 503943) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 503943 * (2 : ZMod 2064151171) ^ 503943 := by rw [pow_add]
          _ = 981983862 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 2064151171) ^ 2015772 = 1179921816 := by
        calc
          (2 : ZMod 2064151171) ^ 2015772 = (2 : ZMod 2064151171) ^ (1007886 + 1007886) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1007886 * (2 : ZMod 2064151171) ^ 1007886 := by rw [pow_add]
          _ = 1179921816 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 2064151171) ^ 4031545 = 2029432263 := by
        calc
          (2 : ZMod 2064151171) ^ 4031545 = (2 : ZMod 2064151171) ^ (2015772 + 2015772 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2015772 * (2 : ZMod 2064151171) ^ 2015772) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 2029432263 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 2064151171) ^ 8063090 = 213383594 := by
        calc
          (2 : ZMod 2064151171) ^ 8063090 = (2 : ZMod 2064151171) ^ (4031545 + 4031545) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 4031545 * (2 : ZMod 2064151171) ^ 4031545 := by rw [pow_add]
          _ = 213383594 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 2064151171) ^ 16126181 = 1399563328 := by
        calc
          (2 : ZMod 2064151171) ^ 16126181 = (2 : ZMod 2064151171) ^ (8063090 + 8063090 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 8063090 * (2 : ZMod 2064151171) ^ 8063090) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1399563328 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 2064151171) ^ 32252362 = 358073616 := by
        calc
          (2 : ZMod 2064151171) ^ 32252362 = (2 : ZMod 2064151171) ^ (16126181 + 16126181) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 16126181 * (2 : ZMod 2064151171) ^ 16126181 := by rw [pow_add]
          _ = 358073616 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 2064151171) ^ 64504724 = 1480886835 := by
        calc
          (2 : ZMod 2064151171) ^ 64504724 = (2 : ZMod 2064151171) ^ (32252362 + 32252362) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 32252362 * (2 : ZMod 2064151171) ^ 32252362 := by rw [pow_add]
          _ = 1480886835 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 2064151171) ^ 129009448 = 345190551 := by
        calc
          (2 : ZMod 2064151171) ^ 129009448 = (2 : ZMod 2064151171) ^ (64504724 + 64504724) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 64504724 * (2 : ZMod 2064151171) ^ 64504724 := by rw [pow_add]
          _ = 345190551 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 2064151171) ^ 258018896 = 817485819 := by
        calc
          (2 : ZMod 2064151171) ^ 258018896 = (2 : ZMod 2064151171) ^ (129009448 + 129009448) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 129009448 * (2 : ZMod 2064151171) ^ 129009448 := by rw [pow_add]
          _ = 817485819 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 2064151171) ^ 516037792 = 1796689950 := by
        calc
          (2 : ZMod 2064151171) ^ 516037792 = (2 : ZMod 2064151171) ^ (258018896 + 258018896) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 258018896 * (2 : ZMod 2064151171) ^ 258018896 := by rw [pow_add]
          _ = 1796689950 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 2064151171) ^ 1032075585 = 2064151170 := by
        calc
          (2 : ZMod 2064151171) ^ 1032075585 = (2 : ZMod 2064151171) ^ (516037792 + 516037792 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 516037792 * (2 : ZMod 2064151171) ^ 516037792) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 2064151170 := by rw [factor_0_28]; decide
      change (2 : ZMod 2064151171) ^ 1032075585 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (2 : ZMod 2064151171) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 2064151171) ^ 2 = 4 := by
        calc
          (2 : ZMod 2064151171) ^ 2 = (2 : ZMod 2064151171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1 * (2 : ZMod 2064151171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 2064151171) ^ 5 = 32 := by
        calc
          (2 : ZMod 2064151171) ^ 5 = (2 : ZMod 2064151171) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2 * (2 : ZMod 2064151171) ^ 2) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 2064151171) ^ 10 = 1024 := by
        calc
          (2 : ZMod 2064151171) ^ 10 = (2 : ZMod 2064151171) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 5 * (2 : ZMod 2064151171) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 2064151171) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 2064151171) ^ 20 = (2 : ZMod 2064151171) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 10 * (2 : ZMod 2064151171) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 2064151171) ^ 41 = 702258437 := by
        calc
          (2 : ZMod 2064151171) ^ 41 = (2 : ZMod 2064151171) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 20 * (2 : ZMod 2064151171) ^ 20) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 702258437 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 2064151171) ^ 82 = 1256712151 := by
        calc
          (2 : ZMod 2064151171) ^ 82 = (2 : ZMod 2064151171) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 41 * (2 : ZMod 2064151171) ^ 41 := by rw [pow_add]
          _ = 1256712151 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 2064151171) ^ 164 = 1722844091 := by
        calc
          (2 : ZMod 2064151171) ^ 164 = (2 : ZMod 2064151171) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 82 * (2 : ZMod 2064151171) ^ 82 := by rw [pow_add]
          _ = 1722844091 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 2064151171) ^ 328 = 839705917 := by
        calc
          (2 : ZMod 2064151171) ^ 328 = (2 : ZMod 2064151171) ^ (164 + 164) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 164 * (2 : ZMod 2064151171) ^ 164 := by rw [pow_add]
          _ = 839705917 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 2064151171) ^ 656 = 66056711 := by
        calc
          (2 : ZMod 2064151171) ^ 656 = (2 : ZMod 2064151171) ^ (328 + 328) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 328 * (2 : ZMod 2064151171) ^ 328 := by rw [pow_add]
          _ = 66056711 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 2064151171) ^ 1312 = 1470016123 := by
        calc
          (2 : ZMod 2064151171) ^ 1312 = (2 : ZMod 2064151171) ^ (656 + 656) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 656 * (2 : ZMod 2064151171) ^ 656 := by rw [pow_add]
          _ = 1470016123 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 2064151171) ^ 2624 = 176519285 := by
        calc
          (2 : ZMod 2064151171) ^ 2624 = (2 : ZMod 2064151171) ^ (1312 + 1312) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1312 * (2 : ZMod 2064151171) ^ 1312 := by rw [pow_add]
          _ = 176519285 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 2064151171) ^ 5249 = 863443196 := by
        calc
          (2 : ZMod 2064151171) ^ 5249 = (2 : ZMod 2064151171) ^ (2624 + 2624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2624 * (2 : ZMod 2064151171) ^ 2624) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 863443196 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 2064151171) ^ 10498 = 1489677453 := by
        calc
          (2 : ZMod 2064151171) ^ 10498 = (2 : ZMod 2064151171) ^ (5249 + 5249) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 5249 * (2 : ZMod 2064151171) ^ 5249 := by rw [pow_add]
          _ = 1489677453 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 2064151171) ^ 20997 = 1456684756 := by
        calc
          (2 : ZMod 2064151171) ^ 20997 = (2 : ZMod 2064151171) ^ (10498 + 10498 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 10498 * (2 : ZMod 2064151171) ^ 10498) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1456684756 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 2064151171) ^ 41995 = 1228763472 := by
        calc
          (2 : ZMod 2064151171) ^ 41995 = (2 : ZMod 2064151171) ^ (20997 + 20997 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 20997 * (2 : ZMod 2064151171) ^ 20997) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1228763472 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 2064151171) ^ 83990 = 59353920 := by
        calc
          (2 : ZMod 2064151171) ^ 83990 = (2 : ZMod 2064151171) ^ (41995 + 41995) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 41995 * (2 : ZMod 2064151171) ^ 41995 := by rw [pow_add]
          _ = 59353920 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 2064151171) ^ 167981 = 2031641400 := by
        calc
          (2 : ZMod 2064151171) ^ 167981 = (2 : ZMod 2064151171) ^ (83990 + 83990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 83990 * (2 : ZMod 2064151171) ^ 83990) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 2031641400 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 2064151171) ^ 335962 = 592048192 := by
        calc
          (2 : ZMod 2064151171) ^ 335962 = (2 : ZMod 2064151171) ^ (167981 + 167981) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 167981 * (2 : ZMod 2064151171) ^ 167981 := by rw [pow_add]
          _ = 592048192 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 2064151171) ^ 671924 = 637975346 := by
        calc
          (2 : ZMod 2064151171) ^ 671924 = (2 : ZMod 2064151171) ^ (335962 + 335962) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 335962 * (2 : ZMod 2064151171) ^ 335962 := by rw [pow_add]
          _ = 637975346 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 2064151171) ^ 1343848 = 322666469 := by
        calc
          (2 : ZMod 2064151171) ^ 1343848 = (2 : ZMod 2064151171) ^ (671924 + 671924) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 671924 * (2 : ZMod 2064151171) ^ 671924 := by rw [pow_add]
          _ = 322666469 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 2064151171) ^ 2687696 = 1548149946 := by
        calc
          (2 : ZMod 2064151171) ^ 2687696 = (2 : ZMod 2064151171) ^ (1343848 + 1343848) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1343848 * (2 : ZMod 2064151171) ^ 1343848 := by rw [pow_add]
          _ = 1548149946 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 2064151171) ^ 5375393 = 1900343991 := by
        calc
          (2 : ZMod 2064151171) ^ 5375393 = (2 : ZMod 2064151171) ^ (2687696 + 2687696 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2687696 * (2 : ZMod 2064151171) ^ 2687696) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1900343991 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 2064151171) ^ 10750787 = 932986227 := by
        calc
          (2 : ZMod 2064151171) ^ 10750787 = (2 : ZMod 2064151171) ^ (5375393 + 5375393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 5375393 * (2 : ZMod 2064151171) ^ 5375393) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 932986227 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 2064151171) ^ 21501574 = 861696961 := by
        calc
          (2 : ZMod 2064151171) ^ 21501574 = (2 : ZMod 2064151171) ^ (10750787 + 10750787) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 10750787 * (2 : ZMod 2064151171) ^ 10750787 := by rw [pow_add]
          _ = 861696961 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 2064151171) ^ 43003149 = 1984489741 := by
        calc
          (2 : ZMod 2064151171) ^ 43003149 = (2 : ZMod 2064151171) ^ (21501574 + 21501574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 21501574 * (2 : ZMod 2064151171) ^ 21501574) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1984489741 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 2064151171) ^ 86006298 = 1699720511 := by
        calc
          (2 : ZMod 2064151171) ^ 86006298 = (2 : ZMod 2064151171) ^ (43003149 + 43003149) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 43003149 * (2 : ZMod 2064151171) ^ 43003149 := by rw [pow_add]
          _ = 1699720511 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 2064151171) ^ 172012597 = 1286773550 := by
        calc
          (2 : ZMod 2064151171) ^ 172012597 = (2 : ZMod 2064151171) ^ (86006298 + 86006298 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 86006298 * (2 : ZMod 2064151171) ^ 86006298) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1286773550 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 2064151171) ^ 344025195 = 1012222682 := by
        calc
          (2 : ZMod 2064151171) ^ 344025195 = (2 : ZMod 2064151171) ^ (172012597 + 172012597 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 172012597 * (2 : ZMod 2064151171) ^ 172012597) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1012222682 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 2064151171) ^ 688050390 = 1012222681 := by
        calc
          (2 : ZMod 2064151171) ^ 688050390 = (2 : ZMod 2064151171) ^ (344025195 + 344025195) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 344025195 * (2 : ZMod 2064151171) ^ 344025195 := by rw [pow_add]
          _ = 1012222681 := by rw [factor_1_28]; decide
      change (2 : ZMod 2064151171) ^ 688050390 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (2 : ZMod 2064151171) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 2064151171) ^ 3 = 8 := by
        calc
          (2 : ZMod 2064151171) ^ 3 = (2 : ZMod 2064151171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1 * (2 : ZMod 2064151171) ^ 1) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 2064151171) ^ 6 = 64 := by
        calc
          (2 : ZMod 2064151171) ^ 6 = (2 : ZMod 2064151171) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 3 * (2 : ZMod 2064151171) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 2064151171) ^ 12 = 4096 := by
        calc
          (2 : ZMod 2064151171) ^ 12 = (2 : ZMod 2064151171) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 6 * (2 : ZMod 2064151171) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 2064151171) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 2064151171) ^ 24 = (2 : ZMod 2064151171) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 12 * (2 : ZMod 2064151171) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 2064151171) ^ 49 = 197007995 := by
        calc
          (2 : ZMod 2064151171) ^ 49 = (2 : ZMod 2064151171) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 24 * (2 : ZMod 2064151171) ^ 24) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 197007995 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 2064151171) ^ 98 = 255805036 := by
        calc
          (2 : ZMod 2064151171) ^ 98 = (2 : ZMod 2064151171) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 49 * (2 : ZMod 2064151171) ^ 49 := by rw [pow_add]
          _ = 255805036 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 2064151171) ^ 196 = 786122955 := by
        calc
          (2 : ZMod 2064151171) ^ 196 = (2 : ZMod 2064151171) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 98 * (2 : ZMod 2064151171) ^ 98 := by rw [pow_add]
          _ = 786122955 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 2064151171) ^ 393 = 1093238615 := by
        calc
          (2 : ZMod 2064151171) ^ 393 = (2 : ZMod 2064151171) ^ (196 + 196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 196 * (2 : ZMod 2064151171) ^ 196) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1093238615 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 2064151171) ^ 787 = 1652892663 := by
        calc
          (2 : ZMod 2064151171) ^ 787 = (2 : ZMod 2064151171) ^ (393 + 393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 393 * (2 : ZMod 2064151171) ^ 393) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1652892663 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 2064151171) ^ 1574 = 277390501 := by
        calc
          (2 : ZMod 2064151171) ^ 1574 = (2 : ZMod 2064151171) ^ (787 + 787) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 787 * (2 : ZMod 2064151171) ^ 787 := by rw [pow_add]
          _ = 277390501 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 2064151171) ^ 3149 = 1860885140 := by
        calc
          (2 : ZMod 2064151171) ^ 3149 = (2 : ZMod 2064151171) ^ (1574 + 1574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1574 * (2 : ZMod 2064151171) ^ 1574) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1860885140 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 2064151171) ^ 6299 = 1080796435 := by
        calc
          (2 : ZMod 2064151171) ^ 6299 = (2 : ZMod 2064151171) ^ (3149 + 3149 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 3149 * (2 : ZMod 2064151171) ^ 3149) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1080796435 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 2064151171) ^ 12598 = 1513319889 := by
        calc
          (2 : ZMod 2064151171) ^ 12598 = (2 : ZMod 2064151171) ^ (6299 + 6299) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 6299 * (2 : ZMod 2064151171) ^ 6299 := by rw [pow_add]
          _ = 1513319889 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 2064151171) ^ 25197 = 64333369 := by
        calc
          (2 : ZMod 2064151171) ^ 25197 = (2 : ZMod 2064151171) ^ (12598 + 12598 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 12598 * (2 : ZMod 2064151171) ^ 12598) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 64333369 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 2064151171) ^ 50394 = 329394994 := by
        calc
          (2 : ZMod 2064151171) ^ 50394 = (2 : ZMod 2064151171) ^ (25197 + 25197) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 25197 * (2 : ZMod 2064151171) ^ 25197 := by rw [pow_add]
          _ = 329394994 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 2064151171) ^ 100788 = 229137562 := by
        calc
          (2 : ZMod 2064151171) ^ 100788 = (2 : ZMod 2064151171) ^ (50394 + 50394) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 50394 * (2 : ZMod 2064151171) ^ 50394 := by rw [pow_add]
          _ = 229137562 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 2064151171) ^ 201577 = 1331586544 := by
        calc
          (2 : ZMod 2064151171) ^ 201577 = (2 : ZMod 2064151171) ^ (100788 + 100788 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 100788 * (2 : ZMod 2064151171) ^ 100788) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1331586544 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 2064151171) ^ 403154 = 29494524 := by
        calc
          (2 : ZMod 2064151171) ^ 403154 = (2 : ZMod 2064151171) ^ (201577 + 201577) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 201577 * (2 : ZMod 2064151171) ^ 201577 := by rw [pow_add]
          _ = 29494524 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 2064151171) ^ 806309 = 1511448962 := by
        calc
          (2 : ZMod 2064151171) ^ 806309 = (2 : ZMod 2064151171) ^ (403154 + 403154 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 403154 * (2 : ZMod 2064151171) ^ 403154) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1511448962 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 2064151171) ^ 1612618 = 1613886755 := by
        calc
          (2 : ZMod 2064151171) ^ 1612618 = (2 : ZMod 2064151171) ^ (806309 + 806309) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 806309 * (2 : ZMod 2064151171) ^ 806309 := by rw [pow_add]
          _ = 1613886755 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 2064151171) ^ 3225236 = 1983538114 := by
        calc
          (2 : ZMod 2064151171) ^ 3225236 = (2 : ZMod 2064151171) ^ (1612618 + 1612618) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1612618 * (2 : ZMod 2064151171) ^ 1612618 := by rw [pow_add]
          _ = 1983538114 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 2064151171) ^ 6450472 = 1034784499 := by
        calc
          (2 : ZMod 2064151171) ^ 6450472 = (2 : ZMod 2064151171) ^ (3225236 + 3225236) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 3225236 * (2 : ZMod 2064151171) ^ 3225236 := by rw [pow_add]
          _ = 1034784499 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 2064151171) ^ 12900944 = 670975370 := by
        calc
          (2 : ZMod 2064151171) ^ 12900944 = (2 : ZMod 2064151171) ^ (6450472 + 6450472) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 6450472 * (2 : ZMod 2064151171) ^ 6450472 := by rw [pow_add]
          _ = 670975370 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 2064151171) ^ 25801889 = 1171116369 := by
        calc
          (2 : ZMod 2064151171) ^ 25801889 = (2 : ZMod 2064151171) ^ (12900944 + 12900944 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 12900944 * (2 : ZMod 2064151171) ^ 12900944) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1171116369 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 2064151171) ^ 51603779 = 1362809265 := by
        calc
          (2 : ZMod 2064151171) ^ 51603779 = (2 : ZMod 2064151171) ^ (25801889 + 25801889 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 25801889 * (2 : ZMod 2064151171) ^ 25801889) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1362809265 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 2064151171) ^ 103207558 = 1029195519 := by
        calc
          (2 : ZMod 2064151171) ^ 103207558 = (2 : ZMod 2064151171) ^ (51603779 + 51603779) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 51603779 * (2 : ZMod 2064151171) ^ 51603779 := by rw [pow_add]
          _ = 1029195519 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 2064151171) ^ 206415117 = 1015203103 := by
        calc
          (2 : ZMod 2064151171) ^ 206415117 = (2 : ZMod 2064151171) ^ (103207558 + 103207558 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 103207558 * (2 : ZMod 2064151171) ^ 103207558) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1015203103 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 2064151171) ^ 412830234 = 1708850963 := by
        calc
          (2 : ZMod 2064151171) ^ 412830234 = (2 : ZMod 2064151171) ^ (206415117 + 206415117) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 206415117 * (2 : ZMod 2064151171) ^ 206415117 := by rw [pow_add]
          _ = 1708850963 := by rw [factor_2_27]; decide
      change (2 : ZMod 2064151171) ^ 412830234 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (2 : ZMod 2064151171) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 2064151171) ^ 2 = 4 := by
        calc
          (2 : ZMod 2064151171) ^ 2 = (2 : ZMod 2064151171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1 * (2 : ZMod 2064151171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 2064151171) ^ 5 = 32 := by
        calc
          (2 : ZMod 2064151171) ^ 5 = (2 : ZMod 2064151171) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2 * (2 : ZMod 2064151171) ^ 2) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 2064151171) ^ 10 = 1024 := by
        calc
          (2 : ZMod 2064151171) ^ 10 = (2 : ZMod 2064151171) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 5 * (2 : ZMod 2064151171) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 2064151171) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 2064151171) ^ 20 = (2 : ZMod 2064151171) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 10 * (2 : ZMod 2064151171) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 2064151171) ^ 41 = 702258437 := by
        calc
          (2 : ZMod 2064151171) ^ 41 = (2 : ZMod 2064151171) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 20 * (2 : ZMod 2064151171) ^ 20) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 702258437 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 2064151171) ^ 83 = 449273131 := by
        calc
          (2 : ZMod 2064151171) ^ 83 = (2 : ZMod 2064151171) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 41 * (2 : ZMod 2064151171) ^ 41) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 449273131 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 2064151171) ^ 167 = 1397845702 := by
        calc
          (2 : ZMod 2064151171) ^ 167 = (2 : ZMod 2064151171) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 83 * (2 : ZMod 2064151171) ^ 83) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1397845702 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 2064151171) ^ 335 = 146496484 := by
        calc
          (2 : ZMod 2064151171) ^ 335 = (2 : ZMod 2064151171) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 167 * (2 : ZMod 2064151171) ^ 167) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 146496484 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 2064151171) ^ 670 = 657939420 := by
        calc
          (2 : ZMod 2064151171) ^ 670 = (2 : ZMod 2064151171) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 335 * (2 : ZMod 2064151171) ^ 335 := by rw [pow_add]
          _ = 657939420 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 2064151171) ^ 1340 = 159807684 := by
        calc
          (2 : ZMod 2064151171) ^ 1340 = (2 : ZMod 2064151171) ^ (670 + 670) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 670 * (2 : ZMod 2064151171) ^ 670 := by rw [pow_add]
          _ = 159807684 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 2064151171) ^ 2680 = 173968140 := by
        calc
          (2 : ZMod 2064151171) ^ 2680 = (2 : ZMod 2064151171) ^ (1340 + 1340) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1340 * (2 : ZMod 2064151171) ^ 1340 := by rw [pow_add]
          _ = 173968140 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 2064151171) ^ 5361 = 67491651 := by
        calc
          (2 : ZMod 2064151171) ^ 5361 = (2 : ZMod 2064151171) ^ (2680 + 2680 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2680 * (2 : ZMod 2064151171) ^ 2680) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 67491651 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 2064151171) ^ 10722 = 1626019934 := by
        calc
          (2 : ZMod 2064151171) ^ 10722 = (2 : ZMod 2064151171) ^ (5361 + 5361) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 5361 * (2 : ZMod 2064151171) ^ 5361 := by rw [pow_add]
          _ = 1626019934 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 2064151171) ^ 21444 = 1970666699 := by
        calc
          (2 : ZMod 2064151171) ^ 21444 = (2 : ZMod 2064151171) ^ (10722 + 10722) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 10722 * (2 : ZMod 2064151171) ^ 10722 := by rw [pow_add]
          _ = 1970666699 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 2064151171) ^ 42888 = 850908185 := by
        calc
          (2 : ZMod 2064151171) ^ 42888 = (2 : ZMod 2064151171) ^ (21444 + 21444) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 21444 * (2 : ZMod 2064151171) ^ 21444 := by rw [pow_add]
          _ = 850908185 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 2064151171) ^ 85777 = 892338403 := by
        calc
          (2 : ZMod 2064151171) ^ 85777 = (2 : ZMod 2064151171) ^ (42888 + 42888 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 42888 * (2 : ZMod 2064151171) ^ 42888) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 892338403 := by rw [factor_3_15]; decide
      have factor_3_17 : (2 : ZMod 2064151171) ^ 171555 = 1471974836 := by
        calc
          (2 : ZMod 2064151171) ^ 171555 = (2 : ZMod 2064151171) ^ (85777 + 85777 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 85777 * (2 : ZMod 2064151171) ^ 85777) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1471974836 := by rw [factor_3_16]; decide
      have factor_3_18 : (2 : ZMod 2064151171) ^ 343110 = 519900300 := by
        calc
          (2 : ZMod 2064151171) ^ 343110 = (2 : ZMod 2064151171) ^ (171555 + 171555) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 171555 * (2 : ZMod 2064151171) ^ 171555 := by rw [pow_add]
          _ = 519900300 := by rw [factor_3_17]; decide
      have factor_3_19 : (2 : ZMod 2064151171) ^ 686220 = 954715141 := by
        calc
          (2 : ZMod 2064151171) ^ 686220 = (2 : ZMod 2064151171) ^ (343110 + 343110) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 343110 * (2 : ZMod 2064151171) ^ 343110 := by rw [pow_add]
          _ = 954715141 := by rw [factor_3_18]; decide
      have factor_3_20 : (2 : ZMod 2064151171) ^ 1372440 = 2052020482 := by
        calc
          (2 : ZMod 2064151171) ^ 1372440 = (2 : ZMod 2064151171) ^ (686220 + 686220) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 686220 * (2 : ZMod 2064151171) ^ 686220 := by rw [pow_add]
          _ = 2052020482 := by rw [factor_3_19]; decide
      have factor_3_21 : (2 : ZMod 2064151171) ^ 2744881 = 557268262 := by
        calc
          (2 : ZMod 2064151171) ^ 2744881 = (2 : ZMod 2064151171) ^ (1372440 + 1372440 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1372440 * (2 : ZMod 2064151171) ^ 1372440) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 557268262 := by rw [factor_3_20]; decide
      have factor_3_22 : (2 : ZMod 2064151171) ^ 5489763 = 1866618524 := by
        calc
          (2 : ZMod 2064151171) ^ 5489763 = (2 : ZMod 2064151171) ^ (2744881 + 2744881 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 2744881 * (2 : ZMod 2064151171) ^ 2744881) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1866618524 := by rw [factor_3_21]; decide
      have factor_3_23 : (2 : ZMod 2064151171) ^ 10979527 = 1234113967 := by
        calc
          (2 : ZMod 2064151171) ^ 10979527 = (2 : ZMod 2064151171) ^ (5489763 + 5489763 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 5489763 * (2 : ZMod 2064151171) ^ 5489763) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1234113967 := by rw [factor_3_22]; decide
      have factor_3_24 : (2 : ZMod 2064151171) ^ 21959055 = 322762480 := by
        calc
          (2 : ZMod 2064151171) ^ 21959055 = (2 : ZMod 2064151171) ^ (10979527 + 10979527 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 10979527 * (2 : ZMod 2064151171) ^ 10979527) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 322762480 := by rw [factor_3_23]; decide
      have factor_3_25 : (2 : ZMod 2064151171) ^ 43918110 = 1944667794 := by
        calc
          (2 : ZMod 2064151171) ^ 43918110 = (2 : ZMod 2064151171) ^ (21959055 + 21959055) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 21959055 * (2 : ZMod 2064151171) ^ 21959055 := by rw [pow_add]
          _ = 1944667794 := by rw [factor_3_24]; decide
      change (2 : ZMod 2064151171) ^ 43918110 ≠ 1
      rw [factor_3_25]
      decide
    ·
      have factor_4_0 : (2 : ZMod 2064151171) ^ 1 = 2 := by norm_num
      have factor_4_1 : (2 : ZMod 2064151171) ^ 2 = 4 := by
        calc
          (2 : ZMod 2064151171) ^ 2 = (2 : ZMod 2064151171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 1 * (2 : ZMod 2064151171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_4_0]; decide
      have factor_4_2 : (2 : ZMod 2064151171) ^ 4 = 16 := by
        calc
          (2 : ZMod 2064151171) ^ 4 = (2 : ZMod 2064151171) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 2 * (2 : ZMod 2064151171) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_4_1]; decide
      have factor_4_3 : (2 : ZMod 2064151171) ^ 8 = 256 := by
        calc
          (2 : ZMod 2064151171) ^ 8 = (2 : ZMod 2064151171) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 4 * (2 : ZMod 2064151171) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_4_2]; decide
      have factor_4_4 : (2 : ZMod 2064151171) ^ 16 = 65536 := by
        calc
          (2 : ZMod 2064151171) ^ 16 = (2 : ZMod 2064151171) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 8 * (2 : ZMod 2064151171) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_4_3]; decide
      have factor_4_5 : (2 : ZMod 2064151171) ^ 33 = 333329908 := by
        calc
          (2 : ZMod 2064151171) ^ 33 = (2 : ZMod 2064151171) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 16 * (2 : ZMod 2064151171) ^ 16) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 333329908 := by rw [factor_4_4]; decide
      have factor_4_6 : (2 : ZMod 2064151171) ^ 66 = 1764922601 := by
        calc
          (2 : ZMod 2064151171) ^ 66 = (2 : ZMod 2064151171) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 33 * (2 : ZMod 2064151171) ^ 33 := by rw [pow_add]
          _ = 1764922601 := by rw [factor_4_5]; decide
      have factor_4_7 : (2 : ZMod 2064151171) ^ 132 = 1106831861 := by
        calc
          (2 : ZMod 2064151171) ^ 132 = (2 : ZMod 2064151171) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 66 * (2 : ZMod 2064151171) ^ 66 := by rw [pow_add]
          _ = 1106831861 := by rw [factor_4_6]; decide
      have factor_4_8 : (2 : ZMod 2064151171) ^ 264 = 1849094925 := by
        calc
          (2 : ZMod 2064151171) ^ 264 = (2 : ZMod 2064151171) ^ (132 + 132) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 132 * (2 : ZMod 2064151171) ^ 132 := by rw [pow_add]
          _ = 1849094925 := by rw [factor_4_7]; decide
      have factor_4_9 : (2 : ZMod 2064151171) ^ 528 = 1515640735 := by
        calc
          (2 : ZMod 2064151171) ^ 528 = (2 : ZMod 2064151171) ^ (264 + 264) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 264 * (2 : ZMod 2064151171) ^ 264 := by rw [pow_add]
          _ = 1515640735 := by rw [factor_4_8]; decide
      have factor_4_10 : (2 : ZMod 2064151171) ^ 1057 = 1093816152 := by
        calc
          (2 : ZMod 2064151171) ^ 1057 = (2 : ZMod 2064151171) ^ (528 + 528 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 528 * (2 : ZMod 2064151171) ^ 528) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 1093816152 := by rw [factor_4_9]; decide
      have factor_4_11 : (2 : ZMod 2064151171) ^ 2115 = 340202071 := by
        calc
          (2 : ZMod 2064151171) ^ 2115 = (2 : ZMod 2064151171) ^ (1057 + 1057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = ((2 : ZMod 2064151171) ^ 1057 * (2 : ZMod 2064151171) ^ 1057) * (2 : ZMod 2064151171) := by rw [pow_succ, pow_add]
          _ = 340202071 := by rw [factor_4_10]; decide
      have factor_4_12 : (2 : ZMod 2064151171) ^ 4230 = 1686740343 := by
        calc
          (2 : ZMod 2064151171) ^ 4230 = (2 : ZMod 2064151171) ^ (2115 + 2115) :=
            congrArg (fun n : ℕ => (2 : ZMod 2064151171) ^ n) (by norm_num)
          _ = (2 : ZMod 2064151171) ^ 2115 * (2 : ZMod 2064151171) ^ 2115 := by rw [pow_add]
          _ = 1686740343 := by rw [factor_4_11]; decide
      change (2 : ZMod 2064151171) ^ 4230 ≠ 1
      rw [factor_4_12]
      decide

#print axioms prime_lucas_2064151171

end TotientTailPeriodKiller
end Erdos249257
