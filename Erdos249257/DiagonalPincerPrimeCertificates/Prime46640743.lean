import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_46640743 : Nat.Prime 46640743 := by
  apply lucas_primality 46640743 (3 : ZMod 46640743)
  ·
      have fermat_0 : (3 : ZMod 46640743) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 46640743) ^ 2 = 9 := by
        calc
          (3 : ZMod 46640743) ^ 2 = (3 : ZMod 46640743) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1 * (3 : ZMod 46640743) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 46640743) ^ 5 = 243 := by
        calc
          (3 : ZMod 46640743) ^ 5 = (3 : ZMod 46640743) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 2 * (3 : ZMod 46640743) ^ 2) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 46640743) ^ 11 = 177147 := by
        calc
          (3 : ZMod 46640743) ^ 11 = (3 : ZMod 46640743) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 5 * (3 : ZMod 46640743) ^ 5) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 46640743) ^ 22 = 38480313 := by
        calc
          (3 : ZMod 46640743) ^ 22 = (3 : ZMod 46640743) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 11 * (3 : ZMod 46640743) ^ 11 := by rw [pow_add]
          _ = 38480313 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 46640743) ^ 44 = 37666589 := by
        calc
          (3 : ZMod 46640743) ^ 44 = (3 : ZMod 46640743) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 22 * (3 : ZMod 46640743) ^ 22 := by rw [pow_add]
          _ = 37666589 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 46640743) ^ 88 = 29544242 := by
        calc
          (3 : ZMod 46640743) ^ 88 = (3 : ZMod 46640743) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 44 * (3 : ZMod 46640743) ^ 44 := by rw [pow_add]
          _ = 29544242 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 46640743) ^ 177 = 24850012 := by
        calc
          (3 : ZMod 46640743) ^ 177 = (3 : ZMod 46640743) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 88 * (3 : ZMod 46640743) ^ 88) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 24850012 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 46640743) ^ 355 = 3336778 := by
        calc
          (3 : ZMod 46640743) ^ 355 = (3 : ZMod 46640743) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 177 * (3 : ZMod 46640743) ^ 177) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 3336778 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 46640743) ^ 711 = 27756972 := by
        calc
          (3 : ZMod 46640743) ^ 711 = (3 : ZMod 46640743) ^ (355 + 355 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 355 * (3 : ZMod 46640743) ^ 355) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 27756972 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 46640743) ^ 1423 = 1402577 := by
        calc
          (3 : ZMod 46640743) ^ 1423 = (3 : ZMod 46640743) ^ (711 + 711 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 711 * (3 : ZMod 46640743) ^ 711) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 1402577 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 46640743) ^ 2846 = 8982675 := by
        calc
          (3 : ZMod 46640743) ^ 2846 = (3 : ZMod 46640743) ^ (1423 + 1423) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1423 * (3 : ZMod 46640743) ^ 1423 := by rw [pow_add]
          _ = 8982675 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 46640743) ^ 5693 = 34219104 := by
        calc
          (3 : ZMod 46640743) ^ 5693 = (3 : ZMod 46640743) ^ (2846 + 2846 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 2846 * (3 : ZMod 46640743) ^ 2846) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 34219104 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 46640743) ^ 11386 = 22890749 := by
        calc
          (3 : ZMod 46640743) ^ 11386 = (3 : ZMod 46640743) ^ (5693 + 5693) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 5693 * (3 : ZMod 46640743) ^ 5693 := by rw [pow_add]
          _ = 22890749 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 46640743) ^ 22773 = 42557180 := by
        calc
          (3 : ZMod 46640743) ^ 22773 = (3 : ZMod 46640743) ^ (11386 + 11386 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 11386 * (3 : ZMod 46640743) ^ 11386) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 42557180 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 46640743) ^ 45547 = 19149794 := by
        calc
          (3 : ZMod 46640743) ^ 45547 = (3 : ZMod 46640743) ^ (22773 + 22773 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 22773 * (3 : ZMod 46640743) ^ 22773) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 19149794 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 46640743) ^ 91095 = 34810849 := by
        calc
          (3 : ZMod 46640743) ^ 91095 = (3 : ZMod 46640743) ^ (45547 + 45547 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 45547 * (3 : ZMod 46640743) ^ 45547) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 34810849 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 46640743) ^ 182190 = 3146362 := by
        calc
          (3 : ZMod 46640743) ^ 182190 = (3 : ZMod 46640743) ^ (91095 + 91095) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 91095 * (3 : ZMod 46640743) ^ 91095 := by rw [pow_add]
          _ = 3146362 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 46640743) ^ 364380 = 2851808 := by
        calc
          (3 : ZMod 46640743) ^ 364380 = (3 : ZMod 46640743) ^ (182190 + 182190) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 182190 * (3 : ZMod 46640743) ^ 182190 := by rw [pow_add]
          _ = 2851808 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 46640743) ^ 728761 = 972890 := by
        calc
          (3 : ZMod 46640743) ^ 728761 = (3 : ZMod 46640743) ^ (364380 + 364380 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 364380 * (3 : ZMod 46640743) ^ 364380) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 972890 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 46640743) ^ 1457523 = 9781717 := by
        calc
          (3 : ZMod 46640743) ^ 1457523 = (3 : ZMod 46640743) ^ (728761 + 728761 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 728761 * (3 : ZMod 46640743) ^ 728761) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 9781717 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 46640743) ^ 2915046 = 42348108 := by
        calc
          (3 : ZMod 46640743) ^ 2915046 = (3 : ZMod 46640743) ^ (1457523 + 1457523) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1457523 * (3 : ZMod 46640743) ^ 1457523 := by rw [pow_add]
          _ = 42348108 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 46640743) ^ 5830092 = 30421014 := by
        calc
          (3 : ZMod 46640743) ^ 5830092 = (3 : ZMod 46640743) ^ (2915046 + 2915046) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 2915046 * (3 : ZMod 46640743) ^ 2915046 := by rw [pow_add]
          _ = 30421014 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 46640743) ^ 11660185 = 31306943 := by
        calc
          (3 : ZMod 46640743) ^ 11660185 = (3 : ZMod 46640743) ^ (5830092 + 5830092 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 5830092 * (3 : ZMod 46640743) ^ 5830092) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 31306943 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 46640743) ^ 23320371 = 46640742 := by
        calc
          (3 : ZMod 46640743) ^ 23320371 = (3 : ZMod 46640743) ^ (11660185 + 11660185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 11660185 * (3 : ZMod 46640743) ^ 11660185) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 46640742 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 46640743) ^ 46640742 = 1 := by
        calc
          (3 : ZMod 46640743) ^ 46640742 = (3 : ZMod 46640743) ^ (23320371 + 23320371) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 23320371 * (3 : ZMod 46640743) ^ 23320371 := by rw [pow_add]
          _ = 1 := by rw [fermat_24]; decide
      simpa using fermat_25
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (53, 1), (146669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (53, 1), (146669, 1)] : List FactorBlock).map factorBlockValue).prod = 46640743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 46640743) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 46640743) ^ 2 = 9 := by
        calc
          (3 : ZMod 46640743) ^ 2 = (3 : ZMod 46640743) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1 * (3 : ZMod 46640743) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 46640743) ^ 5 = 243 := by
        calc
          (3 : ZMod 46640743) ^ 5 = (3 : ZMod 46640743) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 2 * (3 : ZMod 46640743) ^ 2) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 46640743) ^ 11 = 177147 := by
        calc
          (3 : ZMod 46640743) ^ 11 = (3 : ZMod 46640743) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 5 * (3 : ZMod 46640743) ^ 5) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 46640743) ^ 22 = 38480313 := by
        calc
          (3 : ZMod 46640743) ^ 22 = (3 : ZMod 46640743) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 11 * (3 : ZMod 46640743) ^ 11 := by rw [pow_add]
          _ = 38480313 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 46640743) ^ 44 = 37666589 := by
        calc
          (3 : ZMod 46640743) ^ 44 = (3 : ZMod 46640743) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 22 * (3 : ZMod 46640743) ^ 22 := by rw [pow_add]
          _ = 37666589 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 46640743) ^ 88 = 29544242 := by
        calc
          (3 : ZMod 46640743) ^ 88 = (3 : ZMod 46640743) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 44 * (3 : ZMod 46640743) ^ 44 := by rw [pow_add]
          _ = 29544242 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 46640743) ^ 177 = 24850012 := by
        calc
          (3 : ZMod 46640743) ^ 177 = (3 : ZMod 46640743) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 88 * (3 : ZMod 46640743) ^ 88) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 24850012 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 46640743) ^ 355 = 3336778 := by
        calc
          (3 : ZMod 46640743) ^ 355 = (3 : ZMod 46640743) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 177 * (3 : ZMod 46640743) ^ 177) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 3336778 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 46640743) ^ 711 = 27756972 := by
        calc
          (3 : ZMod 46640743) ^ 711 = (3 : ZMod 46640743) ^ (355 + 355 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 355 * (3 : ZMod 46640743) ^ 355) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 27756972 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 46640743) ^ 1423 = 1402577 := by
        calc
          (3 : ZMod 46640743) ^ 1423 = (3 : ZMod 46640743) ^ (711 + 711 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 711 * (3 : ZMod 46640743) ^ 711) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 1402577 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 46640743) ^ 2846 = 8982675 := by
        calc
          (3 : ZMod 46640743) ^ 2846 = (3 : ZMod 46640743) ^ (1423 + 1423) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1423 * (3 : ZMod 46640743) ^ 1423 := by rw [pow_add]
          _ = 8982675 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 46640743) ^ 5693 = 34219104 := by
        calc
          (3 : ZMod 46640743) ^ 5693 = (3 : ZMod 46640743) ^ (2846 + 2846 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 2846 * (3 : ZMod 46640743) ^ 2846) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 34219104 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 46640743) ^ 11386 = 22890749 := by
        calc
          (3 : ZMod 46640743) ^ 11386 = (3 : ZMod 46640743) ^ (5693 + 5693) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 5693 * (3 : ZMod 46640743) ^ 5693 := by rw [pow_add]
          _ = 22890749 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 46640743) ^ 22773 = 42557180 := by
        calc
          (3 : ZMod 46640743) ^ 22773 = (3 : ZMod 46640743) ^ (11386 + 11386 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 11386 * (3 : ZMod 46640743) ^ 11386) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 42557180 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 46640743) ^ 45547 = 19149794 := by
        calc
          (3 : ZMod 46640743) ^ 45547 = (3 : ZMod 46640743) ^ (22773 + 22773 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 22773 * (3 : ZMod 46640743) ^ 22773) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 19149794 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 46640743) ^ 91095 = 34810849 := by
        calc
          (3 : ZMod 46640743) ^ 91095 = (3 : ZMod 46640743) ^ (45547 + 45547 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 45547 * (3 : ZMod 46640743) ^ 45547) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 34810849 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 46640743) ^ 182190 = 3146362 := by
        calc
          (3 : ZMod 46640743) ^ 182190 = (3 : ZMod 46640743) ^ (91095 + 91095) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 91095 * (3 : ZMod 46640743) ^ 91095 := by rw [pow_add]
          _ = 3146362 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 46640743) ^ 364380 = 2851808 := by
        calc
          (3 : ZMod 46640743) ^ 364380 = (3 : ZMod 46640743) ^ (182190 + 182190) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 182190 * (3 : ZMod 46640743) ^ 182190 := by rw [pow_add]
          _ = 2851808 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 46640743) ^ 728761 = 972890 := by
        calc
          (3 : ZMod 46640743) ^ 728761 = (3 : ZMod 46640743) ^ (364380 + 364380 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 364380 * (3 : ZMod 46640743) ^ 364380) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 972890 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 46640743) ^ 1457523 = 9781717 := by
        calc
          (3 : ZMod 46640743) ^ 1457523 = (3 : ZMod 46640743) ^ (728761 + 728761 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 728761 * (3 : ZMod 46640743) ^ 728761) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 9781717 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 46640743) ^ 2915046 = 42348108 := by
        calc
          (3 : ZMod 46640743) ^ 2915046 = (3 : ZMod 46640743) ^ (1457523 + 1457523) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1457523 * (3 : ZMod 46640743) ^ 1457523 := by rw [pow_add]
          _ = 42348108 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 46640743) ^ 5830092 = 30421014 := by
        calc
          (3 : ZMod 46640743) ^ 5830092 = (3 : ZMod 46640743) ^ (2915046 + 2915046) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 2915046 * (3 : ZMod 46640743) ^ 2915046 := by rw [pow_add]
          _ = 30421014 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 46640743) ^ 11660185 = 31306943 := by
        calc
          (3 : ZMod 46640743) ^ 11660185 = (3 : ZMod 46640743) ^ (5830092 + 5830092 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 5830092 * (3 : ZMod 46640743) ^ 5830092) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 31306943 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 46640743) ^ 23320371 = 46640742 := by
        calc
          (3 : ZMod 46640743) ^ 23320371 = (3 : ZMod 46640743) ^ (11660185 + 11660185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 11660185 * (3 : ZMod 46640743) ^ 11660185) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 46640742 := by rw [factor_0_23]; decide
      change (3 : ZMod 46640743) ^ 23320371 ≠ 1
      rw [factor_0_24]
      decide
    ·
      have factor_1_0 : (3 : ZMod 46640743) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 46640743) ^ 3 = 27 := by
        calc
          (3 : ZMod 46640743) ^ 3 = (3 : ZMod 46640743) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 1 * (3 : ZMod 46640743) ^ 1) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 46640743) ^ 7 = 2187 := by
        calc
          (3 : ZMod 46640743) ^ 7 = (3 : ZMod 46640743) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 3 * (3 : ZMod 46640743) ^ 3) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 46640743) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 46640743) ^ 14 = (3 : ZMod 46640743) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 7 * (3 : ZMod 46640743) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 46640743) ^ 29 = 16544159 := by
        calc
          (3 : ZMod 46640743) ^ 29 = (3 : ZMod 46640743) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 14 * (3 : ZMod 46640743) ^ 14) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 16544159 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 46640743) ^ 59 = 6821190 := by
        calc
          (3 : ZMod 46640743) ^ 59 = (3 : ZMod 46640743) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 29 * (3 : ZMod 46640743) ^ 29) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 6821190 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 46640743) ^ 118 = 14362272 := by
        calc
          (3 : ZMod 46640743) ^ 118 = (3 : ZMod 46640743) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 59 * (3 : ZMod 46640743) ^ 59 := by rw [pow_add]
          _ = 14362272 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 46640743) ^ 237 = 43519224 := by
        calc
          (3 : ZMod 46640743) ^ 237 = (3 : ZMod 46640743) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 118 * (3 : ZMod 46640743) ^ 118) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 43519224 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 46640743) ^ 474 = 23325002 := by
        calc
          (3 : ZMod 46640743) ^ 474 = (3 : ZMod 46640743) ^ (237 + 237) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 237 * (3 : ZMod 46640743) ^ 237 := by rw [pow_add]
          _ = 23325002 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 46640743) ^ 948 = 33101716 := by
        calc
          (3 : ZMod 46640743) ^ 948 = (3 : ZMod 46640743) ^ (474 + 474) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 474 * (3 : ZMod 46640743) ^ 474 := by rw [pow_add]
          _ = 33101716 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 46640743) ^ 1897 = 34889893 := by
        calc
          (3 : ZMod 46640743) ^ 1897 = (3 : ZMod 46640743) ^ (948 + 948 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 948 * (3 : ZMod 46640743) ^ 948) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 34889893 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 46640743) ^ 3795 = 19131148 := by
        calc
          (3 : ZMod 46640743) ^ 3795 = (3 : ZMod 46640743) ^ (1897 + 1897 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 1897 * (3 : ZMod 46640743) ^ 1897) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 19131148 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 46640743) ^ 7591 = 45269869 := by
        calc
          (3 : ZMod 46640743) ^ 7591 = (3 : ZMod 46640743) ^ (3795 + 3795 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 3795 * (3 : ZMod 46640743) ^ 3795) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 45269869 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 46640743) ^ 15182 = 66177 := by
        calc
          (3 : ZMod 46640743) ^ 15182 = (3 : ZMod 46640743) ^ (7591 + 7591) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 7591 * (3 : ZMod 46640743) ^ 7591 := by rw [pow_add]
          _ = 66177 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 46640743) ^ 30365 = 32137204 := by
        calc
          (3 : ZMod 46640743) ^ 30365 = (3 : ZMod 46640743) ^ (15182 + 15182 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 15182 * (3 : ZMod 46640743) ^ 15182) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 32137204 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 46640743) ^ 60730 = 868455 := by
        calc
          (3 : ZMod 46640743) ^ 60730 = (3 : ZMod 46640743) ^ (30365 + 30365) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 30365 * (3 : ZMod 46640743) ^ 30365 := by rw [pow_add]
          _ = 868455 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 46640743) ^ 121460 = 33272715 := by
        calc
          (3 : ZMod 46640743) ^ 121460 = (3 : ZMod 46640743) ^ (60730 + 60730) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 60730 * (3 : ZMod 46640743) ^ 60730 := by rw [pow_add]
          _ = 33272715 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 46640743) ^ 242920 = 25882055 := by
        calc
          (3 : ZMod 46640743) ^ 242920 = (3 : ZMod 46640743) ^ (121460 + 121460) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 121460 * (3 : ZMod 46640743) ^ 121460 := by rw [pow_add]
          _ = 25882055 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 46640743) ^ 485841 = 17548718 := by
        calc
          (3 : ZMod 46640743) ^ 485841 = (3 : ZMod 46640743) ^ (242920 + 242920 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 242920 * (3 : ZMod 46640743) ^ 242920) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 17548718 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 46640743) ^ 971682 = 11115073 := by
        calc
          (3 : ZMod 46640743) ^ 971682 = (3 : ZMod 46640743) ^ (485841 + 485841) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 485841 * (3 : ZMod 46640743) ^ 485841 := by rw [pow_add]
          _ = 11115073 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 46640743) ^ 1943364 = 2651606 := by
        calc
          (3 : ZMod 46640743) ^ 1943364 = (3 : ZMod 46640743) ^ (971682 + 971682) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 971682 * (3 : ZMod 46640743) ^ 971682 := by rw [pow_add]
          _ = 2651606 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 46640743) ^ 3886728 = 15653472 := by
        calc
          (3 : ZMod 46640743) ^ 3886728 = (3 : ZMod 46640743) ^ (1943364 + 1943364) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1943364 * (3 : ZMod 46640743) ^ 1943364 := by rw [pow_add]
          _ = 15653472 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 46640743) ^ 7773457 = 319672 := by
        calc
          (3 : ZMod 46640743) ^ 7773457 = (3 : ZMod 46640743) ^ (3886728 + 3886728 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 3886728 * (3 : ZMod 46640743) ^ 3886728) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 319672 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 46640743) ^ 15546914 = 319671 := by
        calc
          (3 : ZMod 46640743) ^ 15546914 = (3 : ZMod 46640743) ^ (7773457 + 7773457) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 7773457 * (3 : ZMod 46640743) ^ 7773457 := by rw [pow_add]
          _ = 319671 := by rw [factor_1_22]; decide
      change (3 : ZMod 46640743) ^ 15546914 ≠ 1
      rw [factor_1_23]
      decide
    ·
      have factor_2_0 : (3 : ZMod 46640743) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 46640743) ^ 3 = 27 := by
        calc
          (3 : ZMod 46640743) ^ 3 = (3 : ZMod 46640743) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 1 * (3 : ZMod 46640743) ^ 1) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 46640743) ^ 6 = 729 := by
        calc
          (3 : ZMod 46640743) ^ 6 = (3 : ZMod 46640743) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 3 * (3 : ZMod 46640743) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 46640743) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 46640743) ^ 13 = (3 : ZMod 46640743) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 6 * (3 : ZMod 46640743) ^ 6) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 46640743) ^ 26 = 38616315 := by
        calc
          (3 : ZMod 46640743) ^ 26 = (3 : ZMod 46640743) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 13 * (3 : ZMod 46640743) ^ 13 := by rw [pow_add]
          _ = 38616315 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 46640743) ^ 53 = 36861302 := by
        calc
          (3 : ZMod 46640743) ^ 53 = (3 : ZMod 46640743) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 26 * (3 : ZMod 46640743) ^ 26) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 36861302 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 46640743) ^ 107 = 2623223 := by
        calc
          (3 : ZMod 46640743) ^ 107 = (3 : ZMod 46640743) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 53 * (3 : ZMod 46640743) ^ 53) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 2623223 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 46640743) ^ 214 = 16966995 := by
        calc
          (3 : ZMod 46640743) ^ 214 = (3 : ZMod 46640743) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 107 * (3 : ZMod 46640743) ^ 107 := by rw [pow_add]
          _ = 16966995 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 46640743) ^ 429 = 7696591 := by
        calc
          (3 : ZMod 46640743) ^ 429 = (3 : ZMod 46640743) ^ (214 + 214 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 214 * (3 : ZMod 46640743) ^ 214) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 7696591 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 46640743) ^ 859 = 21174037 := by
        calc
          (3 : ZMod 46640743) ^ 859 = (3 : ZMod 46640743) ^ (429 + 429 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 429 * (3 : ZMod 46640743) ^ 429) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 21174037 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 46640743) ^ 1718 = 10619223 := by
        calc
          (3 : ZMod 46640743) ^ 1718 = (3 : ZMod 46640743) ^ (859 + 859) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 859 * (3 : ZMod 46640743) ^ 859 := by rw [pow_add]
          _ = 10619223 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 46640743) ^ 3437 = 5939445 := by
        calc
          (3 : ZMod 46640743) ^ 3437 = (3 : ZMod 46640743) ^ (1718 + 1718 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 1718 * (3 : ZMod 46640743) ^ 1718) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 5939445 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 46640743) ^ 6875 = 3286551 := by
        calc
          (3 : ZMod 46640743) ^ 6875 = (3 : ZMod 46640743) ^ (3437 + 3437 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 3437 * (3 : ZMod 46640743) ^ 3437) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 3286551 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 46640743) ^ 13750 = 27726460 := by
        calc
          (3 : ZMod 46640743) ^ 13750 = (3 : ZMod 46640743) ^ (6875 + 6875) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 6875 * (3 : ZMod 46640743) ^ 6875 := by rw [pow_add]
          _ = 27726460 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 46640743) ^ 27500 = 24585927 := by
        calc
          (3 : ZMod 46640743) ^ 27500 = (3 : ZMod 46640743) ^ (13750 + 13750) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 13750 * (3 : ZMod 46640743) ^ 13750 := by rw [pow_add]
          _ = 24585927 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 46640743) ^ 55000 = 45909889 := by
        calc
          (3 : ZMod 46640743) ^ 55000 = (3 : ZMod 46640743) ^ (27500 + 27500) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 27500 * (3 : ZMod 46640743) ^ 27500 := by rw [pow_add]
          _ = 45909889 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 46640743) ^ 110001 = 6700697 := by
        calc
          (3 : ZMod 46640743) ^ 110001 = (3 : ZMod 46640743) ^ (55000 + 55000 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 55000 * (3 : ZMod 46640743) ^ 55000) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 6700697 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 46640743) ^ 220003 = 21480857 := by
        calc
          (3 : ZMod 46640743) ^ 220003 = (3 : ZMod 46640743) ^ (110001 + 110001 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 110001 * (3 : ZMod 46640743) ^ 110001) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 21480857 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 46640743) ^ 440007 = 24772252 := by
        calc
          (3 : ZMod 46640743) ^ 440007 = (3 : ZMod 46640743) ^ (220003 + 220003 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 220003 * (3 : ZMod 46640743) ^ 220003) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 24772252 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 46640743) ^ 880014 = 40266581 := by
        calc
          (3 : ZMod 46640743) ^ 880014 = (3 : ZMod 46640743) ^ (440007 + 440007) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 440007 * (3 : ZMod 46640743) ^ 440007 := by rw [pow_add]
          _ = 40266581 := by rw [factor_2_18]; decide
      change (3 : ZMod 46640743) ^ 880014 ≠ 1
      rw [factor_2_19]
      decide
    ·
      have factor_3_0 : (3 : ZMod 46640743) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 46640743) ^ 2 = 9 := by
        calc
          (3 : ZMod 46640743) ^ 2 = (3 : ZMod 46640743) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 1 * (3 : ZMod 46640743) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 46640743) ^ 4 = 81 := by
        calc
          (3 : ZMod 46640743) ^ 4 = (3 : ZMod 46640743) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 2 * (3 : ZMod 46640743) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 46640743) ^ 9 = 19683 := by
        calc
          (3 : ZMod 46640743) ^ 9 = (3 : ZMod 46640743) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 4 * (3 : ZMod 46640743) ^ 4) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 46640743) ^ 19 = 42883635 := by
        calc
          (3 : ZMod 46640743) ^ 19 = (3 : ZMod 46640743) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 9 * (3 : ZMod 46640743) ^ 9) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 42883635 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 46640743) ^ 39 = 25682656 := by
        calc
          (3 : ZMod 46640743) ^ 39 = (3 : ZMod 46640743) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 19 * (3 : ZMod 46640743) ^ 19) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 25682656 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 46640743) ^ 79 = 17505701 := by
        calc
          (3 : ZMod 46640743) ^ 79 = (3 : ZMod 46640743) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 39 * (3 : ZMod 46640743) ^ 39) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 17505701 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 46640743) ^ 159 = 4463906 := by
        calc
          (3 : ZMod 46640743) ^ 159 = (3 : ZMod 46640743) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = ((3 : ZMod 46640743) ^ 79 * (3 : ZMod 46640743) ^ 79) * (3 : ZMod 46640743) := by rw [pow_succ, pow_add]
          _ = 4463906 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 46640743) ^ 318 = 38863460 := by
        calc
          (3 : ZMod 46640743) ^ 318 = (3 : ZMod 46640743) ^ (159 + 159) :=
            congrArg (fun n : ℕ => (3 : ZMod 46640743) ^ n) (by norm_num)
          _ = (3 : ZMod 46640743) ^ 159 * (3 : ZMod 46640743) ^ 159 := by rw [pow_add]
          _ = 38863460 := by rw [factor_3_7]; decide
      change (3 : ZMod 46640743) ^ 318 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_46640743

end TotientTailPeriodKiller
end Erdos249257
