import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_154779973 : Nat.Prime 154779973 := by
  apply lucas_primality 154779973 (2 : ZMod 154779973)
  ·
      have fermat_0 : (2 : ZMod 154779973) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 154779973) ^ 2 = 4 := by
        calc
          (2 : ZMod 154779973) ^ 2 = (2 : ZMod 154779973) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 1 * (2 : ZMod 154779973) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 154779973) ^ 4 = 16 := by
        calc
          (2 : ZMod 154779973) ^ 4 = (2 : ZMod 154779973) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 2 * (2 : ZMod 154779973) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 154779973) ^ 9 = 512 := by
        calc
          (2 : ZMod 154779973) ^ 9 = (2 : ZMod 154779973) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 4 * (2 : ZMod 154779973) ^ 4) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 154779973) ^ 18 = 262144 := by
        calc
          (2 : ZMod 154779973) ^ 18 = (2 : ZMod 154779973) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 9 * (2 : ZMod 154779973) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 154779973) ^ 36 = 151948697 := by
        calc
          (2 : ZMod 154779973) ^ 36 = (2 : ZMod 154779973) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 18 * (2 : ZMod 154779973) ^ 18 := by rw [pow_add]
          _ = 151948697 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 154779973) ^ 73 = 137973012 := by
        calc
          (2 : ZMod 154779973) ^ 73 = (2 : ZMod 154779973) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 36 * (2 : ZMod 154779973) ^ 36) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 137973012 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 154779973) ^ 147 = 45981204 := by
        calc
          (2 : ZMod 154779973) ^ 147 = (2 : ZMod 154779973) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 73 * (2 : ZMod 154779973) ^ 73) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 45981204 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 154779973) ^ 295 = 123771078 := by
        calc
          (2 : ZMod 154779973) ^ 295 = (2 : ZMod 154779973) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 147 * (2 : ZMod 154779973) ^ 147) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 123771078 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 154779973) ^ 590 = 24795204 := by
        calc
          (2 : ZMod 154779973) ^ 590 = (2 : ZMod 154779973) ^ (295 + 295) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 295 * (2 : ZMod 154779973) ^ 295 := by rw [pow_add]
          _ = 24795204 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 154779973) ^ 1180 = 146308397 := by
        calc
          (2 : ZMod 154779973) ^ 1180 = (2 : ZMod 154779973) ^ (590 + 590) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 590 * (2 : ZMod 154779973) ^ 590 := by rw [pow_add]
          _ = 146308397 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 154779973) ^ 2361 = 146665975 := by
        calc
          (2 : ZMod 154779973) ^ 2361 = (2 : ZMod 154779973) ^ (1180 + 1180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1180 * (2 : ZMod 154779973) ^ 1180) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 146665975 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 154779973) ^ 4723 = 127577340 := by
        calc
          (2 : ZMod 154779973) ^ 4723 = (2 : ZMod 154779973) ^ (2361 + 2361 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 2361 * (2 : ZMod 154779973) ^ 2361) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 127577340 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 154779973) ^ 9447 = 6112466 := by
        calc
          (2 : ZMod 154779973) ^ 9447 = (2 : ZMod 154779973) ^ (4723 + 4723 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 4723 * (2 : ZMod 154779973) ^ 4723) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 6112466 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 154779973) ^ 18894 = 57698659 := by
        calc
          (2 : ZMod 154779973) ^ 18894 = (2 : ZMod 154779973) ^ (9447 + 9447) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 9447 * (2 : ZMod 154779973) ^ 9447 := by rw [pow_add]
          _ = 57698659 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 154779973) ^ 37788 = 52416529 := by
        calc
          (2 : ZMod 154779973) ^ 37788 = (2 : ZMod 154779973) ^ (18894 + 18894) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 18894 * (2 : ZMod 154779973) ^ 18894 := by rw [pow_add]
          _ = 52416529 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 154779973) ^ 75576 = 22003653 := by
        calc
          (2 : ZMod 154779973) ^ 75576 = (2 : ZMod 154779973) ^ (37788 + 37788) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 37788 * (2 : ZMod 154779973) ^ 37788 := by rw [pow_add]
          _ = 22003653 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 154779973) ^ 151152 = 12561975 := by
        calc
          (2 : ZMod 154779973) ^ 151152 = (2 : ZMod 154779973) ^ (75576 + 75576) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 75576 * (2 : ZMod 154779973) ^ 75576 := by rw [pow_add]
          _ = 12561975 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 154779973) ^ 302304 = 80467989 := by
        calc
          (2 : ZMod 154779973) ^ 302304 = (2 : ZMod 154779973) ^ (151152 + 151152) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 151152 * (2 : ZMod 154779973) ^ 151152 := by rw [pow_add]
          _ = 80467989 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 154779973) ^ 604609 = 111875339 := by
        calc
          (2 : ZMod 154779973) ^ 604609 = (2 : ZMod 154779973) ^ (302304 + 302304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 302304 * (2 : ZMod 154779973) ^ 302304) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 111875339 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 154779973) ^ 1209218 = 112986576 := by
        calc
          (2 : ZMod 154779973) ^ 1209218 = (2 : ZMod 154779973) ^ (604609 + 604609) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 604609 * (2 : ZMod 154779973) ^ 604609 := by rw [pow_add]
          _ = 112986576 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 154779973) ^ 2418437 = 123547814 := by
        calc
          (2 : ZMod 154779973) ^ 2418437 = (2 : ZMod 154779973) ^ (1209218 + 1209218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1209218 * (2 : ZMod 154779973) ^ 1209218) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 123547814 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 154779973) ^ 4836874 = 65499520 := by
        calc
          (2 : ZMod 154779973) ^ 4836874 = (2 : ZMod 154779973) ^ (2418437 + 2418437) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 2418437 * (2 : ZMod 154779973) ^ 2418437 := by rw [pow_add]
          _ = 65499520 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 154779973) ^ 9673748 = 7675671 := by
        calc
          (2 : ZMod 154779973) ^ 9673748 = (2 : ZMod 154779973) ^ (4836874 + 4836874) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 4836874 * (2 : ZMod 154779973) ^ 4836874 := by rw [pow_add]
          _ = 7675671 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 154779973) ^ 19347496 = 12037602 := by
        calc
          (2 : ZMod 154779973) ^ 19347496 = (2 : ZMod 154779973) ^ (9673748 + 9673748) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 9673748 * (2 : ZMod 154779973) ^ 9673748 := by rw [pow_add]
          _ = 12037602 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 154779973) ^ 38694993 = 24075203 := by
        calc
          (2 : ZMod 154779973) ^ 38694993 = (2 : ZMod 154779973) ^ (19347496 + 19347496 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 19347496 * (2 : ZMod 154779973) ^ 19347496) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 24075203 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 154779973) ^ 77389986 = 154779972 := by
        calc
          (2 : ZMod 154779973) ^ 77389986 = (2 : ZMod 154779973) ^ (38694993 + 38694993) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 38694993 * (2 : ZMod 154779973) ^ 38694993 := by rw [pow_add]
          _ = 154779972 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 154779973) ^ 154779972 = 1 := by
        calc
          (2 : ZMod 154779973) ^ 154779972 = (2 : ZMod 154779973) ^ (77389986 + 77389986) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 77389986 * (2 : ZMod 154779973) ^ 77389986 := by rw [pow_add]
          _ = 1 := by rw [fermat_26]; decide
      simpa using fermat_27
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (23, 1), (560797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (23, 1), (560797, 1)] : List FactorBlock).map factorBlockValue).prod = 154779973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 154779973) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 154779973) ^ 2 = 4 := by
        calc
          (2 : ZMod 154779973) ^ 2 = (2 : ZMod 154779973) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 1 * (2 : ZMod 154779973) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 154779973) ^ 4 = 16 := by
        calc
          (2 : ZMod 154779973) ^ 4 = (2 : ZMod 154779973) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 2 * (2 : ZMod 154779973) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 154779973) ^ 9 = 512 := by
        calc
          (2 : ZMod 154779973) ^ 9 = (2 : ZMod 154779973) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 4 * (2 : ZMod 154779973) ^ 4) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 154779973) ^ 18 = 262144 := by
        calc
          (2 : ZMod 154779973) ^ 18 = (2 : ZMod 154779973) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 9 * (2 : ZMod 154779973) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 154779973) ^ 36 = 151948697 := by
        calc
          (2 : ZMod 154779973) ^ 36 = (2 : ZMod 154779973) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 18 * (2 : ZMod 154779973) ^ 18 := by rw [pow_add]
          _ = 151948697 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 154779973) ^ 73 = 137973012 := by
        calc
          (2 : ZMod 154779973) ^ 73 = (2 : ZMod 154779973) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 36 * (2 : ZMod 154779973) ^ 36) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 137973012 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 154779973) ^ 147 = 45981204 := by
        calc
          (2 : ZMod 154779973) ^ 147 = (2 : ZMod 154779973) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 73 * (2 : ZMod 154779973) ^ 73) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 45981204 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 154779973) ^ 295 = 123771078 := by
        calc
          (2 : ZMod 154779973) ^ 295 = (2 : ZMod 154779973) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 147 * (2 : ZMod 154779973) ^ 147) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 123771078 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 154779973) ^ 590 = 24795204 := by
        calc
          (2 : ZMod 154779973) ^ 590 = (2 : ZMod 154779973) ^ (295 + 295) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 295 * (2 : ZMod 154779973) ^ 295 := by rw [pow_add]
          _ = 24795204 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 154779973) ^ 1180 = 146308397 := by
        calc
          (2 : ZMod 154779973) ^ 1180 = (2 : ZMod 154779973) ^ (590 + 590) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 590 * (2 : ZMod 154779973) ^ 590 := by rw [pow_add]
          _ = 146308397 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 154779973) ^ 2361 = 146665975 := by
        calc
          (2 : ZMod 154779973) ^ 2361 = (2 : ZMod 154779973) ^ (1180 + 1180 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1180 * (2 : ZMod 154779973) ^ 1180) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 146665975 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 154779973) ^ 4723 = 127577340 := by
        calc
          (2 : ZMod 154779973) ^ 4723 = (2 : ZMod 154779973) ^ (2361 + 2361 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 2361 * (2 : ZMod 154779973) ^ 2361) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 127577340 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 154779973) ^ 9447 = 6112466 := by
        calc
          (2 : ZMod 154779973) ^ 9447 = (2 : ZMod 154779973) ^ (4723 + 4723 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 4723 * (2 : ZMod 154779973) ^ 4723) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 6112466 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 154779973) ^ 18894 = 57698659 := by
        calc
          (2 : ZMod 154779973) ^ 18894 = (2 : ZMod 154779973) ^ (9447 + 9447) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 9447 * (2 : ZMod 154779973) ^ 9447 := by rw [pow_add]
          _ = 57698659 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 154779973) ^ 37788 = 52416529 := by
        calc
          (2 : ZMod 154779973) ^ 37788 = (2 : ZMod 154779973) ^ (18894 + 18894) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 18894 * (2 : ZMod 154779973) ^ 18894 := by rw [pow_add]
          _ = 52416529 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 154779973) ^ 75576 = 22003653 := by
        calc
          (2 : ZMod 154779973) ^ 75576 = (2 : ZMod 154779973) ^ (37788 + 37788) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 37788 * (2 : ZMod 154779973) ^ 37788 := by rw [pow_add]
          _ = 22003653 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 154779973) ^ 151152 = 12561975 := by
        calc
          (2 : ZMod 154779973) ^ 151152 = (2 : ZMod 154779973) ^ (75576 + 75576) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 75576 * (2 : ZMod 154779973) ^ 75576 := by rw [pow_add]
          _ = 12561975 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 154779973) ^ 302304 = 80467989 := by
        calc
          (2 : ZMod 154779973) ^ 302304 = (2 : ZMod 154779973) ^ (151152 + 151152) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 151152 * (2 : ZMod 154779973) ^ 151152 := by rw [pow_add]
          _ = 80467989 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 154779973) ^ 604609 = 111875339 := by
        calc
          (2 : ZMod 154779973) ^ 604609 = (2 : ZMod 154779973) ^ (302304 + 302304 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 302304 * (2 : ZMod 154779973) ^ 302304) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 111875339 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 154779973) ^ 1209218 = 112986576 := by
        calc
          (2 : ZMod 154779973) ^ 1209218 = (2 : ZMod 154779973) ^ (604609 + 604609) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 604609 * (2 : ZMod 154779973) ^ 604609 := by rw [pow_add]
          _ = 112986576 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 154779973) ^ 2418437 = 123547814 := by
        calc
          (2 : ZMod 154779973) ^ 2418437 = (2 : ZMod 154779973) ^ (1209218 + 1209218 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1209218 * (2 : ZMod 154779973) ^ 1209218) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 123547814 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 154779973) ^ 4836874 = 65499520 := by
        calc
          (2 : ZMod 154779973) ^ 4836874 = (2 : ZMod 154779973) ^ (2418437 + 2418437) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 2418437 * (2 : ZMod 154779973) ^ 2418437 := by rw [pow_add]
          _ = 65499520 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 154779973) ^ 9673748 = 7675671 := by
        calc
          (2 : ZMod 154779973) ^ 9673748 = (2 : ZMod 154779973) ^ (4836874 + 4836874) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 4836874 * (2 : ZMod 154779973) ^ 4836874 := by rw [pow_add]
          _ = 7675671 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 154779973) ^ 19347496 = 12037602 := by
        calc
          (2 : ZMod 154779973) ^ 19347496 = (2 : ZMod 154779973) ^ (9673748 + 9673748) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 9673748 * (2 : ZMod 154779973) ^ 9673748 := by rw [pow_add]
          _ = 12037602 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 154779973) ^ 38694993 = 24075203 := by
        calc
          (2 : ZMod 154779973) ^ 38694993 = (2 : ZMod 154779973) ^ (19347496 + 19347496 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 19347496 * (2 : ZMod 154779973) ^ 19347496) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 24075203 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 154779973) ^ 77389986 = 154779972 := by
        calc
          (2 : ZMod 154779973) ^ 77389986 = (2 : ZMod 154779973) ^ (38694993 + 38694993) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 38694993 * (2 : ZMod 154779973) ^ 38694993 := by rw [pow_add]
          _ = 154779972 := by rw [factor_0_25]; decide
      change (2 : ZMod 154779973) ^ 77389986 ≠ 1
      rw [factor_0_26]
      decide
    ·
      have factor_1_0 : (2 : ZMod 154779973) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 154779973) ^ 3 = 8 := by
        calc
          (2 : ZMod 154779973) ^ 3 = (2 : ZMod 154779973) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1 * (2 : ZMod 154779973) ^ 1) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 154779973) ^ 6 = 64 := by
        calc
          (2 : ZMod 154779973) ^ 6 = (2 : ZMod 154779973) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 3 * (2 : ZMod 154779973) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 154779973) ^ 12 = 4096 := by
        calc
          (2 : ZMod 154779973) ^ 12 = (2 : ZMod 154779973) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 6 * (2 : ZMod 154779973) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 154779973) ^ 24 = 16777216 := by
        calc
          (2 : ZMod 154779973) ^ 24 = (2 : ZMod 154779973) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 12 * (2 : ZMod 154779973) ^ 12 := by rw [pow_add]
          _ = 16777216 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 154779973) ^ 49 = 23182958 := by
        calc
          (2 : ZMod 154779973) ^ 49 = (2 : ZMod 154779973) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 24 * (2 : ZMod 154779973) ^ 24) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 23182958 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 154779973) ^ 98 = 76283079 := by
        calc
          (2 : ZMod 154779973) ^ 98 = (2 : ZMod 154779973) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 49 * (2 : ZMod 154779973) ^ 49 := by rw [pow_add]
          _ = 76283079 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 154779973) ^ 196 = 122032268 := by
        calc
          (2 : ZMod 154779973) ^ 196 = (2 : ZMod 154779973) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 98 * (2 : ZMod 154779973) ^ 98 := by rw [pow_add]
          _ = 122032268 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 154779973) ^ 393 = 49019719 := by
        calc
          (2 : ZMod 154779973) ^ 393 = (2 : ZMod 154779973) ^ (196 + 196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 196 * (2 : ZMod 154779973) ^ 196) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 49019719 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 154779973) ^ 787 = 10438769 := by
        calc
          (2 : ZMod 154779973) ^ 787 = (2 : ZMod 154779973) ^ (393 + 393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 393 * (2 : ZMod 154779973) ^ 393) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 10438769 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 154779973) ^ 1574 = 11203847 := by
        calc
          (2 : ZMod 154779973) ^ 1574 = (2 : ZMod 154779973) ^ (787 + 787) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 787 * (2 : ZMod 154779973) ^ 787 := by rw [pow_add]
          _ = 11203847 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 154779973) ^ 3149 = 32892683 := by
        calc
          (2 : ZMod 154779973) ^ 3149 = (2 : ZMod 154779973) ^ (1574 + 1574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1574 * (2 : ZMod 154779973) ^ 1574) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 32892683 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 154779973) ^ 6298 = 22211378 := by
        calc
          (2 : ZMod 154779973) ^ 6298 = (2 : ZMod 154779973) ^ (3149 + 3149) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 3149 * (2 : ZMod 154779973) ^ 3149 := by rw [pow_add]
          _ = 22211378 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 154779973) ^ 12596 = 91058603 := by
        calc
          (2 : ZMod 154779973) ^ 12596 = (2 : ZMod 154779973) ^ (6298 + 6298) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 6298 * (2 : ZMod 154779973) ^ 6298 := by rw [pow_add]
          _ = 91058603 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 154779973) ^ 25192 = 2420104 := by
        calc
          (2 : ZMod 154779973) ^ 25192 = (2 : ZMod 154779973) ^ (12596 + 12596) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 12596 * (2 : ZMod 154779973) ^ 12596 := by rw [pow_add]
          _ = 2420104 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 154779973) ^ 50384 = 29192496 := by
        calc
          (2 : ZMod 154779973) ^ 50384 = (2 : ZMod 154779973) ^ (25192 + 25192) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 25192 * (2 : ZMod 154779973) ^ 25192 := by rw [pow_add]
          _ = 29192496 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 154779973) ^ 100768 = 7609100 := by
        calc
          (2 : ZMod 154779973) ^ 100768 = (2 : ZMod 154779973) ^ (50384 + 50384) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 50384 * (2 : ZMod 154779973) ^ 50384 := by rw [pow_add]
          _ = 7609100 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 154779973) ^ 201536 = 13089863 := by
        calc
          (2 : ZMod 154779973) ^ 201536 = (2 : ZMod 154779973) ^ (100768 + 100768) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 100768 * (2 : ZMod 154779973) ^ 100768 := by rw [pow_add]
          _ = 13089863 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 154779973) ^ 403072 = 142428282 := by
        calc
          (2 : ZMod 154779973) ^ 403072 = (2 : ZMod 154779973) ^ (201536 + 201536) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 201536 * (2 : ZMod 154779973) ^ 201536 := by rw [pow_add]
          _ = 142428282 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 154779973) ^ 806145 = 100525925 := by
        calc
          (2 : ZMod 154779973) ^ 806145 = (2 : ZMod 154779973) ^ (403072 + 403072 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 403072 * (2 : ZMod 154779973) ^ 403072) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 100525925 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 154779973) ^ 1612291 = 110468374 := by
        calc
          (2 : ZMod 154779973) ^ 1612291 = (2 : ZMod 154779973) ^ (806145 + 806145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 806145 * (2 : ZMod 154779973) ^ 806145) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 110468374 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 154779973) ^ 3224582 = 118535129 := by
        calc
          (2 : ZMod 154779973) ^ 3224582 = (2 : ZMod 154779973) ^ (1612291 + 1612291) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 1612291 * (2 : ZMod 154779973) ^ 1612291 := by rw [pow_add]
          _ = 118535129 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 154779973) ^ 6449165 = 83451458 := by
        calc
          (2 : ZMod 154779973) ^ 6449165 = (2 : ZMod 154779973) ^ (3224582 + 3224582 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 3224582 * (2 : ZMod 154779973) ^ 3224582) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 83451458 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 154779973) ^ 12898331 = 75239050 := by
        calc
          (2 : ZMod 154779973) ^ 12898331 = (2 : ZMod 154779973) ^ (6449165 + 6449165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 6449165 * (2 : ZMod 154779973) ^ 6449165) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 75239050 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 154779973) ^ 25796662 = 115739069 := by
        calc
          (2 : ZMod 154779973) ^ 25796662 = (2 : ZMod 154779973) ^ (12898331 + 12898331) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 12898331 * (2 : ZMod 154779973) ^ 12898331 := by rw [pow_add]
          _ = 115739069 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 154779973) ^ 51593324 = 115739068 := by
        calc
          (2 : ZMod 154779973) ^ 51593324 = (2 : ZMod 154779973) ^ (25796662 + 25796662) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 25796662 * (2 : ZMod 154779973) ^ 25796662 := by rw [pow_add]
          _ = 115739068 := by rw [factor_1_24]; decide
      change (2 : ZMod 154779973) ^ 51593324 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (2 : ZMod 154779973) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 154779973) ^ 3 = 8 := by
        calc
          (2 : ZMod 154779973) ^ 3 = (2 : ZMod 154779973) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1 * (2 : ZMod 154779973) ^ 1) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 154779973) ^ 6 = 64 := by
        calc
          (2 : ZMod 154779973) ^ 6 = (2 : ZMod 154779973) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 3 * (2 : ZMod 154779973) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 154779973) ^ 12 = 4096 := by
        calc
          (2 : ZMod 154779973) ^ 12 = (2 : ZMod 154779973) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 6 * (2 : ZMod 154779973) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 154779973) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 154779973) ^ 25 = (2 : ZMod 154779973) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 12 * (2 : ZMod 154779973) ^ 12) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 154779973) ^ 51 = 92731832 := by
        calc
          (2 : ZMod 154779973) ^ 51 = (2 : ZMod 154779973) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 25 * (2 : ZMod 154779973) ^ 25) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 92731832 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 154779973) ^ 102 = 137069453 := by
        calc
          (2 : ZMod 154779973) ^ 102 = (2 : ZMod 154779973) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 51 * (2 : ZMod 154779973) ^ 51 := by rw [pow_add]
          _ = 137069453 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 154779973) ^ 205 = 104192097 := by
        calc
          (2 : ZMod 154779973) ^ 205 = (2 : ZMod 154779973) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 102 * (2 : ZMod 154779973) ^ 102) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 104192097 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 154779973) ^ 410 = 41149565 := by
        calc
          (2 : ZMod 154779973) ^ 410 = (2 : ZMod 154779973) ^ (205 + 205) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 205 * (2 : ZMod 154779973) ^ 205 := by rw [pow_add]
          _ = 41149565 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 154779973) ^ 821 = 127316263 := by
        calc
          (2 : ZMod 154779973) ^ 821 = (2 : ZMod 154779973) ^ (410 + 410 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 410 * (2 : ZMod 154779973) ^ 410) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 127316263 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 154779973) ^ 1642 = 21357287 := by
        calc
          (2 : ZMod 154779973) ^ 1642 = (2 : ZMod 154779973) ^ (821 + 821) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 821 * (2 : ZMod 154779973) ^ 821 := by rw [pow_add]
          _ = 21357287 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 154779973) ^ 3285 = 136777712 := by
        calc
          (2 : ZMod 154779973) ^ 3285 = (2 : ZMod 154779973) ^ (1642 + 1642 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 1642 * (2 : ZMod 154779973) ^ 1642) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 136777712 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 154779973) ^ 6571 = 150870495 := by
        calc
          (2 : ZMod 154779973) ^ 6571 = (2 : ZMod 154779973) ^ (3285 + 3285 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 3285 * (2 : ZMod 154779973) ^ 3285) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 150870495 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 154779973) ^ 13143 = 75257279 := by
        calc
          (2 : ZMod 154779973) ^ 13143 = (2 : ZMod 154779973) ^ (6571 + 6571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 6571 * (2 : ZMod 154779973) ^ 6571) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 75257279 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 154779973) ^ 26287 = 76597970 := by
        calc
          (2 : ZMod 154779973) ^ 26287 = (2 : ZMod 154779973) ^ (13143 + 13143 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 13143 * (2 : ZMod 154779973) ^ 13143) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 76597970 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 154779973) ^ 52574 = 82990683 := by
        calc
          (2 : ZMod 154779973) ^ 52574 = (2 : ZMod 154779973) ^ (26287 + 26287) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 26287 * (2 : ZMod 154779973) ^ 26287 := by rw [pow_add]
          _ = 82990683 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 154779973) ^ 105149 = 106523878 := by
        calc
          (2 : ZMod 154779973) ^ 105149 = (2 : ZMod 154779973) ^ (52574 + 52574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 52574 * (2 : ZMod 154779973) ^ 52574) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 106523878 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 154779973) ^ 210298 = 95841568 := by
        calc
          (2 : ZMod 154779973) ^ 210298 = (2 : ZMod 154779973) ^ (105149 + 105149) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 105149 * (2 : ZMod 154779973) ^ 105149 := by rw [pow_add]
          _ = 95841568 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 154779973) ^ 420597 = 119233047 := by
        calc
          (2 : ZMod 154779973) ^ 420597 = (2 : ZMod 154779973) ^ (210298 + 210298 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 210298 * (2 : ZMod 154779973) ^ 210298) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 119233047 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 154779973) ^ 841195 = 53861074 := by
        calc
          (2 : ZMod 154779973) ^ 841195 = (2 : ZMod 154779973) ^ (420597 + 420597 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 420597 * (2 : ZMod 154779973) ^ 420597) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 53861074 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 154779973) ^ 1682391 = 58719961 := by
        calc
          (2 : ZMod 154779973) ^ 1682391 = (2 : ZMod 154779973) ^ (841195 + 841195 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 841195 * (2 : ZMod 154779973) ^ 841195) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 58719961 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 154779973) ^ 3364782 = 51760575 := by
        calc
          (2 : ZMod 154779973) ^ 3364782 = (2 : ZMod 154779973) ^ (1682391 + 1682391) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 1682391 * (2 : ZMod 154779973) ^ 1682391 := by rw [pow_add]
          _ = 51760575 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 154779973) ^ 6729564 = 146785910 := by
        calc
          (2 : ZMod 154779973) ^ 6729564 = (2 : ZMod 154779973) ^ (3364782 + 3364782) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 3364782 * (2 : ZMod 154779973) ^ 3364782 := by rw [pow_add]
          _ = 146785910 := by rw [factor_2_21]; decide
      change (2 : ZMod 154779973) ^ 6729564 ≠ 1
      rw [factor_2_22]
      decide
    ·
      have factor_3_0 : (2 : ZMod 154779973) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 154779973) ^ 2 = 4 := by
        calc
          (2 : ZMod 154779973) ^ 2 = (2 : ZMod 154779973) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 1 * (2 : ZMod 154779973) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 154779973) ^ 4 = 16 := by
        calc
          (2 : ZMod 154779973) ^ 4 = (2 : ZMod 154779973) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 2 * (2 : ZMod 154779973) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 154779973) ^ 8 = 256 := by
        calc
          (2 : ZMod 154779973) ^ 8 = (2 : ZMod 154779973) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 4 * (2 : ZMod 154779973) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 154779973) ^ 17 = 131072 := by
        calc
          (2 : ZMod 154779973) ^ 17 = (2 : ZMod 154779973) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 8 * (2 : ZMod 154779973) ^ 8) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 154779973) ^ 34 = 154072154 := by
        calc
          (2 : ZMod 154779973) ^ 34 = (2 : ZMod 154779973) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 17 * (2 : ZMod 154779973) ^ 17 := by rw [pow_add]
          _ = 154072154 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 154779973) ^ 69 = 124708293 := by
        calc
          (2 : ZMod 154779973) ^ 69 = (2 : ZMod 154779973) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = ((2 : ZMod 154779973) ^ 34 * (2 : ZMod 154779973) ^ 34) * (2 : ZMod 154779973) := by rw [pow_succ, pow_add]
          _ = 124708293 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 154779973) ^ 138 = 76270575 := by
        calc
          (2 : ZMod 154779973) ^ 138 = (2 : ZMod 154779973) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 69 * (2 : ZMod 154779973) ^ 69 := by rw [pow_add]
          _ = 76270575 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 154779973) ^ 276 = 99529904 := by
        calc
          (2 : ZMod 154779973) ^ 276 = (2 : ZMod 154779973) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (2 : ZMod 154779973) ^ n) (by norm_num)
          _ = (2 : ZMod 154779973) ^ 138 * (2 : ZMod 154779973) ^ 138 := by rw [pow_add]
          _ = 99529904 := by rw [factor_3_7]; decide
      change (2 : ZMod 154779973) ^ 276 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_154779973

end TotientTailPeriodKiller
end Erdos249257
