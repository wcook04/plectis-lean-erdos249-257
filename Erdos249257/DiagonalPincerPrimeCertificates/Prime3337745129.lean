import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3337745129 : Nat.Prime 3337745129 := by
  apply lucas_primality 3337745129 (3 : ZMod 3337745129)
  ·
      have fermat_0 : (3 : ZMod 3337745129) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 3337745129) ^ 3 = 27 := by
        calc
          (3 : ZMod 3337745129) ^ 3 = (3 : ZMod 3337745129) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 1 * (3 : ZMod 3337745129) ^ 1) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 3337745129) ^ 6 = 729 := by
        calc
          (3 : ZMod 3337745129) ^ 6 = (3 : ZMod 3337745129) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 3 * (3 : ZMod 3337745129) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 3337745129) ^ 12 = 531441 := by
        calc
          (3 : ZMod 3337745129) ^ 12 = (3 : ZMod 3337745129) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6 * (3 : ZMod 3337745129) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 3337745129) ^ 24 = 2058945645 := by
        calc
          (3 : ZMod 3337745129) ^ 24 = (3 : ZMod 3337745129) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 12 * (3 : ZMod 3337745129) ^ 12 := by rw [pow_add]
          _ = 2058945645 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 3337745129) ^ 49 = 61136023 := by
        calc
          (3 : ZMod 3337745129) ^ 49 = (3 : ZMod 3337745129) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 24 * (3 : ZMod 3337745129) ^ 24) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 61136023 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 3337745129) ^ 99 = 2249681342 := by
        calc
          (3 : ZMod 3337745129) ^ 99 = (3 : ZMod 3337745129) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 49 * (3 : ZMod 3337745129) ^ 49) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2249681342 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 3337745129) ^ 198 = 1005016317 := by
        calc
          (3 : ZMod 3337745129) ^ 198 = (3 : ZMod 3337745129) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 99 * (3 : ZMod 3337745129) ^ 99 := by rw [pow_add]
          _ = 1005016317 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 3337745129) ^ 397 = 1662736449 := by
        calc
          (3 : ZMod 3337745129) ^ 397 = (3 : ZMod 3337745129) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 198 * (3 : ZMod 3337745129) ^ 198) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1662736449 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 3337745129) ^ 795 = 604068685 := by
        calc
          (3 : ZMod 3337745129) ^ 795 = (3 : ZMod 3337745129) ^ (397 + 397 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 397 * (3 : ZMod 3337745129) ^ 397) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 604068685 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 3337745129) ^ 1591 = 3286563965 := by
        calc
          (3 : ZMod 3337745129) ^ 1591 = (3 : ZMod 3337745129) ^ (795 + 795 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 795 * (3 : ZMod 3337745129) ^ 795) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 3286563965 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 3337745129) ^ 3183 = 652681412 := by
        calc
          (3 : ZMod 3337745129) ^ 3183 = (3 : ZMod 3337745129) ^ (1591 + 1591 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 1591 * (3 : ZMod 3337745129) ^ 1591) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 652681412 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 3337745129) ^ 6366 = 2567349679 := by
        calc
          (3 : ZMod 3337745129) ^ 6366 = (3 : ZMod 3337745129) ^ (3183 + 3183) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 3183 * (3 : ZMod 3337745129) ^ 3183 := by rw [pow_add]
          _ = 2567349679 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 3337745129) ^ 12732 = 2030238416 := by
        calc
          (3 : ZMod 3337745129) ^ 12732 = (3 : ZMod 3337745129) ^ (6366 + 6366) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6366 * (3 : ZMod 3337745129) ^ 6366 := by rw [pow_add]
          _ = 2030238416 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 3337745129) ^ 25464 = 1580168441 := by
        calc
          (3 : ZMod 3337745129) ^ 25464 = (3 : ZMod 3337745129) ^ (12732 + 12732) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 12732 * (3 : ZMod 3337745129) ^ 12732 := by rw [pow_add]
          _ = 1580168441 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 3337745129) ^ 50929 = 893674788 := by
        calc
          (3 : ZMod 3337745129) ^ 50929 = (3 : ZMod 3337745129) ^ (25464 + 25464 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 25464 * (3 : ZMod 3337745129) ^ 25464) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 893674788 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 3337745129) ^ 101859 = 795674028 := by
        calc
          (3 : ZMod 3337745129) ^ 101859 = (3 : ZMod 3337745129) ^ (50929 + 50929 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 50929 * (3 : ZMod 3337745129) ^ 50929) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 795674028 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 3337745129) ^ 203719 = 91329136 := by
        calc
          (3 : ZMod 3337745129) ^ 203719 = (3 : ZMod 3337745129) ^ (101859 + 101859 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 101859 * (3 : ZMod 3337745129) ^ 101859) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 91329136 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 3337745129) ^ 407439 = 1406093165 := by
        calc
          (3 : ZMod 3337745129) ^ 407439 = (3 : ZMod 3337745129) ^ (203719 + 203719 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 203719 * (3 : ZMod 3337745129) ^ 203719) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1406093165 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 3337745129) ^ 814879 = 1981795198 := by
        calc
          (3 : ZMod 3337745129) ^ 814879 = (3 : ZMod 3337745129) ^ (407439 + 407439 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 407439 * (3 : ZMod 3337745129) ^ 407439) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1981795198 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 3337745129) ^ 1629758 = 26086793 := by
        calc
          (3 : ZMod 3337745129) ^ 1629758 = (3 : ZMod 3337745129) ^ (814879 + 814879) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 814879 * (3 : ZMod 3337745129) ^ 814879 := by rw [pow_add]
          _ = 26086793 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 3337745129) ^ 3259516 = 1265653555 := by
        calc
          (3 : ZMod 3337745129) ^ 3259516 = (3 : ZMod 3337745129) ^ (1629758 + 1629758) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 1629758 * (3 : ZMod 3337745129) ^ 1629758 := by rw [pow_add]
          _ = 1265653555 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 3337745129) ^ 6519033 = 1455430282 := by
        calc
          (3 : ZMod 3337745129) ^ 6519033 = (3 : ZMod 3337745129) ^ (3259516 + 3259516 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 3259516 * (3 : ZMod 3337745129) ^ 3259516) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1455430282 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 3337745129) ^ 13038066 = 2905704660 := by
        calc
          (3 : ZMod 3337745129) ^ 13038066 = (3 : ZMod 3337745129) ^ (6519033 + 6519033) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6519033 * (3 : ZMod 3337745129) ^ 6519033 := by rw [pow_add]
          _ = 2905704660 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 3337745129) ^ 26076133 = 2444348561 := by
        calc
          (3 : ZMod 3337745129) ^ 26076133 = (3 : ZMod 3337745129) ^ (13038066 + 13038066 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 13038066 * (3 : ZMod 3337745129) ^ 13038066) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2444348561 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 3337745129) ^ 52152267 = 2062883620 := by
        calc
          (3 : ZMod 3337745129) ^ 52152267 = (3 : ZMod 3337745129) ^ (26076133 + 26076133 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 26076133 * (3 : ZMod 3337745129) ^ 26076133) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2062883620 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 3337745129) ^ 104304535 = 690821283 := by
        calc
          (3 : ZMod 3337745129) ^ 104304535 = (3 : ZMod 3337745129) ^ (52152267 + 52152267 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 52152267 * (3 : ZMod 3337745129) ^ 52152267) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 690821283 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 3337745129) ^ 208609070 = 2213080701 := by
        calc
          (3 : ZMod 3337745129) ^ 208609070 = (3 : ZMod 3337745129) ^ (104304535 + 104304535) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 104304535 * (3 : ZMod 3337745129) ^ 104304535 := by rw [pow_add]
          _ = 2213080701 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 3337745129) ^ 417218141 = 1781467467 := by
        calc
          (3 : ZMod 3337745129) ^ 417218141 = (3 : ZMod 3337745129) ^ (208609070 + 208609070 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 208609070 * (3 : ZMod 3337745129) ^ 208609070) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1781467467 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 3337745129) ^ 834436282 = 771853200 := by
        calc
          (3 : ZMod 3337745129) ^ 834436282 = (3 : ZMod 3337745129) ^ (417218141 + 417218141) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 417218141 * (3 : ZMod 3337745129) ^ 417218141 := by rw [pow_add]
          _ = 771853200 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 3337745129) ^ 1668872564 = 3337745128 := by
        calc
          (3 : ZMod 3337745129) ^ 1668872564 = (3 : ZMod 3337745129) ^ (834436282 + 834436282) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 834436282 * (3 : ZMod 3337745129) ^ 834436282 := by rw [pow_add]
          _ = 3337745128 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 3337745129) ^ 3337745128 = 1 := by
        calc
          (3 : ZMod 3337745129) ^ 3337745128 = (3 : ZMod 3337745129) ^ (1668872564 + 1668872564) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 1668872564 * (3 : ZMod 3337745129) ^ 1668872564 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (73, 1), (2039, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (73, 1), (2039, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod = 3337745129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 3337745129) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 3337745129) ^ 3 = 27 := by
        calc
          (3 : ZMod 3337745129) ^ 3 = (3 : ZMod 3337745129) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 1 * (3 : ZMod 3337745129) ^ 1) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 3337745129) ^ 6 = 729 := by
        calc
          (3 : ZMod 3337745129) ^ 6 = (3 : ZMod 3337745129) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 3 * (3 : ZMod 3337745129) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 3337745129) ^ 12 = 531441 := by
        calc
          (3 : ZMod 3337745129) ^ 12 = (3 : ZMod 3337745129) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6 * (3 : ZMod 3337745129) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 3337745129) ^ 24 = 2058945645 := by
        calc
          (3 : ZMod 3337745129) ^ 24 = (3 : ZMod 3337745129) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 12 * (3 : ZMod 3337745129) ^ 12 := by rw [pow_add]
          _ = 2058945645 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 3337745129) ^ 49 = 61136023 := by
        calc
          (3 : ZMod 3337745129) ^ 49 = (3 : ZMod 3337745129) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 24 * (3 : ZMod 3337745129) ^ 24) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 61136023 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 3337745129) ^ 99 = 2249681342 := by
        calc
          (3 : ZMod 3337745129) ^ 99 = (3 : ZMod 3337745129) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 49 * (3 : ZMod 3337745129) ^ 49) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2249681342 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 3337745129) ^ 198 = 1005016317 := by
        calc
          (3 : ZMod 3337745129) ^ 198 = (3 : ZMod 3337745129) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 99 * (3 : ZMod 3337745129) ^ 99 := by rw [pow_add]
          _ = 1005016317 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 3337745129) ^ 397 = 1662736449 := by
        calc
          (3 : ZMod 3337745129) ^ 397 = (3 : ZMod 3337745129) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 198 * (3 : ZMod 3337745129) ^ 198) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1662736449 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 3337745129) ^ 795 = 604068685 := by
        calc
          (3 : ZMod 3337745129) ^ 795 = (3 : ZMod 3337745129) ^ (397 + 397 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 397 * (3 : ZMod 3337745129) ^ 397) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 604068685 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 3337745129) ^ 1591 = 3286563965 := by
        calc
          (3 : ZMod 3337745129) ^ 1591 = (3 : ZMod 3337745129) ^ (795 + 795 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 795 * (3 : ZMod 3337745129) ^ 795) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 3286563965 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 3337745129) ^ 3183 = 652681412 := by
        calc
          (3 : ZMod 3337745129) ^ 3183 = (3 : ZMod 3337745129) ^ (1591 + 1591 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 1591 * (3 : ZMod 3337745129) ^ 1591) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 652681412 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 3337745129) ^ 6366 = 2567349679 := by
        calc
          (3 : ZMod 3337745129) ^ 6366 = (3 : ZMod 3337745129) ^ (3183 + 3183) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 3183 * (3 : ZMod 3337745129) ^ 3183 := by rw [pow_add]
          _ = 2567349679 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 3337745129) ^ 12732 = 2030238416 := by
        calc
          (3 : ZMod 3337745129) ^ 12732 = (3 : ZMod 3337745129) ^ (6366 + 6366) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6366 * (3 : ZMod 3337745129) ^ 6366 := by rw [pow_add]
          _ = 2030238416 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 3337745129) ^ 25464 = 1580168441 := by
        calc
          (3 : ZMod 3337745129) ^ 25464 = (3 : ZMod 3337745129) ^ (12732 + 12732) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 12732 * (3 : ZMod 3337745129) ^ 12732 := by rw [pow_add]
          _ = 1580168441 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 3337745129) ^ 50929 = 893674788 := by
        calc
          (3 : ZMod 3337745129) ^ 50929 = (3 : ZMod 3337745129) ^ (25464 + 25464 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 25464 * (3 : ZMod 3337745129) ^ 25464) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 893674788 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 3337745129) ^ 101859 = 795674028 := by
        calc
          (3 : ZMod 3337745129) ^ 101859 = (3 : ZMod 3337745129) ^ (50929 + 50929 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 50929 * (3 : ZMod 3337745129) ^ 50929) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 795674028 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 3337745129) ^ 203719 = 91329136 := by
        calc
          (3 : ZMod 3337745129) ^ 203719 = (3 : ZMod 3337745129) ^ (101859 + 101859 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 101859 * (3 : ZMod 3337745129) ^ 101859) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 91329136 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 3337745129) ^ 407439 = 1406093165 := by
        calc
          (3 : ZMod 3337745129) ^ 407439 = (3 : ZMod 3337745129) ^ (203719 + 203719 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 203719 * (3 : ZMod 3337745129) ^ 203719) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1406093165 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 3337745129) ^ 814879 = 1981795198 := by
        calc
          (3 : ZMod 3337745129) ^ 814879 = (3 : ZMod 3337745129) ^ (407439 + 407439 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 407439 * (3 : ZMod 3337745129) ^ 407439) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1981795198 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 3337745129) ^ 1629758 = 26086793 := by
        calc
          (3 : ZMod 3337745129) ^ 1629758 = (3 : ZMod 3337745129) ^ (814879 + 814879) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 814879 * (3 : ZMod 3337745129) ^ 814879 := by rw [pow_add]
          _ = 26086793 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 3337745129) ^ 3259516 = 1265653555 := by
        calc
          (3 : ZMod 3337745129) ^ 3259516 = (3 : ZMod 3337745129) ^ (1629758 + 1629758) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 1629758 * (3 : ZMod 3337745129) ^ 1629758 := by rw [pow_add]
          _ = 1265653555 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 3337745129) ^ 6519033 = 1455430282 := by
        calc
          (3 : ZMod 3337745129) ^ 6519033 = (3 : ZMod 3337745129) ^ (3259516 + 3259516 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 3259516 * (3 : ZMod 3337745129) ^ 3259516) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1455430282 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 3337745129) ^ 13038066 = 2905704660 := by
        calc
          (3 : ZMod 3337745129) ^ 13038066 = (3 : ZMod 3337745129) ^ (6519033 + 6519033) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6519033 * (3 : ZMod 3337745129) ^ 6519033 := by rw [pow_add]
          _ = 2905704660 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 3337745129) ^ 26076133 = 2444348561 := by
        calc
          (3 : ZMod 3337745129) ^ 26076133 = (3 : ZMod 3337745129) ^ (13038066 + 13038066 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 13038066 * (3 : ZMod 3337745129) ^ 13038066) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2444348561 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 3337745129) ^ 52152267 = 2062883620 := by
        calc
          (3 : ZMod 3337745129) ^ 52152267 = (3 : ZMod 3337745129) ^ (26076133 + 26076133 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 26076133 * (3 : ZMod 3337745129) ^ 26076133) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2062883620 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 3337745129) ^ 104304535 = 690821283 := by
        calc
          (3 : ZMod 3337745129) ^ 104304535 = (3 : ZMod 3337745129) ^ (52152267 + 52152267 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 52152267 * (3 : ZMod 3337745129) ^ 52152267) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 690821283 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 3337745129) ^ 208609070 = 2213080701 := by
        calc
          (3 : ZMod 3337745129) ^ 208609070 = (3 : ZMod 3337745129) ^ (104304535 + 104304535) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 104304535 * (3 : ZMod 3337745129) ^ 104304535 := by rw [pow_add]
          _ = 2213080701 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 3337745129) ^ 417218141 = 1781467467 := by
        calc
          (3 : ZMod 3337745129) ^ 417218141 = (3 : ZMod 3337745129) ^ (208609070 + 208609070 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 208609070 * (3 : ZMod 3337745129) ^ 208609070) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1781467467 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 3337745129) ^ 834436282 = 771853200 := by
        calc
          (3 : ZMod 3337745129) ^ 834436282 = (3 : ZMod 3337745129) ^ (417218141 + 417218141) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 417218141 * (3 : ZMod 3337745129) ^ 417218141 := by rw [pow_add]
          _ = 771853200 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 3337745129) ^ 1668872564 = 3337745128 := by
        calc
          (3 : ZMod 3337745129) ^ 1668872564 = (3 : ZMod 3337745129) ^ (834436282 + 834436282) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 834436282 * (3 : ZMod 3337745129) ^ 834436282 := by rw [pow_add]
          _ = 3337745128 := by rw [factor_0_29]; decide
      change (3 : ZMod 3337745129) ^ 1668872564 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (3 : ZMod 3337745129) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 3337745129) ^ 2 = 9 := by
        calc
          (3 : ZMod 3337745129) ^ 2 = (3 : ZMod 3337745129) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 1 * (3 : ZMod 3337745129) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 3337745129) ^ 5 = 243 := by
        calc
          (3 : ZMod 3337745129) ^ 5 = (3 : ZMod 3337745129) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 2 * (3 : ZMod 3337745129) ^ 2) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 3337745129) ^ 10 = 59049 := by
        calc
          (3 : ZMod 3337745129) ^ 10 = (3 : ZMod 3337745129) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 5 * (3 : ZMod 3337745129) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 3337745129) ^ 21 = 447117816 := by
        calc
          (3 : ZMod 3337745129) ^ 21 = (3 : ZMod 3337745129) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 10 * (3 : ZMod 3337745129) ^ 10) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 447117816 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 3337745129) ^ 43 = 265638345 := by
        calc
          (3 : ZMod 3337745129) ^ 43 = (3 : ZMod 3337745129) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 21 * (3 : ZMod 3337745129) ^ 21) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 265638345 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 3337745129) ^ 87 = 3197711798 := by
        calc
          (3 : ZMod 3337745129) ^ 87 = (3 : ZMod 3337745129) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 43 * (3 : ZMod 3337745129) ^ 43) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 3197711798 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 3337745129) ^ 174 = 1052197465 := by
        calc
          (3 : ZMod 3337745129) ^ 174 = (3 : ZMod 3337745129) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 87 * (3 : ZMod 3337745129) ^ 87 := by rw [pow_add]
          _ = 1052197465 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 3337745129) ^ 348 = 13224123 := by
        calc
          (3 : ZMod 3337745129) ^ 348 = (3 : ZMod 3337745129) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 174 * (3 : ZMod 3337745129) ^ 174 := by rw [pow_add]
          _ = 13224123 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 3337745129) ^ 697 = 2170236038 := by
        calc
          (3 : ZMod 3337745129) ^ 697 = (3 : ZMod 3337745129) ^ (348 + 348 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 348 * (3 : ZMod 3337745129) ^ 348) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2170236038 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 3337745129) ^ 1395 = 2525311301 := by
        calc
          (3 : ZMod 3337745129) ^ 1395 = (3 : ZMod 3337745129) ^ (697 + 697 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 697 * (3 : ZMod 3337745129) ^ 697) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2525311301 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 3337745129) ^ 2790 = 2899776677 := by
        calc
          (3 : ZMod 3337745129) ^ 2790 = (3 : ZMod 3337745129) ^ (1395 + 1395) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 1395 * (3 : ZMod 3337745129) ^ 1395 := by rw [pow_add]
          _ = 2899776677 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 3337745129) ^ 5581 = 2411340123 := by
        calc
          (3 : ZMod 3337745129) ^ 5581 = (3 : ZMod 3337745129) ^ (2790 + 2790 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 2790 * (3 : ZMod 3337745129) ^ 2790) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2411340123 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 3337745129) ^ 11162 = 922165828 := by
        calc
          (3 : ZMod 3337745129) ^ 11162 = (3 : ZMod 3337745129) ^ (5581 + 5581) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 5581 * (3 : ZMod 3337745129) ^ 5581 := by rw [pow_add]
          _ = 922165828 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 3337745129) ^ 22325 = 1289019952 := by
        calc
          (3 : ZMod 3337745129) ^ 22325 = (3 : ZMod 3337745129) ^ (11162 + 11162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 11162 * (3 : ZMod 3337745129) ^ 11162) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1289019952 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 3337745129) ^ 44650 = 1386503880 := by
        calc
          (3 : ZMod 3337745129) ^ 44650 = (3 : ZMod 3337745129) ^ (22325 + 22325) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 22325 * (3 : ZMod 3337745129) ^ 22325 := by rw [pow_add]
          _ = 1386503880 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 3337745129) ^ 89301 = 2464639839 := by
        calc
          (3 : ZMod 3337745129) ^ 89301 = (3 : ZMod 3337745129) ^ (44650 + 44650 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 44650 * (3 : ZMod 3337745129) ^ 44650) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2464639839 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 3337745129) ^ 178603 = 1474700097 := by
        calc
          (3 : ZMod 3337745129) ^ 178603 = (3 : ZMod 3337745129) ^ (89301 + 89301 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 89301 * (3 : ZMod 3337745129) ^ 89301) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1474700097 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 3337745129) ^ 357207 = 2857025751 := by
        calc
          (3 : ZMod 3337745129) ^ 357207 = (3 : ZMod 3337745129) ^ (178603 + 178603 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 178603 * (3 : ZMod 3337745129) ^ 178603) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2857025751 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 3337745129) ^ 714414 = 3294546713 := by
        calc
          (3 : ZMod 3337745129) ^ 714414 = (3 : ZMod 3337745129) ^ (357207 + 357207) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 357207 * (3 : ZMod 3337745129) ^ 357207 := by rw [pow_add]
          _ = 3294546713 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 3337745129) ^ 1428829 = 2986719080 := by
        calc
          (3 : ZMod 3337745129) ^ 1428829 = (3 : ZMod 3337745129) ^ (714414 + 714414 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 714414 * (3 : ZMod 3337745129) ^ 714414) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2986719080 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 3337745129) ^ 2857658 = 480142076 := by
        calc
          (3 : ZMod 3337745129) ^ 2857658 = (3 : ZMod 3337745129) ^ (1428829 + 1428829) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 1428829 * (3 : ZMod 3337745129) ^ 1428829 := by rw [pow_add]
          _ = 480142076 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 3337745129) ^ 5715317 = 1106234861 := by
        calc
          (3 : ZMod 3337745129) ^ 5715317 = (3 : ZMod 3337745129) ^ (2857658 + 2857658 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 2857658 * (3 : ZMod 3337745129) ^ 2857658) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1106234861 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 3337745129) ^ 11430634 = 725477947 := by
        calc
          (3 : ZMod 3337745129) ^ 11430634 = (3 : ZMod 3337745129) ^ (5715317 + 5715317) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 5715317 * (3 : ZMod 3337745129) ^ 5715317 := by rw [pow_add]
          _ = 725477947 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 3337745129) ^ 22861268 = 3108091479 := by
        calc
          (3 : ZMod 3337745129) ^ 22861268 = (3 : ZMod 3337745129) ^ (11430634 + 11430634) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 11430634 * (3 : ZMod 3337745129) ^ 11430634 := by rw [pow_add]
          _ = 3108091479 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 3337745129) ^ 45722536 = 70081446 := by
        calc
          (3 : ZMod 3337745129) ^ 45722536 = (3 : ZMod 3337745129) ^ (22861268 + 22861268) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 22861268 * (3 : ZMod 3337745129) ^ 22861268 := by rw [pow_add]
          _ = 70081446 := by rw [factor_1_24]; decide
      change (3 : ZMod 3337745129) ^ 45722536 ≠ 1
      rw [factor_1_25]
      decide
    ·
      have factor_2_0 : (3 : ZMod 3337745129) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 3337745129) ^ 3 = 27 := by
        calc
          (3 : ZMod 3337745129) ^ 3 = (3 : ZMod 3337745129) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 1 * (3 : ZMod 3337745129) ^ 1) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 3337745129) ^ 6 = 729 := by
        calc
          (3 : ZMod 3337745129) ^ 6 = (3 : ZMod 3337745129) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 3 * (3 : ZMod 3337745129) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 3337745129) ^ 12 = 531441 := by
        calc
          (3 : ZMod 3337745129) ^ 12 = (3 : ZMod 3337745129) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6 * (3 : ZMod 3337745129) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 3337745129) ^ 24 = 2058945645 := by
        calc
          (3 : ZMod 3337745129) ^ 24 = (3 : ZMod 3337745129) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 12 * (3 : ZMod 3337745129) ^ 12 := by rw [pow_add]
          _ = 2058945645 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 3337745129) ^ 49 = 61136023 := by
        calc
          (3 : ZMod 3337745129) ^ 49 = (3 : ZMod 3337745129) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 24 * (3 : ZMod 3337745129) ^ 24) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 61136023 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 3337745129) ^ 99 = 2249681342 := by
        calc
          (3 : ZMod 3337745129) ^ 99 = (3 : ZMod 3337745129) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 49 * (3 : ZMod 3337745129) ^ 49) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2249681342 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 3337745129) ^ 199 = 3015048951 := by
        calc
          (3 : ZMod 3337745129) ^ 199 = (3 : ZMod 3337745129) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 99 * (3 : ZMod 3337745129) ^ 99) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 3015048951 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 3337745129) ^ 399 = 1613647525 := by
        calc
          (3 : ZMod 3337745129) ^ 399 = (3 : ZMod 3337745129) ^ (199 + 199 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 199 * (3 : ZMod 3337745129) ^ 199) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1613647525 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 3337745129) ^ 799 = 2201131679 := by
        calc
          (3 : ZMod 3337745129) ^ 799 = (3 : ZMod 3337745129) ^ (399 + 399 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 399 * (3 : ZMod 3337745129) ^ 399) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2201131679 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 3337745129) ^ 1598 = 1550128718 := by
        calc
          (3 : ZMod 3337745129) ^ 1598 = (3 : ZMod 3337745129) ^ (799 + 799) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 799 * (3 : ZMod 3337745129) ^ 799 := by rw [pow_add]
          _ = 1550128718 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 3337745129) ^ 3197 = 1994260076 := by
        calc
          (3 : ZMod 3337745129) ^ 3197 = (3 : ZMod 3337745129) ^ (1598 + 1598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 1598 * (3 : ZMod 3337745129) ^ 1598) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1994260076 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 3337745129) ^ 6394 = 1350576225 := by
        calc
          (3 : ZMod 3337745129) ^ 6394 = (3 : ZMod 3337745129) ^ (3197 + 3197) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 3197 * (3 : ZMod 3337745129) ^ 3197 := by rw [pow_add]
          _ = 1350576225 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 3337745129) ^ 12788 = 1721264481 := by
        calc
          (3 : ZMod 3337745129) ^ 12788 = (3 : ZMod 3337745129) ^ (6394 + 6394) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 6394 * (3 : ZMod 3337745129) ^ 6394 := by rw [pow_add]
          _ = 1721264481 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 3337745129) ^ 25577 = 1656582075 := by
        calc
          (3 : ZMod 3337745129) ^ 25577 = (3 : ZMod 3337745129) ^ (12788 + 12788 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 12788 * (3 : ZMod 3337745129) ^ 12788) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1656582075 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 3337745129) ^ 51154 = 2304155304 := by
        calc
          (3 : ZMod 3337745129) ^ 51154 = (3 : ZMod 3337745129) ^ (25577 + 25577) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 25577 * (3 : ZMod 3337745129) ^ 25577 := by rw [pow_add]
          _ = 2304155304 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 3337745129) ^ 102309 = 1867048948 := by
        calc
          (3 : ZMod 3337745129) ^ 102309 = (3 : ZMod 3337745129) ^ (51154 + 51154 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 51154 * (3 : ZMod 3337745129) ^ 51154) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1867048948 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 3337745129) ^ 204619 = 2393533169 := by
        calc
          (3 : ZMod 3337745129) ^ 204619 = (3 : ZMod 3337745129) ^ (102309 + 102309 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 102309 * (3 : ZMod 3337745129) ^ 102309) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2393533169 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 3337745129) ^ 409238 = 2401894740 := by
        calc
          (3 : ZMod 3337745129) ^ 409238 = (3 : ZMod 3337745129) ^ (204619 + 204619) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 204619 * (3 : ZMod 3337745129) ^ 204619 := by rw [pow_add]
          _ = 2401894740 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 3337745129) ^ 818476 = 3144379982 := by
        calc
          (3 : ZMod 3337745129) ^ 818476 = (3 : ZMod 3337745129) ^ (409238 + 409238) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 409238 * (3 : ZMod 3337745129) ^ 409238 := by rw [pow_add]
          _ = 3144379982 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 3337745129) ^ 1636952 = 1603483196 := by
        calc
          (3 : ZMod 3337745129) ^ 1636952 = (3 : ZMod 3337745129) ^ (818476 + 818476) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 818476 * (3 : ZMod 3337745129) ^ 818476 := by rw [pow_add]
          _ = 1603483196 := by rw [factor_2_19]; decide
      change (3 : ZMod 3337745129) ^ 1636952 ≠ 1
      rw [factor_2_20]
      decide
    ·
      have factor_3_0 : (3 : ZMod 3337745129) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 3337745129) ^ 2 = 9 := by
        calc
          (3 : ZMod 3337745129) ^ 2 = (3 : ZMod 3337745129) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 1 * (3 : ZMod 3337745129) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 3337745129) ^ 4 = 81 := by
        calc
          (3 : ZMod 3337745129) ^ 4 = (3 : ZMod 3337745129) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 2 * (3 : ZMod 3337745129) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 3337745129) ^ 9 = 19683 := by
        calc
          (3 : ZMod 3337745129) ^ 9 = (3 : ZMod 3337745129) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 4 * (3 : ZMod 3337745129) ^ 4) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 3337745129) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 3337745129) ^ 18 = (3 : ZMod 3337745129) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 9 * (3 : ZMod 3337745129) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 3337745129) ^ 36 = 1822374633 := by
        calc
          (3 : ZMod 3337745129) ^ 36 = (3 : ZMod 3337745129) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 18 * (3 : ZMod 3337745129) ^ 18 := by rw [pow_add]
          _ = 1822374633 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 3337745129) ^ 72 = 2368519201 := by
        calc
          (3 : ZMod 3337745129) ^ 72 = (3 : ZMod 3337745129) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 36 * (3 : ZMod 3337745129) ^ 36 := by rw [pow_add]
          _ = 2368519201 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 3337745129) ^ 145 = 3062281342 := by
        calc
          (3 : ZMod 3337745129) ^ 145 = (3 : ZMod 3337745129) ^ (72 + 72 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 72 * (3 : ZMod 3337745129) ^ 72) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 3062281342 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 3337745129) ^ 290 = 185695369 := by
        calc
          (3 : ZMod 3337745129) ^ 290 = (3 : ZMod 3337745129) ^ (145 + 145) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 145 * (3 : ZMod 3337745129) ^ 145 := by rw [pow_add]
          _ = 185695369 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 3337745129) ^ 581 = 5340595 := by
        calc
          (3 : ZMod 3337745129) ^ 581 = (3 : ZMod 3337745129) ^ (290 + 290 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 290 * (3 : ZMod 3337745129) ^ 290) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 5340595 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 3337745129) ^ 1162 = 922826720 := by
        calc
          (3 : ZMod 3337745129) ^ 1162 = (3 : ZMod 3337745129) ^ (581 + 581) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 581 * (3 : ZMod 3337745129) ^ 581 := by rw [pow_add]
          _ = 922826720 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 3337745129) ^ 2325 = 1933520076 := by
        calc
          (3 : ZMod 3337745129) ^ 2325 = (3 : ZMod 3337745129) ^ (1162 + 1162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 1162 * (3 : ZMod 3337745129) ^ 1162) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1933520076 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 3337745129) ^ 4651 = 2559945055 := by
        calc
          (3 : ZMod 3337745129) ^ 4651 = (3 : ZMod 3337745129) ^ (2325 + 2325 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 2325 * (3 : ZMod 3337745129) ^ 2325) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 2559945055 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 3337745129) ^ 9302 = 1694858508 := by
        calc
          (3 : ZMod 3337745129) ^ 9302 = (3 : ZMod 3337745129) ^ (4651 + 4651) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 4651 * (3 : ZMod 3337745129) ^ 4651 := by rw [pow_add]
          _ = 1694858508 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 3337745129) ^ 18605 = 922341728 := by
        calc
          (3 : ZMod 3337745129) ^ 18605 = (3 : ZMod 3337745129) ^ (9302 + 9302 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 9302 * (3 : ZMod 3337745129) ^ 9302) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 922341728 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 3337745129) ^ 37211 = 1367292430 := by
        calc
          (3 : ZMod 3337745129) ^ 37211 = (3 : ZMod 3337745129) ^ (18605 + 18605 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 18605 * (3 : ZMod 3337745129) ^ 18605) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1367292430 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 3337745129) ^ 74423 = 919765757 := by
        calc
          (3 : ZMod 3337745129) ^ 74423 = (3 : ZMod 3337745129) ^ (37211 + 37211 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 37211 * (3 : ZMod 3337745129) ^ 37211) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 919765757 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 3337745129) ^ 148847 = 1511259946 := by
        calc
          (3 : ZMod 3337745129) ^ 148847 = (3 : ZMod 3337745129) ^ (74423 + 74423 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = ((3 : ZMod 3337745129) ^ 74423 * (3 : ZMod 3337745129) ^ 74423) * (3 : ZMod 3337745129) := by rw [pow_succ, pow_add]
          _ = 1511259946 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 3337745129) ^ 297694 = 1136735830 := by
        calc
          (3 : ZMod 3337745129) ^ 297694 = (3 : ZMod 3337745129) ^ (148847 + 148847) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 148847 * (3 : ZMod 3337745129) ^ 148847 := by rw [pow_add]
          _ = 1136735830 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 3337745129) ^ 595388 = 2965277581 := by
        calc
          (3 : ZMod 3337745129) ^ 595388 = (3 : ZMod 3337745129) ^ (297694 + 297694) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 297694 * (3 : ZMod 3337745129) ^ 297694 := by rw [pow_add]
          _ = 2965277581 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 3337745129) ^ 1190776 = 3084592743 := by
        calc
          (3 : ZMod 3337745129) ^ 1190776 = (3 : ZMod 3337745129) ^ (595388 + 595388) :=
            congrArg (fun n : ℕ => (3 : ZMod 3337745129) ^ n) (by norm_num)
          _ = (3 : ZMod 3337745129) ^ 595388 * (3 : ZMod 3337745129) ^ 595388 := by rw [pow_add]
          _ = 3084592743 := by rw [factor_3_19]; decide
      change (3 : ZMod 3337745129) ^ 1190776 ≠ 1
      rw [factor_3_20]
      decide

#print axioms prime_lucas_3337745129

end TotientTailPeriodKiller
end Erdos249257
