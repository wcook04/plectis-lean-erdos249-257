import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1918069369 : Nat.Prime 1918069369 := by
  apply lucas_primality 1918069369 (7 : ZMod 1918069369)
  ·
      have fermat_0 : (7 : ZMod 1918069369) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 1918069369) ^ 3 = 343 := by
        calc
          (7 : ZMod 1918069369) ^ 3 = (7 : ZMod 1918069369) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 1 * (7 : ZMod 1918069369) ^ 1) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 1918069369) ^ 7 = 823543 := by
        calc
          (7 : ZMod 1918069369) ^ 7 = (7 : ZMod 1918069369) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 3 * (7 : ZMod 1918069369) ^ 3) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 1918069369) ^ 14 = 1144585592 := by
        calc
          (7 : ZMod 1918069369) ^ 14 = (7 : ZMod 1918069369) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 7 * (7 : ZMod 1918069369) ^ 7 := by rw [pow_add]
          _ = 1144585592 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 1918069369) ^ 28 = 772498066 := by
        calc
          (7 : ZMod 1918069369) ^ 28 = (7 : ZMod 1918069369) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 14 * (7 : ZMod 1918069369) ^ 14 := by rw [pow_add]
          _ = 772498066 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 1918069369) ^ 57 = 1632177687 := by
        calc
          (7 : ZMod 1918069369) ^ 57 = (7 : ZMod 1918069369) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 28 * (7 : ZMod 1918069369) ^ 28) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1632177687 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 1918069369) ^ 114 = 614622632 := by
        calc
          (7 : ZMod 1918069369) ^ 114 = (7 : ZMod 1918069369) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 57 * (7 : ZMod 1918069369) ^ 57 := by rw [pow_add]
          _ = 614622632 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 1918069369) ^ 228 = 660711843 := by
        calc
          (7 : ZMod 1918069369) ^ 228 = (7 : ZMod 1918069369) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 114 * (7 : ZMod 1918069369) ^ 114 := by rw [pow_add]
          _ = 660711843 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 1918069369) ^ 457 = 1318038320 := by
        calc
          (7 : ZMod 1918069369) ^ 457 = (7 : ZMod 1918069369) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 228 * (7 : ZMod 1918069369) ^ 228) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1318038320 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 1918069369) ^ 914 = 1183174944 := by
        calc
          (7 : ZMod 1918069369) ^ 914 = (7 : ZMod 1918069369) ^ (457 + 457) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 457 * (7 : ZMod 1918069369) ^ 457 := by rw [pow_add]
          _ = 1183174944 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 1918069369) ^ 1829 = 1666485491 := by
        calc
          (7 : ZMod 1918069369) ^ 1829 = (7 : ZMod 1918069369) ^ (914 + 914 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 914 * (7 : ZMod 1918069369) ^ 914) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1666485491 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 1918069369) ^ 3658 = 1757182493 := by
        calc
          (7 : ZMod 1918069369) ^ 3658 = (7 : ZMod 1918069369) ^ (1829 + 1829) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1829 * (7 : ZMod 1918069369) ^ 1829 := by rw [pow_add]
          _ = 1757182493 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 1918069369) ^ 7316 = 975713251 := by
        calc
          (7 : ZMod 1918069369) ^ 7316 = (7 : ZMod 1918069369) ^ (3658 + 3658) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 3658 * (7 : ZMod 1918069369) ^ 3658 := by rw [pow_add]
          _ = 975713251 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 1918069369) ^ 14633 = 437642367 := by
        calc
          (7 : ZMod 1918069369) ^ 14633 = (7 : ZMod 1918069369) ^ (7316 + 7316 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 7316 * (7 : ZMod 1918069369) ^ 7316) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 437642367 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 1918069369) ^ 29267 = 1166575651 := by
        calc
          (7 : ZMod 1918069369) ^ 29267 = (7 : ZMod 1918069369) ^ (14633 + 14633 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 14633 * (7 : ZMod 1918069369) ^ 14633) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1166575651 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 1918069369) ^ 58534 = 918709926 := by
        calc
          (7 : ZMod 1918069369) ^ 58534 = (7 : ZMod 1918069369) ^ (29267 + 29267) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 29267 * (7 : ZMod 1918069369) ^ 29267 := by rw [pow_add]
          _ = 918709926 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 1918069369) ^ 117069 = 1144290784 := by
        calc
          (7 : ZMod 1918069369) ^ 117069 = (7 : ZMod 1918069369) ^ (58534 + 58534 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 58534 * (7 : ZMod 1918069369) ^ 58534) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1144290784 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 1918069369) ^ 234139 = 1077411420 := by
        calc
          (7 : ZMod 1918069369) ^ 234139 = (7 : ZMod 1918069369) ^ (117069 + 117069 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 117069 * (7 : ZMod 1918069369) ^ 117069) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1077411420 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 1918069369) ^ 468278 = 651385728 := by
        calc
          (7 : ZMod 1918069369) ^ 468278 = (7 : ZMod 1918069369) ^ (234139 + 234139) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 234139 * (7 : ZMod 1918069369) ^ 234139 := by rw [pow_add]
          _ = 651385728 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 1918069369) ^ 936557 = 1859985325 := by
        calc
          (7 : ZMod 1918069369) ^ 936557 = (7 : ZMod 1918069369) ^ (468278 + 468278 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 468278 * (7 : ZMod 1918069369) ^ 468278) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1859985325 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 1918069369) ^ 1873114 = 657970659 := by
        calc
          (7 : ZMod 1918069369) ^ 1873114 = (7 : ZMod 1918069369) ^ (936557 + 936557) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 936557 * (7 : ZMod 1918069369) ^ 936557 := by rw [pow_add]
          _ = 657970659 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 1918069369) ^ 3746229 = 1036140718 := by
        calc
          (7 : ZMod 1918069369) ^ 3746229 = (7 : ZMod 1918069369) ^ (1873114 + 1873114 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 1873114 * (7 : ZMod 1918069369) ^ 1873114) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1036140718 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 1918069369) ^ 7492458 = 39103668 := by
        calc
          (7 : ZMod 1918069369) ^ 7492458 = (7 : ZMod 1918069369) ^ (3746229 + 3746229) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 3746229 * (7 : ZMod 1918069369) ^ 3746229 := by rw [pow_add]
          _ = 39103668 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 1918069369) ^ 14984916 = 441671210 := by
        calc
          (7 : ZMod 1918069369) ^ 14984916 = (7 : ZMod 1918069369) ^ (7492458 + 7492458) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 7492458 * (7 : ZMod 1918069369) ^ 7492458 := by rw [pow_add]
          _ = 441671210 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 1918069369) ^ 29969833 = 1453921387 := by
        calc
          (7 : ZMod 1918069369) ^ 29969833 = (7 : ZMod 1918069369) ^ (14984916 + 14984916 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 14984916 * (7 : ZMod 1918069369) ^ 14984916) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1453921387 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 1918069369) ^ 59939667 = 1110058621 := by
        calc
          (7 : ZMod 1918069369) ^ 59939667 = (7 : ZMod 1918069369) ^ (29969833 + 29969833 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 29969833 * (7 : ZMod 1918069369) ^ 29969833) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1110058621 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 1918069369) ^ 119879335 = 1629690530 := by
        calc
          (7 : ZMod 1918069369) ^ 119879335 = (7 : ZMod 1918069369) ^ (59939667 + 59939667 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 59939667 * (7 : ZMod 1918069369) ^ 59939667) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1629690530 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 1918069369) ^ 239758671 = 1713594293 := by
        calc
          (7 : ZMod 1918069369) ^ 239758671 = (7 : ZMod 1918069369) ^ (119879335 + 119879335 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 119879335 * (7 : ZMod 1918069369) ^ 119879335) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1713594293 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 1918069369) ^ 479517342 = 1698506835 := by
        calc
          (7 : ZMod 1918069369) ^ 479517342 = (7 : ZMod 1918069369) ^ (239758671 + 239758671) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 239758671 * (7 : ZMod 1918069369) ^ 239758671 := by rw [pow_add]
          _ = 1698506835 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 1918069369) ^ 959034684 = 1918069368 := by
        calc
          (7 : ZMod 1918069369) ^ 959034684 = (7 : ZMod 1918069369) ^ (479517342 + 479517342) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 479517342 * (7 : ZMod 1918069369) ^ 479517342 := by rw [pow_add]
          _ = 1918069368 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 1918069369) ^ 1918069368 = 1 := by
        calc
          (7 : ZMod 1918069369) ^ 1918069368 = (7 : ZMod 1918069369) ^ (959034684 + 959034684) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 959034684 * (7 : ZMod 1918069369) ^ 959034684 := by rw [pow_add]
          _ = 1 := by rw [fermat_29]; decide
      simpa using fermat_30
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (191, 1), (418427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (191, 1), (418427, 1)] : List FactorBlock).map factorBlockValue).prod = 1918069369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 1918069369) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 1918069369) ^ 3 = 343 := by
        calc
          (7 : ZMod 1918069369) ^ 3 = (7 : ZMod 1918069369) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 1 * (7 : ZMod 1918069369) ^ 1) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 1918069369) ^ 7 = 823543 := by
        calc
          (7 : ZMod 1918069369) ^ 7 = (7 : ZMod 1918069369) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 3 * (7 : ZMod 1918069369) ^ 3) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 1918069369) ^ 14 = 1144585592 := by
        calc
          (7 : ZMod 1918069369) ^ 14 = (7 : ZMod 1918069369) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 7 * (7 : ZMod 1918069369) ^ 7 := by rw [pow_add]
          _ = 1144585592 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 1918069369) ^ 28 = 772498066 := by
        calc
          (7 : ZMod 1918069369) ^ 28 = (7 : ZMod 1918069369) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 14 * (7 : ZMod 1918069369) ^ 14 := by rw [pow_add]
          _ = 772498066 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 1918069369) ^ 57 = 1632177687 := by
        calc
          (7 : ZMod 1918069369) ^ 57 = (7 : ZMod 1918069369) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 28 * (7 : ZMod 1918069369) ^ 28) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1632177687 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 1918069369) ^ 114 = 614622632 := by
        calc
          (7 : ZMod 1918069369) ^ 114 = (7 : ZMod 1918069369) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 57 * (7 : ZMod 1918069369) ^ 57 := by rw [pow_add]
          _ = 614622632 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 1918069369) ^ 228 = 660711843 := by
        calc
          (7 : ZMod 1918069369) ^ 228 = (7 : ZMod 1918069369) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 114 * (7 : ZMod 1918069369) ^ 114 := by rw [pow_add]
          _ = 660711843 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 1918069369) ^ 457 = 1318038320 := by
        calc
          (7 : ZMod 1918069369) ^ 457 = (7 : ZMod 1918069369) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 228 * (7 : ZMod 1918069369) ^ 228) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1318038320 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 1918069369) ^ 914 = 1183174944 := by
        calc
          (7 : ZMod 1918069369) ^ 914 = (7 : ZMod 1918069369) ^ (457 + 457) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 457 * (7 : ZMod 1918069369) ^ 457 := by rw [pow_add]
          _ = 1183174944 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 1918069369) ^ 1829 = 1666485491 := by
        calc
          (7 : ZMod 1918069369) ^ 1829 = (7 : ZMod 1918069369) ^ (914 + 914 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 914 * (7 : ZMod 1918069369) ^ 914) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1666485491 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 1918069369) ^ 3658 = 1757182493 := by
        calc
          (7 : ZMod 1918069369) ^ 3658 = (7 : ZMod 1918069369) ^ (1829 + 1829) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1829 * (7 : ZMod 1918069369) ^ 1829 := by rw [pow_add]
          _ = 1757182493 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 1918069369) ^ 7316 = 975713251 := by
        calc
          (7 : ZMod 1918069369) ^ 7316 = (7 : ZMod 1918069369) ^ (3658 + 3658) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 3658 * (7 : ZMod 1918069369) ^ 3658 := by rw [pow_add]
          _ = 975713251 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 1918069369) ^ 14633 = 437642367 := by
        calc
          (7 : ZMod 1918069369) ^ 14633 = (7 : ZMod 1918069369) ^ (7316 + 7316 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 7316 * (7 : ZMod 1918069369) ^ 7316) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 437642367 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 1918069369) ^ 29267 = 1166575651 := by
        calc
          (7 : ZMod 1918069369) ^ 29267 = (7 : ZMod 1918069369) ^ (14633 + 14633 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 14633 * (7 : ZMod 1918069369) ^ 14633) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1166575651 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 1918069369) ^ 58534 = 918709926 := by
        calc
          (7 : ZMod 1918069369) ^ 58534 = (7 : ZMod 1918069369) ^ (29267 + 29267) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 29267 * (7 : ZMod 1918069369) ^ 29267 := by rw [pow_add]
          _ = 918709926 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 1918069369) ^ 117069 = 1144290784 := by
        calc
          (7 : ZMod 1918069369) ^ 117069 = (7 : ZMod 1918069369) ^ (58534 + 58534 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 58534 * (7 : ZMod 1918069369) ^ 58534) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1144290784 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 1918069369) ^ 234139 = 1077411420 := by
        calc
          (7 : ZMod 1918069369) ^ 234139 = (7 : ZMod 1918069369) ^ (117069 + 117069 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 117069 * (7 : ZMod 1918069369) ^ 117069) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1077411420 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 1918069369) ^ 468278 = 651385728 := by
        calc
          (7 : ZMod 1918069369) ^ 468278 = (7 : ZMod 1918069369) ^ (234139 + 234139) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 234139 * (7 : ZMod 1918069369) ^ 234139 := by rw [pow_add]
          _ = 651385728 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 1918069369) ^ 936557 = 1859985325 := by
        calc
          (7 : ZMod 1918069369) ^ 936557 = (7 : ZMod 1918069369) ^ (468278 + 468278 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 468278 * (7 : ZMod 1918069369) ^ 468278) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1859985325 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 1918069369) ^ 1873114 = 657970659 := by
        calc
          (7 : ZMod 1918069369) ^ 1873114 = (7 : ZMod 1918069369) ^ (936557 + 936557) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 936557 * (7 : ZMod 1918069369) ^ 936557 := by rw [pow_add]
          _ = 657970659 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 1918069369) ^ 3746229 = 1036140718 := by
        calc
          (7 : ZMod 1918069369) ^ 3746229 = (7 : ZMod 1918069369) ^ (1873114 + 1873114 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 1873114 * (7 : ZMod 1918069369) ^ 1873114) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1036140718 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 1918069369) ^ 7492458 = 39103668 := by
        calc
          (7 : ZMod 1918069369) ^ 7492458 = (7 : ZMod 1918069369) ^ (3746229 + 3746229) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 3746229 * (7 : ZMod 1918069369) ^ 3746229 := by rw [pow_add]
          _ = 39103668 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 1918069369) ^ 14984916 = 441671210 := by
        calc
          (7 : ZMod 1918069369) ^ 14984916 = (7 : ZMod 1918069369) ^ (7492458 + 7492458) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 7492458 * (7 : ZMod 1918069369) ^ 7492458 := by rw [pow_add]
          _ = 441671210 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 1918069369) ^ 29969833 = 1453921387 := by
        calc
          (7 : ZMod 1918069369) ^ 29969833 = (7 : ZMod 1918069369) ^ (14984916 + 14984916 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 14984916 * (7 : ZMod 1918069369) ^ 14984916) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1453921387 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 1918069369) ^ 59939667 = 1110058621 := by
        calc
          (7 : ZMod 1918069369) ^ 59939667 = (7 : ZMod 1918069369) ^ (29969833 + 29969833 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 29969833 * (7 : ZMod 1918069369) ^ 29969833) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1110058621 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 1918069369) ^ 119879335 = 1629690530 := by
        calc
          (7 : ZMod 1918069369) ^ 119879335 = (7 : ZMod 1918069369) ^ (59939667 + 59939667 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 59939667 * (7 : ZMod 1918069369) ^ 59939667) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1629690530 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 1918069369) ^ 239758671 = 1713594293 := by
        calc
          (7 : ZMod 1918069369) ^ 239758671 = (7 : ZMod 1918069369) ^ (119879335 + 119879335 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 119879335 * (7 : ZMod 1918069369) ^ 119879335) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1713594293 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 1918069369) ^ 479517342 = 1698506835 := by
        calc
          (7 : ZMod 1918069369) ^ 479517342 = (7 : ZMod 1918069369) ^ (239758671 + 239758671) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 239758671 * (7 : ZMod 1918069369) ^ 239758671 := by rw [pow_add]
          _ = 1698506835 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 1918069369) ^ 959034684 = 1918069368 := by
        calc
          (7 : ZMod 1918069369) ^ 959034684 = (7 : ZMod 1918069369) ^ (479517342 + 479517342) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 479517342 * (7 : ZMod 1918069369) ^ 479517342 := by rw [pow_add]
          _ = 1918069368 := by rw [factor_0_28]; decide
      change (7 : ZMod 1918069369) ^ 959034684 ≠ 1
      rw [factor_0_29]
      decide
    ·
      have factor_1_0 : (7 : ZMod 1918069369) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 1918069369) ^ 2 = 49 := by
        calc
          (7 : ZMod 1918069369) ^ 2 = (7 : ZMod 1918069369) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1 * (7 : ZMod 1918069369) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 1918069369) ^ 4 = 2401 := by
        calc
          (7 : ZMod 1918069369) ^ 4 = (7 : ZMod 1918069369) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 2 * (7 : ZMod 1918069369) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 1918069369) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 1918069369) ^ 9 = (7 : ZMod 1918069369) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 4 * (7 : ZMod 1918069369) ^ 4) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 1918069369) ^ 19 = 732343043 := by
        calc
          (7 : ZMod 1918069369) ^ 19 = (7 : ZMod 1918069369) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 9 * (7 : ZMod 1918069369) ^ 9) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 732343043 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 1918069369) ^ 38 = 1177539756 := by
        calc
          (7 : ZMod 1918069369) ^ 38 = (7 : ZMod 1918069369) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 19 * (7 : ZMod 1918069369) ^ 19 := by rw [pow_add]
          _ = 1177539756 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 1918069369) ^ 76 = 60786279 := by
        calc
          (7 : ZMod 1918069369) ^ 76 = (7 : ZMod 1918069369) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 38 * (7 : ZMod 1918069369) ^ 38 := by rw [pow_add]
          _ = 60786279 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 1918069369) ^ 152 = 964154872 := by
        calc
          (7 : ZMod 1918069369) ^ 152 = (7 : ZMod 1918069369) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 76 * (7 : ZMod 1918069369) ^ 76 := by rw [pow_add]
          _ = 964154872 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 1918069369) ^ 304 = 1586451691 := by
        calc
          (7 : ZMod 1918069369) ^ 304 = (7 : ZMod 1918069369) ^ (152 + 152) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 152 * (7 : ZMod 1918069369) ^ 152 := by rw [pow_add]
          _ = 1586451691 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 1918069369) ^ 609 = 930267485 := by
        calc
          (7 : ZMod 1918069369) ^ 609 = (7 : ZMod 1918069369) ^ (304 + 304 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 304 * (7 : ZMod 1918069369) ^ 304) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 930267485 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 1918069369) ^ 1219 = 1808102856 := by
        calc
          (7 : ZMod 1918069369) ^ 1219 = (7 : ZMod 1918069369) ^ (609 + 609 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 609 * (7 : ZMod 1918069369) ^ 609) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1808102856 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 1918069369) ^ 2438 = 690552935 := by
        calc
          (7 : ZMod 1918069369) ^ 2438 = (7 : ZMod 1918069369) ^ (1219 + 1219) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1219 * (7 : ZMod 1918069369) ^ 1219 := by rw [pow_add]
          _ = 690552935 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 1918069369) ^ 4877 = 457273314 := by
        calc
          (7 : ZMod 1918069369) ^ 4877 = (7 : ZMod 1918069369) ^ (2438 + 2438 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 2438 * (7 : ZMod 1918069369) ^ 2438) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 457273314 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 1918069369) ^ 9755 = 889482744 := by
        calc
          (7 : ZMod 1918069369) ^ 9755 = (7 : ZMod 1918069369) ^ (4877 + 4877 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 4877 * (7 : ZMod 1918069369) ^ 4877) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 889482744 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 1918069369) ^ 19511 = 1144733594 := by
        calc
          (7 : ZMod 1918069369) ^ 19511 = (7 : ZMod 1918069369) ^ (9755 + 9755 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 9755 * (7 : ZMod 1918069369) ^ 9755) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1144733594 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 1918069369) ^ 39023 = 719038437 := by
        calc
          (7 : ZMod 1918069369) ^ 39023 = (7 : ZMod 1918069369) ^ (19511 + 19511 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 19511 * (7 : ZMod 1918069369) ^ 19511) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 719038437 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 1918069369) ^ 78046 = 309035081 := by
        calc
          (7 : ZMod 1918069369) ^ 78046 = (7 : ZMod 1918069369) ^ (39023 + 39023) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 39023 * (7 : ZMod 1918069369) ^ 39023 := by rw [pow_add]
          _ = 309035081 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 1918069369) ^ 156092 = 1105606587 := by
        calc
          (7 : ZMod 1918069369) ^ 156092 = (7 : ZMod 1918069369) ^ (78046 + 78046) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 78046 * (7 : ZMod 1918069369) ^ 78046 := by rw [pow_add]
          _ = 1105606587 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 1918069369) ^ 312185 = 909811467 := by
        calc
          (7 : ZMod 1918069369) ^ 312185 = (7 : ZMod 1918069369) ^ (156092 + 156092 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 156092 * (7 : ZMod 1918069369) ^ 156092) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 909811467 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 1918069369) ^ 624371 = 1777443318 := by
        calc
          (7 : ZMod 1918069369) ^ 624371 = (7 : ZMod 1918069369) ^ (312185 + 312185 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 312185 * (7 : ZMod 1918069369) ^ 312185) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1777443318 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 1918069369) ^ 1248743 = 93262644 := by
        calc
          (7 : ZMod 1918069369) ^ 1248743 = (7 : ZMod 1918069369) ^ (624371 + 624371 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 624371 * (7 : ZMod 1918069369) ^ 624371) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 93262644 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 1918069369) ^ 2497486 = 1728462842 := by
        calc
          (7 : ZMod 1918069369) ^ 2497486 = (7 : ZMod 1918069369) ^ (1248743 + 1248743) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1248743 * (7 : ZMod 1918069369) ^ 1248743 := by rw [pow_add]
          _ = 1728462842 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 1918069369) ^ 4994972 = 40400545 := by
        calc
          (7 : ZMod 1918069369) ^ 4994972 = (7 : ZMod 1918069369) ^ (2497486 + 2497486) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 2497486 * (7 : ZMod 1918069369) ^ 2497486 := by rw [pow_add]
          _ = 40400545 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 1918069369) ^ 9989944 = 1807983416 := by
        calc
          (7 : ZMod 1918069369) ^ 9989944 = (7 : ZMod 1918069369) ^ (4994972 + 4994972) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 4994972 * (7 : ZMod 1918069369) ^ 4994972 := by rw [pow_add]
          _ = 1807983416 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 1918069369) ^ 19979889 = 1249630607 := by
        calc
          (7 : ZMod 1918069369) ^ 19979889 = (7 : ZMod 1918069369) ^ (9989944 + 9989944 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 9989944 * (7 : ZMod 1918069369) ^ 9989944) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1249630607 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 1918069369) ^ 39959778 = 1207945500 := by
        calc
          (7 : ZMod 1918069369) ^ 39959778 = (7 : ZMod 1918069369) ^ (19979889 + 19979889) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 19979889 * (7 : ZMod 1918069369) ^ 19979889 := by rw [pow_add]
          _ = 1207945500 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 1918069369) ^ 79919557 = 1707083542 := by
        calc
          (7 : ZMod 1918069369) ^ 79919557 = (7 : ZMod 1918069369) ^ (39959778 + 39959778 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 39959778 * (7 : ZMod 1918069369) ^ 39959778) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1707083542 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 1918069369) ^ 159839114 = 1106334631 := by
        calc
          (7 : ZMod 1918069369) ^ 159839114 = (7 : ZMod 1918069369) ^ (79919557 + 79919557) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 79919557 * (7 : ZMod 1918069369) ^ 79919557 := by rw [pow_add]
          _ = 1106334631 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 1918069369) ^ 319678228 = 170621498 := by
        calc
          (7 : ZMod 1918069369) ^ 319678228 = (7 : ZMod 1918069369) ^ (159839114 + 159839114) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 159839114 * (7 : ZMod 1918069369) ^ 159839114 := by rw [pow_add]
          _ = 170621498 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 1918069369) ^ 639356456 = 170621497 := by
        calc
          (7 : ZMod 1918069369) ^ 639356456 = (7 : ZMod 1918069369) ^ (319678228 + 319678228) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 319678228 * (7 : ZMod 1918069369) ^ 319678228 := by rw [pow_add]
          _ = 170621497 := by rw [factor_1_28]; decide
      change (7 : ZMod 1918069369) ^ 639356456 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (7 : ZMod 1918069369) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 1918069369) ^ 2 = 49 := by
        calc
          (7 : ZMod 1918069369) ^ 2 = (7 : ZMod 1918069369) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1 * (7 : ZMod 1918069369) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 1918069369) ^ 4 = 2401 := by
        calc
          (7 : ZMod 1918069369) ^ 4 = (7 : ZMod 1918069369) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 2 * (7 : ZMod 1918069369) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 1918069369) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 1918069369) ^ 9 = (7 : ZMod 1918069369) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 4 * (7 : ZMod 1918069369) ^ 4) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 1918069369) ^ 19 = 732343043 := by
        calc
          (7 : ZMod 1918069369) ^ 19 = (7 : ZMod 1918069369) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 9 * (7 : ZMod 1918069369) ^ 9) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 732343043 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 1918069369) ^ 38 = 1177539756 := by
        calc
          (7 : ZMod 1918069369) ^ 38 = (7 : ZMod 1918069369) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 19 * (7 : ZMod 1918069369) ^ 19 := by rw [pow_add]
          _ = 1177539756 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 1918069369) ^ 76 = 60786279 := by
        calc
          (7 : ZMod 1918069369) ^ 76 = (7 : ZMod 1918069369) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 38 * (7 : ZMod 1918069369) ^ 38 := by rw [pow_add]
          _ = 60786279 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 1918069369) ^ 153 = 994875997 := by
        calc
          (7 : ZMod 1918069369) ^ 153 = (7 : ZMod 1918069369) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 76 * (7 : ZMod 1918069369) ^ 76) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 994875997 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 1918069369) ^ 306 = 1013358099 := by
        calc
          (7 : ZMod 1918069369) ^ 306 = (7 : ZMod 1918069369) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 153 * (7 : ZMod 1918069369) ^ 153 := by rw [pow_add]
          _ = 1013358099 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 1918069369) ^ 612 = 682232101 := by
        calc
          (7 : ZMod 1918069369) ^ 612 = (7 : ZMod 1918069369) ^ (306 + 306) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 306 * (7 : ZMod 1918069369) ^ 306 := by rw [pow_add]
          _ = 682232101 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 1918069369) ^ 1225 = 1845675337 := by
        calc
          (7 : ZMod 1918069369) ^ 1225 = (7 : ZMod 1918069369) ^ (612 + 612 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 612 * (7 : ZMod 1918069369) ^ 612) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1845675337 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 1918069369) ^ 2451 = 816894783 := by
        calc
          (7 : ZMod 1918069369) ^ 2451 = (7 : ZMod 1918069369) ^ (1225 + 1225 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 1225 * (7 : ZMod 1918069369) ^ 1225) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 816894783 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 1918069369) ^ 4903 = 384750301 := by
        calc
          (7 : ZMod 1918069369) ^ 4903 = (7 : ZMod 1918069369) ^ (2451 + 2451 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 2451 * (7 : ZMod 1918069369) ^ 2451) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 384750301 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 1918069369) ^ 9806 = 1833659959 := by
        calc
          (7 : ZMod 1918069369) ^ 9806 = (7 : ZMod 1918069369) ^ (4903 + 4903) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 4903 * (7 : ZMod 1918069369) ^ 4903 := by rw [pow_add]
          _ = 1833659959 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 1918069369) ^ 19613 = 428957451 := by
        calc
          (7 : ZMod 1918069369) ^ 19613 = (7 : ZMod 1918069369) ^ (9806 + 9806 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 9806 * (7 : ZMod 1918069369) ^ 9806) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 428957451 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 1918069369) ^ 39227 = 1329763460 := by
        calc
          (7 : ZMod 1918069369) ^ 39227 = (7 : ZMod 1918069369) ^ (19613 + 19613 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 19613 * (7 : ZMod 1918069369) ^ 19613) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1329763460 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 1918069369) ^ 78455 = 1610927373 := by
        calc
          (7 : ZMod 1918069369) ^ 78455 = (7 : ZMod 1918069369) ^ (39227 + 39227 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 39227 * (7 : ZMod 1918069369) ^ 39227) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1610927373 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 1918069369) ^ 156910 = 1328620761 := by
        calc
          (7 : ZMod 1918069369) ^ 156910 = (7 : ZMod 1918069369) ^ (78455 + 78455) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 78455 * (7 : ZMod 1918069369) ^ 78455 := by rw [pow_add]
          _ = 1328620761 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 1918069369) ^ 313820 = 1656046367 := by
        calc
          (7 : ZMod 1918069369) ^ 313820 = (7 : ZMod 1918069369) ^ (156910 + 156910) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 156910 * (7 : ZMod 1918069369) ^ 156910 := by rw [pow_add]
          _ = 1656046367 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 1918069369) ^ 627640 = 1504618747 := by
        calc
          (7 : ZMod 1918069369) ^ 627640 = (7 : ZMod 1918069369) ^ (313820 + 313820) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 313820 * (7 : ZMod 1918069369) ^ 313820 := by rw [pow_add]
          _ = 1504618747 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 1918069369) ^ 1255281 = 11958639 := by
        calc
          (7 : ZMod 1918069369) ^ 1255281 = (7 : ZMod 1918069369) ^ (627640 + 627640 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 627640 * (7 : ZMod 1918069369) ^ 627640) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 11958639 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 1918069369) ^ 2510562 = 1630718419 := by
        calc
          (7 : ZMod 1918069369) ^ 2510562 = (7 : ZMod 1918069369) ^ (1255281 + 1255281) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1255281 * (7 : ZMod 1918069369) ^ 1255281 := by rw [pow_add]
          _ = 1630718419 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 1918069369) ^ 5021124 = 1076319621 := by
        calc
          (7 : ZMod 1918069369) ^ 5021124 = (7 : ZMod 1918069369) ^ (2510562 + 2510562) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 2510562 * (7 : ZMod 1918069369) ^ 2510562 := by rw [pow_add]
          _ = 1076319621 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 1918069369) ^ 10042248 = 1052923567 := by
        calc
          (7 : ZMod 1918069369) ^ 10042248 = (7 : ZMod 1918069369) ^ (5021124 + 5021124) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 5021124 * (7 : ZMod 1918069369) ^ 5021124 := by rw [pow_add]
          _ = 1052923567 := by rw [factor_2_22]; decide
      change (7 : ZMod 1918069369) ^ 10042248 ≠ 1
      rw [factor_2_23]
      decide
    ·
      have factor_3_0 : (7 : ZMod 1918069369) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 1918069369) ^ 2 = 49 := by
        calc
          (7 : ZMod 1918069369) ^ 2 = (7 : ZMod 1918069369) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1 * (7 : ZMod 1918069369) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 1918069369) ^ 4 = 2401 := by
        calc
          (7 : ZMod 1918069369) ^ 4 = (7 : ZMod 1918069369) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 2 * (7 : ZMod 1918069369) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 1918069369) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 1918069369) ^ 8 = (7 : ZMod 1918069369) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 4 * (7 : ZMod 1918069369) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 1918069369) ^ 17 = 1306706780 := by
        calc
          (7 : ZMod 1918069369) ^ 17 = (7 : ZMod 1918069369) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 8 * (7 : ZMod 1918069369) ^ 8) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1306706780 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 1918069369) ^ 35 = 126457918 := by
        calc
          (7 : ZMod 1918069369) ^ 35 = (7 : ZMod 1918069369) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 17 * (7 : ZMod 1918069369) ^ 17) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 126457918 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 1918069369) ^ 71 = 403543409 := by
        calc
          (7 : ZMod 1918069369) ^ 71 = (7 : ZMod 1918069369) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 35 * (7 : ZMod 1918069369) ^ 35) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 403543409 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 1918069369) ^ 143 = 1454262641 := by
        calc
          (7 : ZMod 1918069369) ^ 143 = (7 : ZMod 1918069369) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 71 * (7 : ZMod 1918069369) ^ 71) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 1454262641 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 1918069369) ^ 286 = 1318656625 := by
        calc
          (7 : ZMod 1918069369) ^ 286 = (7 : ZMod 1918069369) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 143 * (7 : ZMod 1918069369) ^ 143 := by rw [pow_add]
          _ = 1318656625 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 1918069369) ^ 573 = 435736765 := by
        calc
          (7 : ZMod 1918069369) ^ 573 = (7 : ZMod 1918069369) ^ (286 + 286 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = ((7 : ZMod 1918069369) ^ 286 * (7 : ZMod 1918069369) ^ 286) * (7 : ZMod 1918069369) := by rw [pow_succ, pow_add]
          _ = 435736765 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 1918069369) ^ 1146 = 595605968 := by
        calc
          (7 : ZMod 1918069369) ^ 1146 = (7 : ZMod 1918069369) ^ (573 + 573) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 573 * (7 : ZMod 1918069369) ^ 573 := by rw [pow_add]
          _ = 595605968 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 1918069369) ^ 2292 = 1575384953 := by
        calc
          (7 : ZMod 1918069369) ^ 2292 = (7 : ZMod 1918069369) ^ (1146 + 1146) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 1146 * (7 : ZMod 1918069369) ^ 1146 := by rw [pow_add]
          _ = 1575384953 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 1918069369) ^ 4584 = 1055244836 := by
        calc
          (7 : ZMod 1918069369) ^ 4584 = (7 : ZMod 1918069369) ^ (2292 + 2292) :=
            congrArg (fun n : ℕ => (7 : ZMod 1918069369) ^ n) (by norm_num)
          _ = (7 : ZMod 1918069369) ^ 2292 * (7 : ZMod 1918069369) ^ 2292 := by rw [pow_add]
          _ = 1055244836 := by rw [factor_3_11]; decide
      change (7 : ZMod 1918069369) ^ 4584 ≠ 1
      rw [factor_3_12]
      decide

#print axioms prime_lucas_1918069369

end TotientTailPeriodKiller
end Erdos249257
