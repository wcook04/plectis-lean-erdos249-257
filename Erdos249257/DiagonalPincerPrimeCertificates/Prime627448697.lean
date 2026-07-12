import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_627448697 : Nat.Prime 627448697 := by
  apply lucas_primality 627448697 (3 : ZMod 627448697)
  ·
      have fermat_0 : (3 : ZMod 627448697) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 627448697) ^ 2 = 9 := by
        calc
          (3 : ZMod 627448697) ^ 2 = (3 : ZMod 627448697) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 1 * (3 : ZMod 627448697) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 627448697) ^ 4 = 81 := by
        calc
          (3 : ZMod 627448697) ^ 4 = (3 : ZMod 627448697) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 2 * (3 : ZMod 627448697) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 627448697) ^ 9 = 19683 := by
        calc
          (3 : ZMod 627448697) ^ 9 = (3 : ZMod 627448697) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 4 * (3 : ZMod 627448697) ^ 4) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 627448697) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 627448697) ^ 18 = (3 : ZMod 627448697) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 9 * (3 : ZMod 627448697) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 627448697) ^ 37 = 393586921 := by
        calc
          (3 : ZMod 627448697) ^ 37 = (3 : ZMod 627448697) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 18 * (3 : ZMod 627448697) ^ 18) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 393586921 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 627448697) ^ 74 = 520579248 := by
        calc
          (3 : ZMod 627448697) ^ 74 = (3 : ZMod 627448697) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 37 * (3 : ZMod 627448697) ^ 37 := by rw [pow_add]
          _ = 520579248 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 627448697) ^ 149 = 196065402 := by
        calc
          (3 : ZMod 627448697) ^ 149 = (3 : ZMod 627448697) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 74 * (3 : ZMod 627448697) ^ 74) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 196065402 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 627448697) ^ 299 = 16313819 := by
        calc
          (3 : ZMod 627448697) ^ 299 = (3 : ZMod 627448697) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 149 * (3 : ZMod 627448697) ^ 149) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 16313819 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 627448697) ^ 598 = 168699150 := by
        calc
          (3 : ZMod 627448697) ^ 598 = (3 : ZMod 627448697) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 299 * (3 : ZMod 627448697) ^ 299 := by rw [pow_add]
          _ = 168699150 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 627448697) ^ 1196 = 583233914 := by
        calc
          (3 : ZMod 627448697) ^ 1196 = (3 : ZMod 627448697) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 598 * (3 : ZMod 627448697) ^ 598 := by rw [pow_add]
          _ = 583233914 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 627448697) ^ 2393 = 332713839 := by
        calc
          (3 : ZMod 627448697) ^ 2393 = (3 : ZMod 627448697) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 1196 * (3 : ZMod 627448697) ^ 1196) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 332713839 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 627448697) ^ 4787 = 538149729 := by
        calc
          (3 : ZMod 627448697) ^ 4787 = (3 : ZMod 627448697) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 2393 * (3 : ZMod 627448697) ^ 2393) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 538149729 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 627448697) ^ 9574 = 588065809 := by
        calc
          (3 : ZMod 627448697) ^ 9574 = (3 : ZMod 627448697) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 4787 * (3 : ZMod 627448697) ^ 4787 := by rw [pow_add]
          _ = 588065809 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 627448697) ^ 19148 = 99850546 := by
        calc
          (3 : ZMod 627448697) ^ 19148 = (3 : ZMod 627448697) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 9574 * (3 : ZMod 627448697) ^ 9574 := by rw [pow_add]
          _ = 99850546 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 627448697) ^ 38296 = 603808178 := by
        calc
          (3 : ZMod 627448697) ^ 38296 = (3 : ZMod 627448697) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 19148 * (3 : ZMod 627448697) ^ 19148 := by rw [pow_add]
          _ = 603808178 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 627448697) ^ 76592 = 564581885 := by
        calc
          (3 : ZMod 627448697) ^ 76592 = (3 : ZMod 627448697) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 38296 * (3 : ZMod 627448697) ^ 38296 := by rw [pow_add]
          _ = 564581885 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 627448697) ^ 153185 = 242876223 := by
        calc
          (3 : ZMod 627448697) ^ 153185 = (3 : ZMod 627448697) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 76592 * (3 : ZMod 627448697) ^ 76592) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 242876223 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 627448697) ^ 306371 = 519376020 := by
        calc
          (3 : ZMod 627448697) ^ 306371 = (3 : ZMod 627448697) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 153185 * (3 : ZMod 627448697) ^ 153185) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 519376020 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 627448697) ^ 612742 = 136013614 := by
        calc
          (3 : ZMod 627448697) ^ 612742 = (3 : ZMod 627448697) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 306371 * (3 : ZMod 627448697) ^ 306371 := by rw [pow_add]
          _ = 136013614 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 627448697) ^ 1225485 = 491864169 := by
        calc
          (3 : ZMod 627448697) ^ 1225485 = (3 : ZMod 627448697) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 612742 * (3 : ZMod 627448697) ^ 612742) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 491864169 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 627448697) ^ 2450971 = 534552721 := by
        calc
          (3 : ZMod 627448697) ^ 2450971 = (3 : ZMod 627448697) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 1225485 * (3 : ZMod 627448697) ^ 1225485) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 534552721 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 627448697) ^ 4901942 = 271599498 := by
        calc
          (3 : ZMod 627448697) ^ 4901942 = (3 : ZMod 627448697) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 2450971 * (3 : ZMod 627448697) ^ 2450971 := by rw [pow_add]
          _ = 271599498 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 627448697) ^ 9803885 = 462092244 := by
        calc
          (3 : ZMod 627448697) ^ 9803885 = (3 : ZMod 627448697) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 4901942 * (3 : ZMod 627448697) ^ 4901942) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 462092244 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 627448697) ^ 19607771 = 317861717 := by
        calc
          (3 : ZMod 627448697) ^ 19607771 = (3 : ZMod 627448697) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 9803885 * (3 : ZMod 627448697) ^ 9803885) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 317861717 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 627448697) ^ 39215543 = 72570586 := by
        calc
          (3 : ZMod 627448697) ^ 39215543 = (3 : ZMod 627448697) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 19607771 * (3 : ZMod 627448697) ^ 19607771) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 72570586 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 627448697) ^ 78431087 = 452136476 := by
        calc
          (3 : ZMod 627448697) ^ 78431087 = (3 : ZMod 627448697) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 39215543 * (3 : ZMod 627448697) ^ 39215543) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 452136476 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 627448697) ^ 156862174 = 91316505 := by
        calc
          (3 : ZMod 627448697) ^ 156862174 = (3 : ZMod 627448697) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 78431087 * (3 : ZMod 627448697) ^ 78431087 := by rw [pow_add]
          _ = 91316505 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 627448697) ^ 313724348 = 627448696 := by
        calc
          (3 : ZMod 627448697) ^ 313724348 = (3 : ZMod 627448697) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 156862174 * (3 : ZMod 627448697) ^ 156862174 := by rw [pow_add]
          _ = 627448696 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 627448697) ^ 627448696 = 1 := by
        calc
          (3 : ZMod 627448697) ^ 627448696 = (3 : ZMod 627448697) ^ (313724348 + 313724348) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 313724348 * (3 : ZMod 627448697) ^ 313724348 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (1913, 1), (5857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (1913, 1), (5857, 1)] : List FactorBlock).map factorBlockValue).prod = 627448697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 627448697) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 627448697) ^ 2 = 9 := by
        calc
          (3 : ZMod 627448697) ^ 2 = (3 : ZMod 627448697) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 1 * (3 : ZMod 627448697) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 627448697) ^ 4 = 81 := by
        calc
          (3 : ZMod 627448697) ^ 4 = (3 : ZMod 627448697) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 2 * (3 : ZMod 627448697) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 627448697) ^ 9 = 19683 := by
        calc
          (3 : ZMod 627448697) ^ 9 = (3 : ZMod 627448697) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 4 * (3 : ZMod 627448697) ^ 4) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 627448697) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 627448697) ^ 18 = (3 : ZMod 627448697) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 9 * (3 : ZMod 627448697) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 627448697) ^ 37 = 393586921 := by
        calc
          (3 : ZMod 627448697) ^ 37 = (3 : ZMod 627448697) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 18 * (3 : ZMod 627448697) ^ 18) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 393586921 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 627448697) ^ 74 = 520579248 := by
        calc
          (3 : ZMod 627448697) ^ 74 = (3 : ZMod 627448697) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 37 * (3 : ZMod 627448697) ^ 37 := by rw [pow_add]
          _ = 520579248 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 627448697) ^ 149 = 196065402 := by
        calc
          (3 : ZMod 627448697) ^ 149 = (3 : ZMod 627448697) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 74 * (3 : ZMod 627448697) ^ 74) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 196065402 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 627448697) ^ 299 = 16313819 := by
        calc
          (3 : ZMod 627448697) ^ 299 = (3 : ZMod 627448697) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 149 * (3 : ZMod 627448697) ^ 149) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 16313819 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 627448697) ^ 598 = 168699150 := by
        calc
          (3 : ZMod 627448697) ^ 598 = (3 : ZMod 627448697) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 299 * (3 : ZMod 627448697) ^ 299 := by rw [pow_add]
          _ = 168699150 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 627448697) ^ 1196 = 583233914 := by
        calc
          (3 : ZMod 627448697) ^ 1196 = (3 : ZMod 627448697) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 598 * (3 : ZMod 627448697) ^ 598 := by rw [pow_add]
          _ = 583233914 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 627448697) ^ 2393 = 332713839 := by
        calc
          (3 : ZMod 627448697) ^ 2393 = (3 : ZMod 627448697) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 1196 * (3 : ZMod 627448697) ^ 1196) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 332713839 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 627448697) ^ 4787 = 538149729 := by
        calc
          (3 : ZMod 627448697) ^ 4787 = (3 : ZMod 627448697) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 2393 * (3 : ZMod 627448697) ^ 2393) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 538149729 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 627448697) ^ 9574 = 588065809 := by
        calc
          (3 : ZMod 627448697) ^ 9574 = (3 : ZMod 627448697) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 4787 * (3 : ZMod 627448697) ^ 4787 := by rw [pow_add]
          _ = 588065809 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 627448697) ^ 19148 = 99850546 := by
        calc
          (3 : ZMod 627448697) ^ 19148 = (3 : ZMod 627448697) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 9574 * (3 : ZMod 627448697) ^ 9574 := by rw [pow_add]
          _ = 99850546 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 627448697) ^ 38296 = 603808178 := by
        calc
          (3 : ZMod 627448697) ^ 38296 = (3 : ZMod 627448697) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 19148 * (3 : ZMod 627448697) ^ 19148 := by rw [pow_add]
          _ = 603808178 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 627448697) ^ 76592 = 564581885 := by
        calc
          (3 : ZMod 627448697) ^ 76592 = (3 : ZMod 627448697) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 38296 * (3 : ZMod 627448697) ^ 38296 := by rw [pow_add]
          _ = 564581885 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 627448697) ^ 153185 = 242876223 := by
        calc
          (3 : ZMod 627448697) ^ 153185 = (3 : ZMod 627448697) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 76592 * (3 : ZMod 627448697) ^ 76592) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 242876223 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 627448697) ^ 306371 = 519376020 := by
        calc
          (3 : ZMod 627448697) ^ 306371 = (3 : ZMod 627448697) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 153185 * (3 : ZMod 627448697) ^ 153185) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 519376020 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 627448697) ^ 612742 = 136013614 := by
        calc
          (3 : ZMod 627448697) ^ 612742 = (3 : ZMod 627448697) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 306371 * (3 : ZMod 627448697) ^ 306371 := by rw [pow_add]
          _ = 136013614 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 627448697) ^ 1225485 = 491864169 := by
        calc
          (3 : ZMod 627448697) ^ 1225485 = (3 : ZMod 627448697) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 612742 * (3 : ZMod 627448697) ^ 612742) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 491864169 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 627448697) ^ 2450971 = 534552721 := by
        calc
          (3 : ZMod 627448697) ^ 2450971 = (3 : ZMod 627448697) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 1225485 * (3 : ZMod 627448697) ^ 1225485) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 534552721 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 627448697) ^ 4901942 = 271599498 := by
        calc
          (3 : ZMod 627448697) ^ 4901942 = (3 : ZMod 627448697) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 2450971 * (3 : ZMod 627448697) ^ 2450971 := by rw [pow_add]
          _ = 271599498 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 627448697) ^ 9803885 = 462092244 := by
        calc
          (3 : ZMod 627448697) ^ 9803885 = (3 : ZMod 627448697) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 4901942 * (3 : ZMod 627448697) ^ 4901942) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 462092244 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 627448697) ^ 19607771 = 317861717 := by
        calc
          (3 : ZMod 627448697) ^ 19607771 = (3 : ZMod 627448697) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 9803885 * (3 : ZMod 627448697) ^ 9803885) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 317861717 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 627448697) ^ 39215543 = 72570586 := by
        calc
          (3 : ZMod 627448697) ^ 39215543 = (3 : ZMod 627448697) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 19607771 * (3 : ZMod 627448697) ^ 19607771) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 72570586 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 627448697) ^ 78431087 = 452136476 := by
        calc
          (3 : ZMod 627448697) ^ 78431087 = (3 : ZMod 627448697) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 39215543 * (3 : ZMod 627448697) ^ 39215543) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 452136476 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 627448697) ^ 156862174 = 91316505 := by
        calc
          (3 : ZMod 627448697) ^ 156862174 = (3 : ZMod 627448697) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 78431087 * (3 : ZMod 627448697) ^ 78431087 := by rw [pow_add]
          _ = 91316505 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 627448697) ^ 313724348 = 627448696 := by
        calc
          (3 : ZMod 627448697) ^ 313724348 = (3 : ZMod 627448697) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 156862174 * (3 : ZMod 627448697) ^ 156862174 := by rw [pow_add]
          _ = 627448696 := by rw [factor_0_27]; decide
      change (3 : ZMod 627448697) ^ 313724348 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (3 : ZMod 627448697) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 627448697) ^ 2 = 9 := by
        calc
          (3 : ZMod 627448697) ^ 2 = (3 : ZMod 627448697) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 1 * (3 : ZMod 627448697) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 627448697) ^ 5 = 243 := by
        calc
          (3 : ZMod 627448697) ^ 5 = (3 : ZMod 627448697) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 2 * (3 : ZMod 627448697) ^ 2) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 627448697) ^ 10 = 59049 := by
        calc
          (3 : ZMod 627448697) ^ 10 = (3 : ZMod 627448697) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 5 * (3 : ZMod 627448697) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 627448697) ^ 21 = 421174051 := by
        calc
          (3 : ZMod 627448697) ^ 21 = (3 : ZMod 627448697) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 10 * (3 : ZMod 627448697) ^ 10) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 421174051 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 627448697) ^ 42 = 269419859 := by
        calc
          (3 : ZMod 627448697) ^ 42 = (3 : ZMod 627448697) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 21 * (3 : ZMod 627448697) ^ 21 := by rw [pow_add]
          _ = 269419859 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 627448697) ^ 85 = 407252578 := by
        calc
          (3 : ZMod 627448697) ^ 85 = (3 : ZMod 627448697) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 42 * (3 : ZMod 627448697) ^ 42) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 407252578 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 627448697) ^ 170 = 605969271 := by
        calc
          (3 : ZMod 627448697) ^ 170 = (3 : ZMod 627448697) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 85 * (3 : ZMod 627448697) ^ 85 := by rw [pow_add]
          _ = 605969271 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 627448697) ^ 341 = 613771764 := by
        calc
          (3 : ZMod 627448697) ^ 341 = (3 : ZMod 627448697) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 170 * (3 : ZMod 627448697) ^ 170) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 613771764 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 627448697) ^ 683 = 433031395 := by
        calc
          (3 : ZMod 627448697) ^ 683 = (3 : ZMod 627448697) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 341 * (3 : ZMod 627448697) ^ 341) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 433031395 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 627448697) ^ 1367 = 415736498 := by
        calc
          (3 : ZMod 627448697) ^ 1367 = (3 : ZMod 627448697) ^ (683 + 683 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 683 * (3 : ZMod 627448697) ^ 683) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 415736498 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 627448697) ^ 2735 = 216315796 := by
        calc
          (3 : ZMod 627448697) ^ 2735 = (3 : ZMod 627448697) ^ (1367 + 1367 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 1367 * (3 : ZMod 627448697) ^ 1367) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 216315796 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 627448697) ^ 5470 = 551702681 := by
        calc
          (3 : ZMod 627448697) ^ 5470 = (3 : ZMod 627448697) ^ (2735 + 2735) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 2735 * (3 : ZMod 627448697) ^ 2735 := by rw [pow_add]
          _ = 551702681 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 627448697) ^ 10941 = 242686243 := by
        calc
          (3 : ZMod 627448697) ^ 10941 = (3 : ZMod 627448697) ^ (5470 + 5470 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 5470 * (3 : ZMod 627448697) ^ 5470) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 242686243 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 627448697) ^ 21883 = 314905406 := by
        calc
          (3 : ZMod 627448697) ^ 21883 = (3 : ZMod 627448697) ^ (10941 + 10941 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 10941 * (3 : ZMod 627448697) ^ 10941) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 314905406 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 627448697) ^ 43767 = 391956800 := by
        calc
          (3 : ZMod 627448697) ^ 43767 = (3 : ZMod 627448697) ^ (21883 + 21883 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 21883 * (3 : ZMod 627448697) ^ 21883) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 391956800 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 627448697) ^ 87534 = 387626245 := by
        calc
          (3 : ZMod 627448697) ^ 87534 = (3 : ZMod 627448697) ^ (43767 + 43767) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 43767 * (3 : ZMod 627448697) ^ 43767 := by rw [pow_add]
          _ = 387626245 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 627448697) ^ 175069 = 505539346 := by
        calc
          (3 : ZMod 627448697) ^ 175069 = (3 : ZMod 627448697) ^ (87534 + 87534 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 87534 * (3 : ZMod 627448697) ^ 87534) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 505539346 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 627448697) ^ 350138 = 103039770 := by
        calc
          (3 : ZMod 627448697) ^ 350138 = (3 : ZMod 627448697) ^ (175069 + 175069) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 175069 * (3 : ZMod 627448697) ^ 175069 := by rw [pow_add]
          _ = 103039770 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 627448697) ^ 700277 = 322186832 := by
        calc
          (3 : ZMod 627448697) ^ 700277 = (3 : ZMod 627448697) ^ (350138 + 350138 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 350138 * (3 : ZMod 627448697) ^ 350138) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 322186832 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 627448697) ^ 1400555 = 94177903 := by
        calc
          (3 : ZMod 627448697) ^ 1400555 = (3 : ZMod 627448697) ^ (700277 + 700277 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 700277 * (3 : ZMod 627448697) ^ 700277) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 94177903 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 627448697) ^ 2801110 = 43950052 := by
        calc
          (3 : ZMod 627448697) ^ 2801110 = (3 : ZMod 627448697) ^ (1400555 + 1400555) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 1400555 * (3 : ZMod 627448697) ^ 1400555 := by rw [pow_add]
          _ = 43950052 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 627448697) ^ 5602220 = 610049931 := by
        calc
          (3 : ZMod 627448697) ^ 5602220 = (3 : ZMod 627448697) ^ (2801110 + 2801110) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 2801110 * (3 : ZMod 627448697) ^ 2801110 := by rw [pow_add]
          _ = 610049931 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 627448697) ^ 11204441 = 126942681 := by
        calc
          (3 : ZMod 627448697) ^ 11204441 = (3 : ZMod 627448697) ^ (5602220 + 5602220 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 5602220 * (3 : ZMod 627448697) ^ 5602220) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 126942681 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 627448697) ^ 22408882 = 700928 := by
        calc
          (3 : ZMod 627448697) ^ 22408882 = (3 : ZMod 627448697) ^ (11204441 + 11204441) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 11204441 * (3 : ZMod 627448697) ^ 11204441 := by rw [pow_add]
          _ = 700928 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 627448697) ^ 44817764 = 7731433 := by
        calc
          (3 : ZMod 627448697) ^ 44817764 = (3 : ZMod 627448697) ^ (22408882 + 22408882) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 22408882 * (3 : ZMod 627448697) ^ 22408882 := by rw [pow_add]
          _ = 7731433 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 627448697) ^ 89635528 = 528665087 := by
        calc
          (3 : ZMod 627448697) ^ 89635528 = (3 : ZMod 627448697) ^ (44817764 + 44817764) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 44817764 * (3 : ZMod 627448697) ^ 44817764 := by rw [pow_add]
          _ = 528665087 := by rw [factor_1_25]; decide
      change (3 : ZMod 627448697) ^ 89635528 ≠ 1
      rw [factor_1_26]
      decide
    ·
      have factor_2_0 : (3 : ZMod 627448697) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 627448697) ^ 2 = 9 := by
        calc
          (3 : ZMod 627448697) ^ 2 = (3 : ZMod 627448697) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 1 * (3 : ZMod 627448697) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 627448697) ^ 5 = 243 := by
        calc
          (3 : ZMod 627448697) ^ 5 = (3 : ZMod 627448697) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 2 * (3 : ZMod 627448697) ^ 2) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 627448697) ^ 10 = 59049 := by
        calc
          (3 : ZMod 627448697) ^ 10 = (3 : ZMod 627448697) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 5 * (3 : ZMod 627448697) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 627448697) ^ 20 = 349540916 := by
        calc
          (3 : ZMod 627448697) ^ 20 = (3 : ZMod 627448697) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 10 * (3 : ZMod 627448697) ^ 10 := by rw [pow_add]
          _ = 349540916 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 627448697) ^ 40 = 587667715 := by
        calc
          (3 : ZMod 627448697) ^ 40 = (3 : ZMod 627448697) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 20 * (3 : ZMod 627448697) ^ 20 := by rw [pow_add]
          _ = 587667715 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 627448697) ^ 80 = 523258804 := by
        calc
          (3 : ZMod 627448697) ^ 80 = (3 : ZMod 627448697) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 40 * (3 : ZMod 627448697) ^ 40 := by rw [pow_add]
          _ = 523258804 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 627448697) ^ 160 = 602594356 := by
        calc
          (3 : ZMod 627448697) ^ 160 = (3 : ZMod 627448697) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 80 * (3 : ZMod 627448697) ^ 80 := by rw [pow_add]
          _ = 602594356 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 627448697) ^ 320 = 593027750 := by
        calc
          (3 : ZMod 627448697) ^ 320 = (3 : ZMod 627448697) ^ (160 + 160) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 160 * (3 : ZMod 627448697) ^ 160 := by rw [pow_add]
          _ = 593027750 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 627448697) ^ 640 = 257010861 := by
        calc
          (3 : ZMod 627448697) ^ 640 = (3 : ZMod 627448697) ^ (320 + 320) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 320 * (3 : ZMod 627448697) ^ 320 := by rw [pow_add]
          _ = 257010861 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 627448697) ^ 1281 = 461466429 := by
        calc
          (3 : ZMod 627448697) ^ 1281 = (3 : ZMod 627448697) ^ (640 + 640 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 640 * (3 : ZMod 627448697) ^ 640) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 461466429 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 627448697) ^ 2562 = 530345880 := by
        calc
          (3 : ZMod 627448697) ^ 2562 = (3 : ZMod 627448697) ^ (1281 + 1281) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 1281 * (3 : ZMod 627448697) ^ 1281 := by rw [pow_add]
          _ = 530345880 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 627448697) ^ 5124 = 10359354 := by
        calc
          (3 : ZMod 627448697) ^ 5124 = (3 : ZMod 627448697) ^ (2562 + 2562) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 2562 * (3 : ZMod 627448697) ^ 2562 := by rw [pow_add]
          _ = 10359354 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 627448697) ^ 10249 = 327320369 := by
        calc
          (3 : ZMod 627448697) ^ 10249 = (3 : ZMod 627448697) ^ (5124 + 5124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 5124 * (3 : ZMod 627448697) ^ 5124) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 327320369 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 627448697) ^ 20499 = 5096713 := by
        calc
          (3 : ZMod 627448697) ^ 20499 = (3 : ZMod 627448697) ^ (10249 + 10249 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 10249 * (3 : ZMod 627448697) ^ 10249) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 5096713 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 627448697) ^ 40999 = 322045707 := by
        calc
          (3 : ZMod 627448697) ^ 40999 = (3 : ZMod 627448697) ^ (20499 + 20499 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 20499 * (3 : ZMod 627448697) ^ 20499) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 322045707 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 627448697) ^ 81998 = 239671125 := by
        calc
          (3 : ZMod 627448697) ^ 81998 = (3 : ZMod 627448697) ^ (40999 + 40999) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 40999 * (3 : ZMod 627448697) ^ 40999 := by rw [pow_add]
          _ = 239671125 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 627448697) ^ 163996 = 102803173 := by
        calc
          (3 : ZMod 627448697) ^ 163996 = (3 : ZMod 627448697) ^ (81998 + 81998) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 81998 * (3 : ZMod 627448697) ^ 81998 := by rw [pow_add]
          _ = 102803173 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 627448697) ^ 327992 = 15873517 := by
        calc
          (3 : ZMod 627448697) ^ 327992 = (3 : ZMod 627448697) ^ (163996 + 163996) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 163996 * (3 : ZMod 627448697) ^ 163996 := by rw [pow_add]
          _ = 15873517 := by rw [factor_2_17]; decide
      change (3 : ZMod 627448697) ^ 327992 ≠ 1
      rw [factor_2_18]
      decide
    ·
      have factor_3_0 : (3 : ZMod 627448697) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 627448697) ^ 3 = 27 := by
        calc
          (3 : ZMod 627448697) ^ 3 = (3 : ZMod 627448697) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 1 * (3 : ZMod 627448697) ^ 1) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 627448697) ^ 6 = 729 := by
        calc
          (3 : ZMod 627448697) ^ 6 = (3 : ZMod 627448697) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 3 * (3 : ZMod 627448697) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 627448697) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 627448697) ^ 13 = (3 : ZMod 627448697) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 6 * (3 : ZMod 627448697) ^ 6) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 627448697) ^ 26 = 71156782 := by
        calc
          (3 : ZMod 627448697) ^ 26 = (3 : ZMod 627448697) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 13 * (3 : ZMod 627448697) ^ 13 := by rw [pow_add]
          _ = 71156782 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 627448697) ^ 52 = 11541656 := by
        calc
          (3 : ZMod 627448697) ^ 52 = (3 : ZMod 627448697) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 26 * (3 : ZMod 627448697) ^ 26 := by rw [pow_add]
          _ = 11541656 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 627448697) ^ 104 = 582503145 := by
        calc
          (3 : ZMod 627448697) ^ 104 = (3 : ZMod 627448697) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 52 * (3 : ZMod 627448697) ^ 52 := by rw [pow_add]
          _ = 582503145 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 627448697) ^ 209 = 576475062 := by
        calc
          (3 : ZMod 627448697) ^ 209 = (3 : ZMod 627448697) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 104 * (3 : ZMod 627448697) ^ 104) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 576475062 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 627448697) ^ 418 = 607081344 := by
        calc
          (3 : ZMod 627448697) ^ 418 = (3 : ZMod 627448697) ^ (209 + 209) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 209 * (3 : ZMod 627448697) ^ 209 := by rw [pow_add]
          _ = 607081344 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 627448697) ^ 836 = 146486817 := by
        calc
          (3 : ZMod 627448697) ^ 836 = (3 : ZMod 627448697) ^ (418 + 418) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 418 * (3 : ZMod 627448697) ^ 418 := by rw [pow_add]
          _ = 146486817 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 627448697) ^ 1673 = 544343731 := by
        calc
          (3 : ZMod 627448697) ^ 1673 = (3 : ZMod 627448697) ^ (836 + 836 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 836 * (3 : ZMod 627448697) ^ 836) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 544343731 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 627448697) ^ 3347 = 189316210 := by
        calc
          (3 : ZMod 627448697) ^ 3347 = (3 : ZMod 627448697) ^ (1673 + 1673 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 1673 * (3 : ZMod 627448697) ^ 1673) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 189316210 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 627448697) ^ 6695 = 141743069 := by
        calc
          (3 : ZMod 627448697) ^ 6695 = (3 : ZMod 627448697) ^ (3347 + 3347 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 3347 * (3 : ZMod 627448697) ^ 3347) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 141743069 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 627448697) ^ 13391 = 16482013 := by
        calc
          (3 : ZMod 627448697) ^ 13391 = (3 : ZMod 627448697) ^ (6695 + 6695 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = ((3 : ZMod 627448697) ^ 6695 * (3 : ZMod 627448697) ^ 6695) * (3 : ZMod 627448697) := by rw [pow_succ, pow_add]
          _ = 16482013 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 627448697) ^ 26782 = 329371231 := by
        calc
          (3 : ZMod 627448697) ^ 26782 = (3 : ZMod 627448697) ^ (13391 + 13391) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 13391 * (3 : ZMod 627448697) ^ 13391 := by rw [pow_add]
          _ = 329371231 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 627448697) ^ 53564 = 568024202 := by
        calc
          (3 : ZMod 627448697) ^ 53564 = (3 : ZMod 627448697) ^ (26782 + 26782) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 26782 * (3 : ZMod 627448697) ^ 26782 := by rw [pow_add]
          _ = 568024202 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 627448697) ^ 107128 = 5916874 := by
        calc
          (3 : ZMod 627448697) ^ 107128 = (3 : ZMod 627448697) ^ (53564 + 53564) :=
            congrArg (fun n : ℕ => (3 : ZMod 627448697) ^ n) (by norm_num)
          _ = (3 : ZMod 627448697) ^ 53564 * (3 : ZMod 627448697) ^ 53564 := by rw [pow_add]
          _ = 5916874 := by rw [factor_3_15]; decide
      change (3 : ZMod 627448697) ^ 107128 ≠ 1
      rw [factor_3_16]
      decide

#print axioms prime_lucas_627448697

end TotientTailPeriodKiller
end Erdos249257
