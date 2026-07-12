import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime627448697

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_5019589577 : Nat.Prime 5019589577 := by
  apply lucas_primality 5019589577 (3 : ZMod 5019589577)
  ·
      have fermat_0 : (3 : ZMod 5019589577) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 5019589577) ^ 2 = 9 := by
        calc
          (3 : ZMod 5019589577) ^ 2 = (3 : ZMod 5019589577) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 1 * (3 : ZMod 5019589577) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 5019589577) ^ 4 = 81 := by
        calc
          (3 : ZMod 5019589577) ^ 4 = (3 : ZMod 5019589577) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 2 * (3 : ZMod 5019589577) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 5019589577) ^ 9 = 19683 := by
        calc
          (3 : ZMod 5019589577) ^ 9 = (3 : ZMod 5019589577) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 4 * (3 : ZMod 5019589577) ^ 4) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 5019589577) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 5019589577) ^ 18 = (3 : ZMod 5019589577) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 9 * (3 : ZMod 5019589577) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 5019589577) ^ 37 = 1558778992 := by
        calc
          (3 : ZMod 5019589577) ^ 37 = (3 : ZMod 5019589577) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 18 * (3 : ZMod 5019589577) ^ 18) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 1558778992 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 5019589577) ^ 74 = 3527459189 := by
        calc
          (3 : ZMod 5019589577) ^ 74 = (3 : ZMod 5019589577) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 37 * (3 : ZMod 5019589577) ^ 37 := by rw [pow_add]
          _ = 3527459189 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 5019589577) ^ 149 = 3231705559 := by
        calc
          (3 : ZMod 5019589577) ^ 149 = (3 : ZMod 5019589577) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 74 * (3 : ZMod 5019589577) ^ 74) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3231705559 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 5019589577) ^ 299 = 3096110961 := by
        calc
          (3 : ZMod 5019589577) ^ 299 = (3 : ZMod 5019589577) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 149 * (3 : ZMod 5019589577) ^ 149) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3096110961 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 5019589577) ^ 598 = 464232438 := by
        calc
          (3 : ZMod 5019589577) ^ 598 = (3 : ZMod 5019589577) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 299 * (3 : ZMod 5019589577) ^ 299 := by rw [pow_add]
          _ = 464232438 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 5019589577) ^ 1196 = 4889144218 := by
        calc
          (3 : ZMod 5019589577) ^ 1196 = (3 : ZMod 5019589577) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 598 * (3 : ZMod 5019589577) ^ 598 := by rw [pow_add]
          _ = 4889144218 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 5019589577) ^ 2393 = 3953220893 := by
        calc
          (3 : ZMod 5019589577) ^ 2393 = (3 : ZMod 5019589577) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 1196 * (3 : ZMod 5019589577) ^ 1196) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3953220893 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 5019589577) ^ 4787 = 1433214522 := by
        calc
          (3 : ZMod 5019589577) ^ 4787 = (3 : ZMod 5019589577) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 2393 * (3 : ZMod 5019589577) ^ 2393) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 1433214522 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 5019589577) ^ 9574 = 3482818023 := by
        calc
          (3 : ZMod 5019589577) ^ 9574 = (3 : ZMod 5019589577) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 4787 * (3 : ZMod 5019589577) ^ 4787 := by rw [pow_add]
          _ = 3482818023 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 5019589577) ^ 19148 = 3689463799 := by
        calc
          (3 : ZMod 5019589577) ^ 19148 = (3 : ZMod 5019589577) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 9574 * (3 : ZMod 5019589577) ^ 9574 := by rw [pow_add]
          _ = 3689463799 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 5019589577) ^ 38296 = 747066939 := by
        calc
          (3 : ZMod 5019589577) ^ 38296 = (3 : ZMod 5019589577) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 19148 * (3 : ZMod 5019589577) ^ 19148 := by rw [pow_add]
          _ = 747066939 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 5019589577) ^ 76592 = 1034025553 := by
        calc
          (3 : ZMod 5019589577) ^ 76592 = (3 : ZMod 5019589577) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 38296 * (3 : ZMod 5019589577) ^ 38296 := by rw [pow_add]
          _ = 1034025553 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 5019589577) ^ 153185 = 3502965106 := by
        calc
          (3 : ZMod 5019589577) ^ 153185 = (3 : ZMod 5019589577) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 76592 * (3 : ZMod 5019589577) ^ 76592) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3502965106 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 5019589577) ^ 306371 = 246018377 := by
        calc
          (3 : ZMod 5019589577) ^ 306371 = (3 : ZMod 5019589577) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 153185 * (3 : ZMod 5019589577) ^ 153185) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 246018377 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 5019589577) ^ 612742 = 266619570 := by
        calc
          (3 : ZMod 5019589577) ^ 612742 = (3 : ZMod 5019589577) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 306371 * (3 : ZMod 5019589577) ^ 306371 := by rw [pow_add]
          _ = 266619570 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 5019589577) ^ 1225485 = 4340800189 := by
        calc
          (3 : ZMod 5019589577) ^ 1225485 = (3 : ZMod 5019589577) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 612742 * (3 : ZMod 5019589577) ^ 612742) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 4340800189 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 5019589577) ^ 2450971 = 2119569353 := by
        calc
          (3 : ZMod 5019589577) ^ 2450971 = (3 : ZMod 5019589577) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 1225485 * (3 : ZMod 5019589577) ^ 1225485) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 2119569353 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 5019589577) ^ 4901942 = 3540551472 := by
        calc
          (3 : ZMod 5019589577) ^ 4901942 = (3 : ZMod 5019589577) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 2450971 * (3 : ZMod 5019589577) ^ 2450971 := by rw [pow_add]
          _ = 3540551472 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 5019589577) ^ 9803885 = 1062644159 := by
        calc
          (3 : ZMod 5019589577) ^ 9803885 = (3 : ZMod 5019589577) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 4901942 * (3 : ZMod 5019589577) ^ 4901942) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 1062644159 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 5019589577) ^ 19607771 = 72032310 := by
        calc
          (3 : ZMod 5019589577) ^ 19607771 = (3 : ZMod 5019589577) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 9803885 * (3 : ZMod 5019589577) ^ 9803885) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 72032310 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 5019589577) ^ 39215543 = 2950769066 := by
        calc
          (3 : ZMod 5019589577) ^ 39215543 = (3 : ZMod 5019589577) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 19607771 * (3 : ZMod 5019589577) ^ 19607771) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 2950769066 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 5019589577) ^ 78431087 = 2741839940 := by
        calc
          (3 : ZMod 5019589577) ^ 78431087 = (3 : ZMod 5019589577) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 39215543 * (3 : ZMod 5019589577) ^ 39215543) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 2741839940 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 5019589577) ^ 156862174 = 4431685484 := by
        calc
          (3 : ZMod 5019589577) ^ 156862174 = (3 : ZMod 5019589577) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 78431087 * (3 : ZMod 5019589577) ^ 78431087 := by rw [pow_add]
          _ = 4431685484 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 5019589577) ^ 313724348 = 3445139459 := by
        calc
          (3 : ZMod 5019589577) ^ 313724348 = (3 : ZMod 5019589577) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 156862174 * (3 : ZMod 5019589577) ^ 156862174 := by rw [pow_add]
          _ = 3445139459 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 5019589577) ^ 627448697 = 3987909319 := by
        calc
          (3 : ZMod 5019589577) ^ 627448697 = (3 : ZMod 5019589577) ^ (313724348 + 313724348 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 313724348 * (3 : ZMod 5019589577) ^ 313724348) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3987909319 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 5019589577) ^ 1254897394 = 328621328 := by
        calc
          (3 : ZMod 5019589577) ^ 1254897394 = (3 : ZMod 5019589577) ^ (627448697 + 627448697) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 627448697 * (3 : ZMod 5019589577) ^ 627448697 := by rw [pow_add]
          _ = 328621328 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 5019589577) ^ 2509794788 = 5019589576 := by
        calc
          (3 : ZMod 5019589577) ^ 2509794788 = (3 : ZMod 5019589577) ^ (1254897394 + 1254897394) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 1254897394 * (3 : ZMod 5019589577) ^ 1254897394 := by rw [pow_add]
          _ = 5019589576 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 5019589577) ^ 5019589576 = 1 := by
        calc
          (3 : ZMod 5019589577) ^ 5019589576 = (3 : ZMod 5019589577) ^ (2509794788 + 2509794788) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 2509794788 * (3 : ZMod 5019589577) ^ 2509794788 := by rw [pow_add]
          _ = 1 := by rw [fermat_31]; decide
      simpa using fermat_32
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (627448697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (627448697, 1)] : List FactorBlock).map factorBlockValue).prod = 5019589577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_627448697) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 5019589577) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 5019589577) ^ 2 = 9 := by
        calc
          (3 : ZMod 5019589577) ^ 2 = (3 : ZMod 5019589577) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 1 * (3 : ZMod 5019589577) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 5019589577) ^ 4 = 81 := by
        calc
          (3 : ZMod 5019589577) ^ 4 = (3 : ZMod 5019589577) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 2 * (3 : ZMod 5019589577) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 5019589577) ^ 9 = 19683 := by
        calc
          (3 : ZMod 5019589577) ^ 9 = (3 : ZMod 5019589577) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 4 * (3 : ZMod 5019589577) ^ 4) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 5019589577) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 5019589577) ^ 18 = (3 : ZMod 5019589577) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 9 * (3 : ZMod 5019589577) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 5019589577) ^ 37 = 1558778992 := by
        calc
          (3 : ZMod 5019589577) ^ 37 = (3 : ZMod 5019589577) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 18 * (3 : ZMod 5019589577) ^ 18) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 1558778992 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 5019589577) ^ 74 = 3527459189 := by
        calc
          (3 : ZMod 5019589577) ^ 74 = (3 : ZMod 5019589577) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 37 * (3 : ZMod 5019589577) ^ 37 := by rw [pow_add]
          _ = 3527459189 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 5019589577) ^ 149 = 3231705559 := by
        calc
          (3 : ZMod 5019589577) ^ 149 = (3 : ZMod 5019589577) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 74 * (3 : ZMod 5019589577) ^ 74) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3231705559 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 5019589577) ^ 299 = 3096110961 := by
        calc
          (3 : ZMod 5019589577) ^ 299 = (3 : ZMod 5019589577) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 149 * (3 : ZMod 5019589577) ^ 149) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3096110961 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 5019589577) ^ 598 = 464232438 := by
        calc
          (3 : ZMod 5019589577) ^ 598 = (3 : ZMod 5019589577) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 299 * (3 : ZMod 5019589577) ^ 299 := by rw [pow_add]
          _ = 464232438 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 5019589577) ^ 1196 = 4889144218 := by
        calc
          (3 : ZMod 5019589577) ^ 1196 = (3 : ZMod 5019589577) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 598 * (3 : ZMod 5019589577) ^ 598 := by rw [pow_add]
          _ = 4889144218 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 5019589577) ^ 2393 = 3953220893 := by
        calc
          (3 : ZMod 5019589577) ^ 2393 = (3 : ZMod 5019589577) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 1196 * (3 : ZMod 5019589577) ^ 1196) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3953220893 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 5019589577) ^ 4787 = 1433214522 := by
        calc
          (3 : ZMod 5019589577) ^ 4787 = (3 : ZMod 5019589577) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 2393 * (3 : ZMod 5019589577) ^ 2393) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 1433214522 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 5019589577) ^ 9574 = 3482818023 := by
        calc
          (3 : ZMod 5019589577) ^ 9574 = (3 : ZMod 5019589577) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 4787 * (3 : ZMod 5019589577) ^ 4787 := by rw [pow_add]
          _ = 3482818023 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 5019589577) ^ 19148 = 3689463799 := by
        calc
          (3 : ZMod 5019589577) ^ 19148 = (3 : ZMod 5019589577) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 9574 * (3 : ZMod 5019589577) ^ 9574 := by rw [pow_add]
          _ = 3689463799 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 5019589577) ^ 38296 = 747066939 := by
        calc
          (3 : ZMod 5019589577) ^ 38296 = (3 : ZMod 5019589577) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 19148 * (3 : ZMod 5019589577) ^ 19148 := by rw [pow_add]
          _ = 747066939 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 5019589577) ^ 76592 = 1034025553 := by
        calc
          (3 : ZMod 5019589577) ^ 76592 = (3 : ZMod 5019589577) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 38296 * (3 : ZMod 5019589577) ^ 38296 := by rw [pow_add]
          _ = 1034025553 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 5019589577) ^ 153185 = 3502965106 := by
        calc
          (3 : ZMod 5019589577) ^ 153185 = (3 : ZMod 5019589577) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 76592 * (3 : ZMod 5019589577) ^ 76592) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3502965106 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 5019589577) ^ 306371 = 246018377 := by
        calc
          (3 : ZMod 5019589577) ^ 306371 = (3 : ZMod 5019589577) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 153185 * (3 : ZMod 5019589577) ^ 153185) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 246018377 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 5019589577) ^ 612742 = 266619570 := by
        calc
          (3 : ZMod 5019589577) ^ 612742 = (3 : ZMod 5019589577) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 306371 * (3 : ZMod 5019589577) ^ 306371 := by rw [pow_add]
          _ = 266619570 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 5019589577) ^ 1225485 = 4340800189 := by
        calc
          (3 : ZMod 5019589577) ^ 1225485 = (3 : ZMod 5019589577) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 612742 * (3 : ZMod 5019589577) ^ 612742) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 4340800189 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 5019589577) ^ 2450971 = 2119569353 := by
        calc
          (3 : ZMod 5019589577) ^ 2450971 = (3 : ZMod 5019589577) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 1225485 * (3 : ZMod 5019589577) ^ 1225485) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 2119569353 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 5019589577) ^ 4901942 = 3540551472 := by
        calc
          (3 : ZMod 5019589577) ^ 4901942 = (3 : ZMod 5019589577) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 2450971 * (3 : ZMod 5019589577) ^ 2450971 := by rw [pow_add]
          _ = 3540551472 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 5019589577) ^ 9803885 = 1062644159 := by
        calc
          (3 : ZMod 5019589577) ^ 9803885 = (3 : ZMod 5019589577) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 4901942 * (3 : ZMod 5019589577) ^ 4901942) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 1062644159 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 5019589577) ^ 19607771 = 72032310 := by
        calc
          (3 : ZMod 5019589577) ^ 19607771 = (3 : ZMod 5019589577) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 9803885 * (3 : ZMod 5019589577) ^ 9803885) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 72032310 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 5019589577) ^ 39215543 = 2950769066 := by
        calc
          (3 : ZMod 5019589577) ^ 39215543 = (3 : ZMod 5019589577) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 19607771 * (3 : ZMod 5019589577) ^ 19607771) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 2950769066 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 5019589577) ^ 78431087 = 2741839940 := by
        calc
          (3 : ZMod 5019589577) ^ 78431087 = (3 : ZMod 5019589577) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 39215543 * (3 : ZMod 5019589577) ^ 39215543) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 2741839940 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 5019589577) ^ 156862174 = 4431685484 := by
        calc
          (3 : ZMod 5019589577) ^ 156862174 = (3 : ZMod 5019589577) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 78431087 * (3 : ZMod 5019589577) ^ 78431087 := by rw [pow_add]
          _ = 4431685484 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 5019589577) ^ 313724348 = 3445139459 := by
        calc
          (3 : ZMod 5019589577) ^ 313724348 = (3 : ZMod 5019589577) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 156862174 * (3 : ZMod 5019589577) ^ 156862174 := by rw [pow_add]
          _ = 3445139459 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 5019589577) ^ 627448697 = 3987909319 := by
        calc
          (3 : ZMod 5019589577) ^ 627448697 = (3 : ZMod 5019589577) ^ (313724348 + 313724348 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = ((3 : ZMod 5019589577) ^ 313724348 * (3 : ZMod 5019589577) ^ 313724348) * (3 : ZMod 5019589577) := by rw [pow_succ, pow_add]
          _ = 3987909319 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 5019589577) ^ 1254897394 = 328621328 := by
        calc
          (3 : ZMod 5019589577) ^ 1254897394 = (3 : ZMod 5019589577) ^ (627448697 + 627448697) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 627448697 * (3 : ZMod 5019589577) ^ 627448697 := by rw [pow_add]
          _ = 328621328 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 5019589577) ^ 2509794788 = 5019589576 := by
        calc
          (3 : ZMod 5019589577) ^ 2509794788 = (3 : ZMod 5019589577) ^ (1254897394 + 1254897394) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 1254897394 * (3 : ZMod 5019589577) ^ 1254897394 := by rw [pow_add]
          _ = 5019589576 := by rw [factor_0_30]; decide
      change (3 : ZMod 5019589577) ^ 2509794788 ≠ 1
      rw [factor_0_31]
      decide
    ·
      have factor_1_0 : (3 : ZMod 5019589577) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 5019589577) ^ 2 = 9 := by
        calc
          (3 : ZMod 5019589577) ^ 2 = (3 : ZMod 5019589577) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 1 * (3 : ZMod 5019589577) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 5019589577) ^ 4 = 81 := by
        calc
          (3 : ZMod 5019589577) ^ 4 = (3 : ZMod 5019589577) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 2 * (3 : ZMod 5019589577) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 5019589577) ^ 8 = 6561 := by
        calc
          (3 : ZMod 5019589577) ^ 8 = (3 : ZMod 5019589577) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 5019589577) ^ n) (by norm_num)
          _ = (3 : ZMod 5019589577) ^ 4 * (3 : ZMod 5019589577) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      change (3 : ZMod 5019589577) ^ 8 ≠ 1
      rw [factor_1_3]
      decide

#print axioms prime_lucas_5019589577

end TotientTailPeriodKiller
end Erdos249257
