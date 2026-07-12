import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2677114441

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_80313433231 : Nat.Prime 80313433231 := by
  apply lucas_primality 80313433231 (6 : ZMod 80313433231)
  ·
      have fermat_0 : (6 : ZMod 80313433231) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 80313433231) ^ 2 = 36 := by
        calc
          (6 : ZMod 80313433231) ^ 2 = (6 : ZMod 80313433231) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 1 * (6 : ZMod 80313433231) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 80313433231) ^ 4 = 1296 := by
        calc
          (6 : ZMod 80313433231) ^ 4 = (6 : ZMod 80313433231) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 2 * (6 : ZMod 80313433231) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 80313433231) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 80313433231) ^ 9 = (6 : ZMod 80313433231) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 4 * (6 : ZMod 80313433231) ^ 4) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 80313433231) ^ 18 = 43777064432 := by
        calc
          (6 : ZMod 80313433231) ^ 18 = (6 : ZMod 80313433231) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 9 * (6 : ZMod 80313433231) ^ 9 := by rw [pow_add]
          _ = 43777064432 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 80313433231) ^ 37 = 54105733760 := by
        calc
          (6 : ZMod 80313433231) ^ 37 = (6 : ZMod 80313433231) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 18 * (6 : ZMod 80313433231) ^ 18) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 54105733760 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 80313433231) ^ 74 = 23652141287 := by
        calc
          (6 : ZMod 80313433231) ^ 74 = (6 : ZMod 80313433231) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 37 * (6 : ZMod 80313433231) ^ 37 := by rw [pow_add]
          _ = 23652141287 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 80313433231) ^ 149 = 31269276109 := by
        calc
          (6 : ZMod 80313433231) ^ 149 = (6 : ZMod 80313433231) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 74 * (6 : ZMod 80313433231) ^ 74) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 31269276109 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 80313433231) ^ 299 = 19730696844 := by
        calc
          (6 : ZMod 80313433231) ^ 299 = (6 : ZMod 80313433231) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 149 * (6 : ZMod 80313433231) ^ 149) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 19730696844 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 80313433231) ^ 598 = 74234489612 := by
        calc
          (6 : ZMod 80313433231) ^ 598 = (6 : ZMod 80313433231) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 299 * (6 : ZMod 80313433231) ^ 299 := by rw [pow_add]
          _ = 74234489612 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 80313433231) ^ 1196 = 44958264066 := by
        calc
          (6 : ZMod 80313433231) ^ 1196 = (6 : ZMod 80313433231) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 598 * (6 : ZMod 80313433231) ^ 598 := by rw [pow_add]
          _ = 44958264066 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 80313433231) ^ 2393 = 15051263488 := by
        calc
          (6 : ZMod 80313433231) ^ 2393 = (6 : ZMod 80313433231) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1196 * (6 : ZMod 80313433231) ^ 1196) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 15051263488 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 80313433231) ^ 4787 = 80228022041 := by
        calc
          (6 : ZMod 80313433231) ^ 4787 = (6 : ZMod 80313433231) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 2393 * (6 : ZMod 80313433231) ^ 2393) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 80228022041 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 80313433231) ^ 9574 = 41609977908 := by
        calc
          (6 : ZMod 80313433231) ^ 9574 = (6 : ZMod 80313433231) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 4787 * (6 : ZMod 80313433231) ^ 4787 := by rw [pow_add]
          _ = 41609977908 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 80313433231) ^ 19148 = 23263778577 := by
        calc
          (6 : ZMod 80313433231) ^ 19148 = (6 : ZMod 80313433231) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 9574 * (6 : ZMod 80313433231) ^ 9574 := by rw [pow_add]
          _ = 23263778577 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 80313433231) ^ 38296 = 60072240084 := by
        calc
          (6 : ZMod 80313433231) ^ 38296 = (6 : ZMod 80313433231) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 19148 * (6 : ZMod 80313433231) ^ 19148 := by rw [pow_add]
          _ = 60072240084 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 80313433231) ^ 76592 = 71322397807 := by
        calc
          (6 : ZMod 80313433231) ^ 76592 = (6 : ZMod 80313433231) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 38296 * (6 : ZMod 80313433231) ^ 38296 := by rw [pow_add]
          _ = 71322397807 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 80313433231) ^ 153185 = 10318852208 := by
        calc
          (6 : ZMod 80313433231) ^ 153185 = (6 : ZMod 80313433231) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 76592 * (6 : ZMod 80313433231) ^ 76592) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 10318852208 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 80313433231) ^ 306371 = 494071585 := by
        calc
          (6 : ZMod 80313433231) ^ 306371 = (6 : ZMod 80313433231) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 153185 * (6 : ZMod 80313433231) ^ 153185) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 494071585 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 80313433231) ^ 612742 = 74306280050 := by
        calc
          (6 : ZMod 80313433231) ^ 612742 = (6 : ZMod 80313433231) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 306371 * (6 : ZMod 80313433231) ^ 306371 := by rw [pow_add]
          _ = 74306280050 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 80313433231) ^ 1225485 = 66694978534 := by
        calc
          (6 : ZMod 80313433231) ^ 1225485 = (6 : ZMod 80313433231) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 612742 * (6 : ZMod 80313433231) ^ 612742) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 66694978534 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 80313433231) ^ 2450971 = 61087999881 := by
        calc
          (6 : ZMod 80313433231) ^ 2450971 = (6 : ZMod 80313433231) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1225485 * (6 : ZMod 80313433231) ^ 1225485) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 61087999881 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 80313433231) ^ 4901942 = 63157066549 := by
        calc
          (6 : ZMod 80313433231) ^ 4901942 = (6 : ZMod 80313433231) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 2450971 * (6 : ZMod 80313433231) ^ 2450971 := by rw [pow_add]
          _ = 63157066549 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 80313433231) ^ 9803885 = 49546021477 := by
        calc
          (6 : ZMod 80313433231) ^ 9803885 = (6 : ZMod 80313433231) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 4901942 * (6 : ZMod 80313433231) ^ 4901942) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 49546021477 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 80313433231) ^ 19607771 = 34239834504 := by
        calc
          (6 : ZMod 80313433231) ^ 19607771 = (6 : ZMod 80313433231) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 9803885 * (6 : ZMod 80313433231) ^ 9803885) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 34239834504 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 80313433231) ^ 39215543 = 42464079315 := by
        calc
          (6 : ZMod 80313433231) ^ 39215543 = (6 : ZMod 80313433231) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 19607771 * (6 : ZMod 80313433231) ^ 19607771) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 42464079315 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 80313433231) ^ 78431087 = 73885154286 := by
        calc
          (6 : ZMod 80313433231) ^ 78431087 = (6 : ZMod 80313433231) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 39215543 * (6 : ZMod 80313433231) ^ 39215543) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 73885154286 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 80313433231) ^ 156862174 = 29224135459 := by
        calc
          (6 : ZMod 80313433231) ^ 156862174 = (6 : ZMod 80313433231) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 78431087 * (6 : ZMod 80313433231) ^ 78431087 := by rw [pow_add]
          _ = 29224135459 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 80313433231) ^ 313724348 = 42496907943 := by
        calc
          (6 : ZMod 80313433231) ^ 313724348 = (6 : ZMod 80313433231) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 156862174 * (6 : ZMod 80313433231) ^ 156862174 := by rw [pow_add]
          _ = 42496907943 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 80313433231) ^ 627448697 = 80208223798 := by
        calc
          (6 : ZMod 80313433231) ^ 627448697 = (6 : ZMod 80313433231) ^ (313724348 + 313724348 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 313724348 * (6 : ZMod 80313433231) ^ 313724348) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 80208223798 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 80313433231) ^ 1254897394 = 66797418607 := by
        calc
          (6 : ZMod 80313433231) ^ 1254897394 = (6 : ZMod 80313433231) ^ (627448697 + 627448697) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 627448697 * (6 : ZMod 80313433231) ^ 627448697 := by rw [pow_add]
          _ = 66797418607 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 80313433231) ^ 2509794788 = 31821414599 := by
        calc
          (6 : ZMod 80313433231) ^ 2509794788 = (6 : ZMod 80313433231) ^ (1254897394 + 1254897394) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 1254897394 * (6 : ZMod 80313433231) ^ 1254897394 := by rw [pow_add]
          _ = 31821414599 := by rw [fermat_30]; decide
      have fermat_32 : (6 : ZMod 80313433231) ^ 5019589576 = 19561814630 := by
        calc
          (6 : ZMod 80313433231) ^ 5019589576 = (6 : ZMod 80313433231) ^ (2509794788 + 2509794788) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 2509794788 * (6 : ZMod 80313433231) ^ 2509794788 := by rw [pow_add]
          _ = 19561814630 := by rw [fermat_31]; decide
      have fermat_33 : (6 : ZMod 80313433231) ^ 10039179153 = 47097743946 := by
        calc
          (6 : ZMod 80313433231) ^ 10039179153 = (6 : ZMod 80313433231) ^ (5019589576 + 5019589576 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 5019589576 * (6 : ZMod 80313433231) ^ 5019589576) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 47097743946 := by rw [fermat_32]; decide
      have fermat_34 : (6 : ZMod 80313433231) ^ 20078358307 = 54897811377 := by
        calc
          (6 : ZMod 80313433231) ^ 20078358307 = (6 : ZMod 80313433231) ^ (10039179153 + 10039179153 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 10039179153 * (6 : ZMod 80313433231) ^ 10039179153) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 54897811377 := by rw [fermat_33]; decide
      have fermat_35 : (6 : ZMod 80313433231) ^ 40156716615 = 80313433230 := by
        calc
          (6 : ZMod 80313433231) ^ 40156716615 = (6 : ZMod 80313433231) ^ (20078358307 + 20078358307 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 20078358307 * (6 : ZMod 80313433231) ^ 20078358307) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 80313433230 := by rw [fermat_34]; decide
      have fermat_36 : (6 : ZMod 80313433231) ^ 80313433230 = 1 := by
        calc
          (6 : ZMod 80313433231) ^ 80313433230 = (6 : ZMod 80313433231) ^ (40156716615 + 40156716615) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 40156716615 * (6 : ZMod 80313433231) ^ 40156716615 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (2677114441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (2677114441, 1)] : List FactorBlock).map factorBlockValue).prod = 80313433231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_2677114441) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 80313433231) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 80313433231) ^ 2 = 36 := by
        calc
          (6 : ZMod 80313433231) ^ 2 = (6 : ZMod 80313433231) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 1 * (6 : ZMod 80313433231) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 80313433231) ^ 4 = 1296 := by
        calc
          (6 : ZMod 80313433231) ^ 4 = (6 : ZMod 80313433231) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 2 * (6 : ZMod 80313433231) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 80313433231) ^ 9 = 10077696 := by
        calc
          (6 : ZMod 80313433231) ^ 9 = (6 : ZMod 80313433231) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 4 * (6 : ZMod 80313433231) ^ 4) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 10077696 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 80313433231) ^ 18 = 43777064432 := by
        calc
          (6 : ZMod 80313433231) ^ 18 = (6 : ZMod 80313433231) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 9 * (6 : ZMod 80313433231) ^ 9 := by rw [pow_add]
          _ = 43777064432 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 80313433231) ^ 37 = 54105733760 := by
        calc
          (6 : ZMod 80313433231) ^ 37 = (6 : ZMod 80313433231) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 18 * (6 : ZMod 80313433231) ^ 18) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 54105733760 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 80313433231) ^ 74 = 23652141287 := by
        calc
          (6 : ZMod 80313433231) ^ 74 = (6 : ZMod 80313433231) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 37 * (6 : ZMod 80313433231) ^ 37 := by rw [pow_add]
          _ = 23652141287 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 80313433231) ^ 149 = 31269276109 := by
        calc
          (6 : ZMod 80313433231) ^ 149 = (6 : ZMod 80313433231) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 74 * (6 : ZMod 80313433231) ^ 74) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 31269276109 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 80313433231) ^ 299 = 19730696844 := by
        calc
          (6 : ZMod 80313433231) ^ 299 = (6 : ZMod 80313433231) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 149 * (6 : ZMod 80313433231) ^ 149) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 19730696844 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 80313433231) ^ 598 = 74234489612 := by
        calc
          (6 : ZMod 80313433231) ^ 598 = (6 : ZMod 80313433231) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 299 * (6 : ZMod 80313433231) ^ 299 := by rw [pow_add]
          _ = 74234489612 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 80313433231) ^ 1196 = 44958264066 := by
        calc
          (6 : ZMod 80313433231) ^ 1196 = (6 : ZMod 80313433231) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 598 * (6 : ZMod 80313433231) ^ 598 := by rw [pow_add]
          _ = 44958264066 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 80313433231) ^ 2393 = 15051263488 := by
        calc
          (6 : ZMod 80313433231) ^ 2393 = (6 : ZMod 80313433231) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1196 * (6 : ZMod 80313433231) ^ 1196) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 15051263488 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 80313433231) ^ 4787 = 80228022041 := by
        calc
          (6 : ZMod 80313433231) ^ 4787 = (6 : ZMod 80313433231) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 2393 * (6 : ZMod 80313433231) ^ 2393) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 80228022041 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 80313433231) ^ 9574 = 41609977908 := by
        calc
          (6 : ZMod 80313433231) ^ 9574 = (6 : ZMod 80313433231) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 4787 * (6 : ZMod 80313433231) ^ 4787 := by rw [pow_add]
          _ = 41609977908 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 80313433231) ^ 19148 = 23263778577 := by
        calc
          (6 : ZMod 80313433231) ^ 19148 = (6 : ZMod 80313433231) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 9574 * (6 : ZMod 80313433231) ^ 9574 := by rw [pow_add]
          _ = 23263778577 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 80313433231) ^ 38296 = 60072240084 := by
        calc
          (6 : ZMod 80313433231) ^ 38296 = (6 : ZMod 80313433231) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 19148 * (6 : ZMod 80313433231) ^ 19148 := by rw [pow_add]
          _ = 60072240084 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 80313433231) ^ 76592 = 71322397807 := by
        calc
          (6 : ZMod 80313433231) ^ 76592 = (6 : ZMod 80313433231) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 38296 * (6 : ZMod 80313433231) ^ 38296 := by rw [pow_add]
          _ = 71322397807 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 80313433231) ^ 153185 = 10318852208 := by
        calc
          (6 : ZMod 80313433231) ^ 153185 = (6 : ZMod 80313433231) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 76592 * (6 : ZMod 80313433231) ^ 76592) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 10318852208 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 80313433231) ^ 306371 = 494071585 := by
        calc
          (6 : ZMod 80313433231) ^ 306371 = (6 : ZMod 80313433231) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 153185 * (6 : ZMod 80313433231) ^ 153185) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 494071585 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 80313433231) ^ 612742 = 74306280050 := by
        calc
          (6 : ZMod 80313433231) ^ 612742 = (6 : ZMod 80313433231) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 306371 * (6 : ZMod 80313433231) ^ 306371 := by rw [pow_add]
          _ = 74306280050 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 80313433231) ^ 1225485 = 66694978534 := by
        calc
          (6 : ZMod 80313433231) ^ 1225485 = (6 : ZMod 80313433231) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 612742 * (6 : ZMod 80313433231) ^ 612742) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 66694978534 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 80313433231) ^ 2450971 = 61087999881 := by
        calc
          (6 : ZMod 80313433231) ^ 2450971 = (6 : ZMod 80313433231) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1225485 * (6 : ZMod 80313433231) ^ 1225485) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 61087999881 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 80313433231) ^ 4901942 = 63157066549 := by
        calc
          (6 : ZMod 80313433231) ^ 4901942 = (6 : ZMod 80313433231) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 2450971 * (6 : ZMod 80313433231) ^ 2450971 := by rw [pow_add]
          _ = 63157066549 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 80313433231) ^ 9803885 = 49546021477 := by
        calc
          (6 : ZMod 80313433231) ^ 9803885 = (6 : ZMod 80313433231) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 4901942 * (6 : ZMod 80313433231) ^ 4901942) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 49546021477 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 80313433231) ^ 19607771 = 34239834504 := by
        calc
          (6 : ZMod 80313433231) ^ 19607771 = (6 : ZMod 80313433231) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 9803885 * (6 : ZMod 80313433231) ^ 9803885) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 34239834504 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 80313433231) ^ 39215543 = 42464079315 := by
        calc
          (6 : ZMod 80313433231) ^ 39215543 = (6 : ZMod 80313433231) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 19607771 * (6 : ZMod 80313433231) ^ 19607771) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 42464079315 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 80313433231) ^ 78431087 = 73885154286 := by
        calc
          (6 : ZMod 80313433231) ^ 78431087 = (6 : ZMod 80313433231) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 39215543 * (6 : ZMod 80313433231) ^ 39215543) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 73885154286 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 80313433231) ^ 156862174 = 29224135459 := by
        calc
          (6 : ZMod 80313433231) ^ 156862174 = (6 : ZMod 80313433231) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 78431087 * (6 : ZMod 80313433231) ^ 78431087 := by rw [pow_add]
          _ = 29224135459 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 80313433231) ^ 313724348 = 42496907943 := by
        calc
          (6 : ZMod 80313433231) ^ 313724348 = (6 : ZMod 80313433231) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 156862174 * (6 : ZMod 80313433231) ^ 156862174 := by rw [pow_add]
          _ = 42496907943 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 80313433231) ^ 627448697 = 80208223798 := by
        calc
          (6 : ZMod 80313433231) ^ 627448697 = (6 : ZMod 80313433231) ^ (313724348 + 313724348 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 313724348 * (6 : ZMod 80313433231) ^ 313724348) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 80208223798 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 80313433231) ^ 1254897394 = 66797418607 := by
        calc
          (6 : ZMod 80313433231) ^ 1254897394 = (6 : ZMod 80313433231) ^ (627448697 + 627448697) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 627448697 * (6 : ZMod 80313433231) ^ 627448697 := by rw [pow_add]
          _ = 66797418607 := by rw [factor_0_29]; decide
      have factor_0_31 : (6 : ZMod 80313433231) ^ 2509794788 = 31821414599 := by
        calc
          (6 : ZMod 80313433231) ^ 2509794788 = (6 : ZMod 80313433231) ^ (1254897394 + 1254897394) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 1254897394 * (6 : ZMod 80313433231) ^ 1254897394 := by rw [pow_add]
          _ = 31821414599 := by rw [factor_0_30]; decide
      have factor_0_32 : (6 : ZMod 80313433231) ^ 5019589576 = 19561814630 := by
        calc
          (6 : ZMod 80313433231) ^ 5019589576 = (6 : ZMod 80313433231) ^ (2509794788 + 2509794788) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 2509794788 * (6 : ZMod 80313433231) ^ 2509794788 := by rw [pow_add]
          _ = 19561814630 := by rw [factor_0_31]; decide
      have factor_0_33 : (6 : ZMod 80313433231) ^ 10039179153 = 47097743946 := by
        calc
          (6 : ZMod 80313433231) ^ 10039179153 = (6 : ZMod 80313433231) ^ (5019589576 + 5019589576 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 5019589576 * (6 : ZMod 80313433231) ^ 5019589576) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 47097743946 := by rw [factor_0_32]; decide
      have factor_0_34 : (6 : ZMod 80313433231) ^ 20078358307 = 54897811377 := by
        calc
          (6 : ZMod 80313433231) ^ 20078358307 = (6 : ZMod 80313433231) ^ (10039179153 + 10039179153 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 10039179153 * (6 : ZMod 80313433231) ^ 10039179153) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 54897811377 := by rw [factor_0_33]; decide
      have factor_0_35 : (6 : ZMod 80313433231) ^ 40156716615 = 80313433230 := by
        calc
          (6 : ZMod 80313433231) ^ 40156716615 = (6 : ZMod 80313433231) ^ (20078358307 + 20078358307 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 20078358307 * (6 : ZMod 80313433231) ^ 20078358307) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 80313433230 := by rw [factor_0_34]; decide
      change (6 : ZMod 80313433231) ^ 40156716615 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (6 : ZMod 80313433231) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 80313433231) ^ 3 = 216 := by
        calc
          (6 : ZMod 80313433231) ^ 3 = (6 : ZMod 80313433231) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1 * (6 : ZMod 80313433231) ^ 1) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 80313433231) ^ 6 = 46656 := by
        calc
          (6 : ZMod 80313433231) ^ 6 = (6 : ZMod 80313433231) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 3 * (6 : ZMod 80313433231) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 80313433231) ^ 12 = 2176782336 := by
        calc
          (6 : ZMod 80313433231) ^ 12 = (6 : ZMod 80313433231) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 6 * (6 : ZMod 80313433231) ^ 6 := by rw [pow_add]
          _ = 2176782336 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 80313433231) ^ 24 = 11797641831 := by
        calc
          (6 : ZMod 80313433231) ^ 24 = (6 : ZMod 80313433231) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 12 * (6 : ZMod 80313433231) ^ 12 := by rw [pow_add]
          _ = 11797641831 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 80313433231) ^ 49 = 33274162836 := by
        calc
          (6 : ZMod 80313433231) ^ 49 = (6 : ZMod 80313433231) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 24 * (6 : ZMod 80313433231) ^ 24) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 33274162836 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 80313433231) ^ 99 = 1203783936 := by
        calc
          (6 : ZMod 80313433231) ^ 99 = (6 : ZMod 80313433231) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 49 * (6 : ZMod 80313433231) ^ 49) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 1203783936 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 80313433231) ^ 199 = 41424718260 := by
        calc
          (6 : ZMod 80313433231) ^ 199 = (6 : ZMod 80313433231) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 99 * (6 : ZMod 80313433231) ^ 99) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 41424718260 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 80313433231) ^ 398 = 79980016361 := by
        calc
          (6 : ZMod 80313433231) ^ 398 = (6 : ZMod 80313433231) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 199 * (6 : ZMod 80313433231) ^ 199 := by rw [pow_add]
          _ = 79980016361 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 80313433231) ^ 797 = 40996256868 := by
        calc
          (6 : ZMod 80313433231) ^ 797 = (6 : ZMod 80313433231) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 398 * (6 : ZMod 80313433231) ^ 398) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 40996256868 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 80313433231) ^ 1595 = 20113041356 := by
        calc
          (6 : ZMod 80313433231) ^ 1595 = (6 : ZMod 80313433231) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 797 * (6 : ZMod 80313433231) ^ 797) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 20113041356 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 80313433231) ^ 3191 = 66142271384 := by
        calc
          (6 : ZMod 80313433231) ^ 3191 = (6 : ZMod 80313433231) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1595 * (6 : ZMod 80313433231) ^ 1595) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 66142271384 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 80313433231) ^ 6382 = 404148902 := by
        calc
          (6 : ZMod 80313433231) ^ 6382 = (6 : ZMod 80313433231) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 3191 * (6 : ZMod 80313433231) ^ 3191 := by rw [pow_add]
          _ = 404148902 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 80313433231) ^ 12765 = 6940514297 := by
        calc
          (6 : ZMod 80313433231) ^ 12765 = (6 : ZMod 80313433231) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 6382 * (6 : ZMod 80313433231) ^ 6382) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 6940514297 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 80313433231) ^ 25530 = 46719767210 := by
        calc
          (6 : ZMod 80313433231) ^ 25530 = (6 : ZMod 80313433231) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 12765 * (6 : ZMod 80313433231) ^ 12765 := by rw [pow_add]
          _ = 46719767210 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 80313433231) ^ 51061 = 71707768513 := by
        calc
          (6 : ZMod 80313433231) ^ 51061 = (6 : ZMod 80313433231) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 25530 * (6 : ZMod 80313433231) ^ 25530) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 71707768513 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 80313433231) ^ 102123 = 77309412182 := by
        calc
          (6 : ZMod 80313433231) ^ 102123 = (6 : ZMod 80313433231) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 51061 * (6 : ZMod 80313433231) ^ 51061) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 77309412182 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 80313433231) ^ 204247 = 20652425480 := by
        calc
          (6 : ZMod 80313433231) ^ 204247 = (6 : ZMod 80313433231) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 102123 * (6 : ZMod 80313433231) ^ 102123) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 20652425480 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 80313433231) ^ 408495 = 5665153707 := by
        calc
          (6 : ZMod 80313433231) ^ 408495 = (6 : ZMod 80313433231) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 204247 * (6 : ZMod 80313433231) ^ 204247) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 5665153707 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 80313433231) ^ 816990 = 40541124092 := by
        calc
          (6 : ZMod 80313433231) ^ 816990 = (6 : ZMod 80313433231) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 408495 * (6 : ZMod 80313433231) ^ 408495 := by rw [pow_add]
          _ = 40541124092 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 80313433231) ^ 1633980 = 40698573305 := by
        calc
          (6 : ZMod 80313433231) ^ 1633980 = (6 : ZMod 80313433231) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 816990 * (6 : ZMod 80313433231) ^ 816990 := by rw [pow_add]
          _ = 40698573305 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 80313433231) ^ 3267961 = 44238898605 := by
        calc
          (6 : ZMod 80313433231) ^ 3267961 = (6 : ZMod 80313433231) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1633980 * (6 : ZMod 80313433231) ^ 1633980) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 44238898605 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 80313433231) ^ 6535923 = 58900591545 := by
        calc
          (6 : ZMod 80313433231) ^ 6535923 = (6 : ZMod 80313433231) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 3267961 * (6 : ZMod 80313433231) ^ 3267961) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 58900591545 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 80313433231) ^ 13071847 = 66659417317 := by
        calc
          (6 : ZMod 80313433231) ^ 13071847 = (6 : ZMod 80313433231) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 6535923 * (6 : ZMod 80313433231) ^ 6535923) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 66659417317 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 80313433231) ^ 26143695 = 29195951334 := by
        calc
          (6 : ZMod 80313433231) ^ 26143695 = (6 : ZMod 80313433231) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 13071847 * (6 : ZMod 80313433231) ^ 13071847) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 29195951334 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 80313433231) ^ 52287391 = 2124465291 := by
        calc
          (6 : ZMod 80313433231) ^ 52287391 = (6 : ZMod 80313433231) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 26143695 * (6 : ZMod 80313433231) ^ 26143695) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 2124465291 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 80313433231) ^ 104574782 = 48441013896 := by
        calc
          (6 : ZMod 80313433231) ^ 104574782 = (6 : ZMod 80313433231) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 52287391 * (6 : ZMod 80313433231) ^ 52287391 := by rw [pow_add]
          _ = 48441013896 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 80313433231) ^ 209149565 = 53443757095 := by
        calc
          (6 : ZMod 80313433231) ^ 209149565 = (6 : ZMod 80313433231) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 104574782 * (6 : ZMod 80313433231) ^ 104574782) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 53443757095 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 80313433231) ^ 418299131 = 20679540587 := by
        calc
          (6 : ZMod 80313433231) ^ 418299131 = (6 : ZMod 80313433231) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 209149565 * (6 : ZMod 80313433231) ^ 209149565) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 20679540587 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 80313433231) ^ 836598262 = 10595610222 := by
        calc
          (6 : ZMod 80313433231) ^ 836598262 = (6 : ZMod 80313433231) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 418299131 * (6 : ZMod 80313433231) ^ 418299131 := by rw [pow_add]
          _ = 10595610222 := by rw [factor_1_28]; decide
      have factor_1_30 : (6 : ZMod 80313433231) ^ 1673196525 = 8620630125 := by
        calc
          (6 : ZMod 80313433231) ^ 1673196525 = (6 : ZMod 80313433231) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 836598262 * (6 : ZMod 80313433231) ^ 836598262) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 8620630125 := by rw [factor_1_29]; decide
      have factor_1_31 : (6 : ZMod 80313433231) ^ 3346393051 = 51875403996 := by
        calc
          (6 : ZMod 80313433231) ^ 3346393051 = (6 : ZMod 80313433231) ^ (1673196525 + 1673196525 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1673196525 * (6 : ZMod 80313433231) ^ 1673196525) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 51875403996 := by rw [factor_1_30]; decide
      have factor_1_32 : (6 : ZMod 80313433231) ^ 6692786102 = 52894854043 := by
        calc
          (6 : ZMod 80313433231) ^ 6692786102 = (6 : ZMod 80313433231) ^ (3346393051 + 3346393051) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 3346393051 * (6 : ZMod 80313433231) ^ 3346393051 := by rw [pow_add]
          _ = 52894854043 := by rw [factor_1_31]; decide
      have factor_1_33 : (6 : ZMod 80313433231) ^ 13385572205 = 32330049189 := by
        calc
          (6 : ZMod 80313433231) ^ 13385572205 = (6 : ZMod 80313433231) ^ (6692786102 + 6692786102 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 6692786102 * (6 : ZMod 80313433231) ^ 6692786102) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 32330049189 := by rw [factor_1_32]; decide
      have factor_1_34 : (6 : ZMod 80313433231) ^ 26771144410 = 32330049188 := by
        calc
          (6 : ZMod 80313433231) ^ 26771144410 = (6 : ZMod 80313433231) ^ (13385572205 + 13385572205) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 13385572205 * (6 : ZMod 80313433231) ^ 13385572205 := by rw [pow_add]
          _ = 32330049188 := by rw [factor_1_33]; decide
      change (6 : ZMod 80313433231) ^ 26771144410 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (6 : ZMod 80313433231) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 80313433231) ^ 3 = 216 := by
        calc
          (6 : ZMod 80313433231) ^ 3 = (6 : ZMod 80313433231) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1 * (6 : ZMod 80313433231) ^ 1) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 80313433231) ^ 7 = 279936 := by
        calc
          (6 : ZMod 80313433231) ^ 7 = (6 : ZMod 80313433231) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 3 * (6 : ZMod 80313433231) ^ 3) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 80313433231) ^ 14 = 78364164096 := by
        calc
          (6 : ZMod 80313433231) ^ 14 = (6 : ZMod 80313433231) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 7 * (6 : ZMod 80313433231) ^ 7 := by rw [pow_add]
          _ = 78364164096 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 80313433231) ^ 29 = 20522128054 := by
        calc
          (6 : ZMod 80313433231) ^ 29 = (6 : ZMod 80313433231) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 14 * (6 : ZMod 80313433231) ^ 14) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 20522128054 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 80313433231) ^ 59 = 15081025128 := by
        calc
          (6 : ZMod 80313433231) ^ 59 = (6 : ZMod 80313433231) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 29 * (6 : ZMod 80313433231) ^ 29) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 15081025128 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 80313433231) ^ 119 = 71521470753 := by
        calc
          (6 : ZMod 80313433231) ^ 119 = (6 : ZMod 80313433231) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 59 * (6 : ZMod 80313433231) ^ 59) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 71521470753 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 80313433231) ^ 239 = 68365492230 := by
        calc
          (6 : ZMod 80313433231) ^ 239 = (6 : ZMod 80313433231) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 119 * (6 : ZMod 80313433231) ^ 119) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 68365492230 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 80313433231) ^ 478 = 35755930862 := by
        calc
          (6 : ZMod 80313433231) ^ 478 = (6 : ZMod 80313433231) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 239 * (6 : ZMod 80313433231) ^ 239 := by rw [pow_add]
          _ = 35755930862 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 80313433231) ^ 957 = 16628277341 := by
        calc
          (6 : ZMod 80313433231) ^ 957 = (6 : ZMod 80313433231) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 478 * (6 : ZMod 80313433231) ^ 478) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 16628277341 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 80313433231) ^ 1914 = 25096595359 := by
        calc
          (6 : ZMod 80313433231) ^ 1914 = (6 : ZMod 80313433231) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 957 * (6 : ZMod 80313433231) ^ 957 := by rw [pow_add]
          _ = 25096595359 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 80313433231) ^ 3829 = 10033532567 := by
        calc
          (6 : ZMod 80313433231) ^ 3829 = (6 : ZMod 80313433231) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1914 * (6 : ZMod 80313433231) ^ 1914) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 10033532567 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 80313433231) ^ 7659 = 4591449657 := by
        calc
          (6 : ZMod 80313433231) ^ 7659 = (6 : ZMod 80313433231) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 3829 * (6 : ZMod 80313433231) ^ 3829) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 4591449657 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 80313433231) ^ 15318 = 70632180446 := by
        calc
          (6 : ZMod 80313433231) ^ 15318 = (6 : ZMod 80313433231) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 7659 * (6 : ZMod 80313433231) ^ 7659 := by rw [pow_add]
          _ = 70632180446 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 80313433231) ^ 30637 = 58933589890 := by
        calc
          (6 : ZMod 80313433231) ^ 30637 = (6 : ZMod 80313433231) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 15318 * (6 : ZMod 80313433231) ^ 15318) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 58933589890 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 80313433231) ^ 61274 = 23242337338 := by
        calc
          (6 : ZMod 80313433231) ^ 61274 = (6 : ZMod 80313433231) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 30637 * (6 : ZMod 80313433231) ^ 30637 := by rw [pow_add]
          _ = 23242337338 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 80313433231) ^ 122548 = 11444646564 := by
        calc
          (6 : ZMod 80313433231) ^ 122548 = (6 : ZMod 80313433231) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 61274 * (6 : ZMod 80313433231) ^ 61274 := by rw [pow_add]
          _ = 11444646564 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 80313433231) ^ 245097 = 14566208183 := by
        calc
          (6 : ZMod 80313433231) ^ 245097 = (6 : ZMod 80313433231) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 122548 * (6 : ZMod 80313433231) ^ 122548) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 14566208183 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 80313433231) ^ 490194 = 62410677075 := by
        calc
          (6 : ZMod 80313433231) ^ 490194 = (6 : ZMod 80313433231) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 245097 * (6 : ZMod 80313433231) ^ 245097 := by rw [pow_add]
          _ = 62410677075 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 80313433231) ^ 980388 = 7443999607 := by
        calc
          (6 : ZMod 80313433231) ^ 980388 = (6 : ZMod 80313433231) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 490194 * (6 : ZMod 80313433231) ^ 490194 := by rw [pow_add]
          _ = 7443999607 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 80313433231) ^ 1960777 = 14715263884 := by
        calc
          (6 : ZMod 80313433231) ^ 1960777 = (6 : ZMod 80313433231) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 980388 * (6 : ZMod 80313433231) ^ 980388) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 14715263884 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 80313433231) ^ 3921554 = 5089105608 := by
        calc
          (6 : ZMod 80313433231) ^ 3921554 = (6 : ZMod 80313433231) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 1960777 * (6 : ZMod 80313433231) ^ 1960777 := by rw [pow_add]
          _ = 5089105608 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 80313433231) ^ 7843108 = 54748024582 := by
        calc
          (6 : ZMod 80313433231) ^ 7843108 = (6 : ZMod 80313433231) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 3921554 * (6 : ZMod 80313433231) ^ 3921554 := by rw [pow_add]
          _ = 54748024582 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 80313433231) ^ 15686217 = 34202408939 := by
        calc
          (6 : ZMod 80313433231) ^ 15686217 = (6 : ZMod 80313433231) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 7843108 * (6 : ZMod 80313433231) ^ 7843108) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 34202408939 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 80313433231) ^ 31372434 = 70668191257 := by
        calc
          (6 : ZMod 80313433231) ^ 31372434 = (6 : ZMod 80313433231) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 15686217 * (6 : ZMod 80313433231) ^ 15686217 := by rw [pow_add]
          _ = 70668191257 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 80313433231) ^ 62744869 = 49276551096 := by
        calc
          (6 : ZMod 80313433231) ^ 62744869 = (6 : ZMod 80313433231) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 31372434 * (6 : ZMod 80313433231) ^ 31372434) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 49276551096 := by rw [factor_2_24]; decide
      have factor_2_26 : (6 : ZMod 80313433231) ^ 125489739 = 11022724920 := by
        calc
          (6 : ZMod 80313433231) ^ 125489739 = (6 : ZMod 80313433231) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 62744869 * (6 : ZMod 80313433231) ^ 62744869) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 11022724920 := by rw [factor_2_25]; decide
      have factor_2_27 : (6 : ZMod 80313433231) ^ 250979478 = 43061173937 := by
        calc
          (6 : ZMod 80313433231) ^ 250979478 = (6 : ZMod 80313433231) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 125489739 * (6 : ZMod 80313433231) ^ 125489739 := by rw [pow_add]
          _ = 43061173937 := by rw [factor_2_26]; decide
      have factor_2_28 : (6 : ZMod 80313433231) ^ 501958957 = 65431986188 := by
        calc
          (6 : ZMod 80313433231) ^ 501958957 = (6 : ZMod 80313433231) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 250979478 * (6 : ZMod 80313433231) ^ 250979478) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 65431986188 := by rw [factor_2_27]; decide
      have factor_2_29 : (6 : ZMod 80313433231) ^ 1003917915 = 71942410930 := by
        calc
          (6 : ZMod 80313433231) ^ 1003917915 = (6 : ZMod 80313433231) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 501958957 * (6 : ZMod 80313433231) ^ 501958957) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 71942410930 := by rw [factor_2_28]; decide
      have factor_2_30 : (6 : ZMod 80313433231) ^ 2007835830 = 67535427500 := by
        calc
          (6 : ZMod 80313433231) ^ 2007835830 = (6 : ZMod 80313433231) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 1003917915 * (6 : ZMod 80313433231) ^ 1003917915 := by rw [pow_add]
          _ = 67535427500 := by rw [factor_2_29]; decide
      have factor_2_31 : (6 : ZMod 80313433231) ^ 4015671661 = 9187953438 := by
        calc
          (6 : ZMod 80313433231) ^ 4015671661 = (6 : ZMod 80313433231) ^ (2007835830 + 2007835830 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 2007835830 * (6 : ZMod 80313433231) ^ 2007835830) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 9187953438 := by rw [factor_2_30]; decide
      have factor_2_32 : (6 : ZMod 80313433231) ^ 8031343323 = 16406226695 := by
        calc
          (6 : ZMod 80313433231) ^ 8031343323 = (6 : ZMod 80313433231) ^ (4015671661 + 4015671661 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 4015671661 * (6 : ZMod 80313433231) ^ 4015671661) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 16406226695 := by rw [factor_2_31]; decide
      have factor_2_33 : (6 : ZMod 80313433231) ^ 16062686646 = 39169093447 := by
        calc
          (6 : ZMod 80313433231) ^ 16062686646 = (6 : ZMod 80313433231) ^ (8031343323 + 8031343323) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 8031343323 * (6 : ZMod 80313433231) ^ 8031343323 := by rw [pow_add]
          _ = 39169093447 := by rw [factor_2_32]; decide
      change (6 : ZMod 80313433231) ^ 16062686646 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (6 : ZMod 80313433231) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 80313433231) ^ 3 = 216 := by
        calc
          (6 : ZMod 80313433231) ^ 3 = (6 : ZMod 80313433231) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 1 * (6 : ZMod 80313433231) ^ 1) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 80313433231) ^ 7 = 279936 := by
        calc
          (6 : ZMod 80313433231) ^ 7 = (6 : ZMod 80313433231) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 3 * (6 : ZMod 80313433231) ^ 3) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 279936 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 80313433231) ^ 15 = 68617818421 := by
        calc
          (6 : ZMod 80313433231) ^ 15 = (6 : ZMod 80313433231) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = ((6 : ZMod 80313433231) ^ 7 * (6 : ZMod 80313433231) ^ 7) * (6 : ZMod 80313433231) := by rw [pow_succ, pow_add]
          _ = 68617818421 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 80313433231) ^ 30 = 42819335093 := by
        calc
          (6 : ZMod 80313433231) ^ 30 = (6 : ZMod 80313433231) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (6 : ZMod 80313433231) ^ n) (by norm_num)
          _ = (6 : ZMod 80313433231) ^ 15 * (6 : ZMod 80313433231) ^ 15 := by rw [pow_add]
          _ = 42819335093 := by rw [factor_3_3]; decide
      change (6 : ZMod 80313433231) ^ 30 ≠ 1
      rw [factor_3_4]
      decide

#print axioms prime_lucas_80313433231

end TotientTailPeriodKiller
end Erdos249257
