import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_258787729201 : Nat.Prime 258787729201 := by
  apply lucas_primality 258787729201 (41 : ZMod 258787729201)
  ·
      have fermat_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have fermat_1 : (41 : ZMod 258787729201) ^ 3 = 68921 := by
        calc
          (41 : ZMod 258787729201) ^ 3 = (41 : ZMod 258787729201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 68921 := by rw [fermat_0]; decide
      have fermat_2 : (41 : ZMod 258787729201) ^ 7 = 194754273881 := by
        calc
          (41 : ZMod 258787729201) ^ 7 = (41 : ZMod 258787729201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 3 * (41 : ZMod 258787729201) ^ 3) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 194754273881 := by rw [fermat_1]; decide
      have fermat_3 : (41 : ZMod 258787729201) ^ 15 = 172138642820 := by
        calc
          (41 : ZMod 258787729201) ^ 15 = (41 : ZMod 258787729201) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 7 * (41 : ZMod 258787729201) ^ 7) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 172138642820 := by rw [fermat_2]; decide
      have fermat_4 : (41 : ZMod 258787729201) ^ 30 = 61540352039 := by
        calc
          (41 : ZMod 258787729201) ^ 30 = (41 : ZMod 258787729201) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 15 * (41 : ZMod 258787729201) ^ 15 := by rw [pow_add]
          _ = 61540352039 := by rw [fermat_3]; decide
      have fermat_5 : (41 : ZMod 258787729201) ^ 60 = 189324702383 := by
        calc
          (41 : ZMod 258787729201) ^ 60 = (41 : ZMod 258787729201) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 30 * (41 : ZMod 258787729201) ^ 30 := by rw [pow_add]
          _ = 189324702383 := by rw [fermat_4]; decide
      have fermat_6 : (41 : ZMod 258787729201) ^ 120 = 106872668011 := by
        calc
          (41 : ZMod 258787729201) ^ 120 = (41 : ZMod 258787729201) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 60 * (41 : ZMod 258787729201) ^ 60 := by rw [pow_add]
          _ = 106872668011 := by rw [fermat_5]; decide
      have fermat_7 : (41 : ZMod 258787729201) ^ 241 = 22397205330 := by
        calc
          (41 : ZMod 258787729201) ^ 241 = (41 : ZMod 258787729201) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 120 * (41 : ZMod 258787729201) ^ 120) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 22397205330 := by rw [fermat_6]; decide
      have fermat_8 : (41 : ZMod 258787729201) ^ 482 = 239229273903 := by
        calc
          (41 : ZMod 258787729201) ^ 482 = (41 : ZMod 258787729201) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 241 * (41 : ZMod 258787729201) ^ 241 := by rw [pow_add]
          _ = 239229273903 := by rw [fermat_7]; decide
      have fermat_9 : (41 : ZMod 258787729201) ^ 964 = 121048456465 := by
        calc
          (41 : ZMod 258787729201) ^ 964 = (41 : ZMod 258787729201) ^ (482 + 482) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 482 * (41 : ZMod 258787729201) ^ 482 := by rw [pow_add]
          _ = 121048456465 := by rw [fermat_8]; decide
      have fermat_10 : (41 : ZMod 258787729201) ^ 1928 = 217067500248 := by
        calc
          (41 : ZMod 258787729201) ^ 1928 = (41 : ZMod 258787729201) ^ (964 + 964) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 964 * (41 : ZMod 258787729201) ^ 964 := by rw [pow_add]
          _ = 217067500248 := by rw [fermat_9]; decide
      have fermat_11 : (41 : ZMod 258787729201) ^ 3856 = 246975521354 := by
        calc
          (41 : ZMod 258787729201) ^ 3856 = (41 : ZMod 258787729201) ^ (1928 + 1928) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1928 * (41 : ZMod 258787729201) ^ 1928 := by rw [pow_add]
          _ = 246975521354 := by rw [fermat_10]; decide
      have fermat_12 : (41 : ZMod 258787729201) ^ 7712 = 251535263997 := by
        calc
          (41 : ZMod 258787729201) ^ 7712 = (41 : ZMod 258787729201) ^ (3856 + 3856) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3856 * (41 : ZMod 258787729201) ^ 3856 := by rw [pow_add]
          _ = 251535263997 := by rw [fermat_11]; decide
      have fermat_13 : (41 : ZMod 258787729201) ^ 15424 = 114316516986 := by
        calc
          (41 : ZMod 258787729201) ^ 15424 = (41 : ZMod 258787729201) ^ (7712 + 7712) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 7712 * (41 : ZMod 258787729201) ^ 7712 := by rw [pow_add]
          _ = 114316516986 := by rw [fermat_12]; decide
      have fermat_14 : (41 : ZMod 258787729201) ^ 30849 = 223772964166 := by
        calc
          (41 : ZMod 258787729201) ^ 30849 = (41 : ZMod 258787729201) ^ (15424 + 15424 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 15424 * (41 : ZMod 258787729201) ^ 15424) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 223772964166 := by rw [fermat_13]; decide
      have fermat_15 : (41 : ZMod 258787729201) ^ 61699 = 101920989498 := by
        calc
          (41 : ZMod 258787729201) ^ 61699 = (41 : ZMod 258787729201) ^ (30849 + 30849 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 30849 * (41 : ZMod 258787729201) ^ 30849) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 101920989498 := by rw [fermat_14]; decide
      have fermat_16 : (41 : ZMod 258787729201) ^ 123399 = 107323811776 := by
        calc
          (41 : ZMod 258787729201) ^ 123399 = (41 : ZMod 258787729201) ^ (61699 + 61699 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 61699 * (41 : ZMod 258787729201) ^ 61699) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 107323811776 := by rw [fermat_15]; decide
      have fermat_17 : (41 : ZMod 258787729201) ^ 246799 = 39650838709 := by
        calc
          (41 : ZMod 258787729201) ^ 246799 = (41 : ZMod 258787729201) ^ (123399 + 123399 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 123399 * (41 : ZMod 258787729201) ^ 123399) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 39650838709 := by rw [fermat_16]; decide
      have fermat_18 : (41 : ZMod 258787729201) ^ 493598 = 86862827334 := by
        calc
          (41 : ZMod 258787729201) ^ 493598 = (41 : ZMod 258787729201) ^ (246799 + 246799) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 246799 * (41 : ZMod 258787729201) ^ 246799 := by rw [pow_add]
          _ = 86862827334 := by rw [fermat_17]; decide
      have fermat_19 : (41 : ZMod 258787729201) ^ 987196 = 229342635469 := by
        calc
          (41 : ZMod 258787729201) ^ 987196 = (41 : ZMod 258787729201) ^ (493598 + 493598) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 493598 * (41 : ZMod 258787729201) ^ 493598 := by rw [pow_add]
          _ = 229342635469 := by rw [fermat_18]; decide
      have fermat_20 : (41 : ZMod 258787729201) ^ 1974393 = 89949404383 := by
        calc
          (41 : ZMod 258787729201) ^ 1974393 = (41 : ZMod 258787729201) ^ (987196 + 987196 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 987196 * (41 : ZMod 258787729201) ^ 987196) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 89949404383 := by rw [fermat_19]; decide
      have fermat_21 : (41 : ZMod 258787729201) ^ 3948787 = 176276307374 := by
        calc
          (41 : ZMod 258787729201) ^ 3948787 = (41 : ZMod 258787729201) ^ (1974393 + 1974393 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1974393 * (41 : ZMod 258787729201) ^ 1974393) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 176276307374 := by rw [fermat_20]; decide
      have fermat_22 : (41 : ZMod 258787729201) ^ 7897574 = 170555070943 := by
        calc
          (41 : ZMod 258787729201) ^ 7897574 = (41 : ZMod 258787729201) ^ (3948787 + 3948787) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3948787 * (41 : ZMod 258787729201) ^ 3948787 := by rw [pow_add]
          _ = 170555070943 := by rw [fermat_21]; decide
      have fermat_23 : (41 : ZMod 258787729201) ^ 15795149 = 233226291559 := by
        calc
          (41 : ZMod 258787729201) ^ 15795149 = (41 : ZMod 258787729201) ^ (7897574 + 7897574 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 7897574 * (41 : ZMod 258787729201) ^ 7897574) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 233226291559 := by rw [fermat_22]; decide
      have fermat_24 : (41 : ZMod 258787729201) ^ 31590298 = 228165492000 := by
        calc
          (41 : ZMod 258787729201) ^ 31590298 = (41 : ZMod 258787729201) ^ (15795149 + 15795149) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 15795149 * (41 : ZMod 258787729201) ^ 15795149 := by rw [pow_add]
          _ = 228165492000 := by rw [fermat_23]; decide
      have fermat_25 : (41 : ZMod 258787729201) ^ 63180597 = 194074477725 := by
        calc
          (41 : ZMod 258787729201) ^ 63180597 = (41 : ZMod 258787729201) ^ (31590298 + 31590298 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 31590298 * (41 : ZMod 258787729201) ^ 31590298) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 194074477725 := by rw [fermat_24]; decide
      have fermat_26 : (41 : ZMod 258787729201) ^ 126361195 = 17944988643 := by
        calc
          (41 : ZMod 258787729201) ^ 126361195 = (41 : ZMod 258787729201) ^ (63180597 + 63180597 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 63180597 * (41 : ZMod 258787729201) ^ 63180597) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 17944988643 := by rw [fermat_25]; decide
      have fermat_27 : (41 : ZMod 258787729201) ^ 252722391 = 98287788926 := by
        calc
          (41 : ZMod 258787729201) ^ 252722391 = (41 : ZMod 258787729201) ^ (126361195 + 126361195 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 126361195 * (41 : ZMod 258787729201) ^ 126361195) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 98287788926 := by rw [fermat_26]; decide
      have fermat_28 : (41 : ZMod 258787729201) ^ 505444783 = 161290476159 := by
        calc
          (41 : ZMod 258787729201) ^ 505444783 = (41 : ZMod 258787729201) ^ (252722391 + 252722391 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 252722391 * (41 : ZMod 258787729201) ^ 252722391) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 161290476159 := by rw [fermat_27]; decide
      have fermat_29 : (41 : ZMod 258787729201) ^ 1010889567 = 191619872792 := by
        calc
          (41 : ZMod 258787729201) ^ 1010889567 = (41 : ZMod 258787729201) ^ (505444783 + 505444783 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 505444783 * (41 : ZMod 258787729201) ^ 505444783) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 191619872792 := by rw [fermat_28]; decide
      have fermat_30 : (41 : ZMod 258787729201) ^ 2021779134 = 832351988 := by
        calc
          (41 : ZMod 258787729201) ^ 2021779134 = (41 : ZMod 258787729201) ^ (1010889567 + 1010889567) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1010889567 * (41 : ZMod 258787729201) ^ 1010889567 := by rw [pow_add]
          _ = 832351988 := by rw [fermat_29]; decide
      have fermat_31 : (41 : ZMod 258787729201) ^ 4043558268 = 144513033009 := by
        calc
          (41 : ZMod 258787729201) ^ 4043558268 = (41 : ZMod 258787729201) ^ (2021779134 + 2021779134) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2021779134 * (41 : ZMod 258787729201) ^ 2021779134 := by rw [pow_add]
          _ = 144513033009 := by rw [fermat_30]; decide
      have fermat_32 : (41 : ZMod 258787729201) ^ 8087116537 = 189832630337 := by
        calc
          (41 : ZMod 258787729201) ^ 8087116537 = (41 : ZMod 258787729201) ^ (4043558268 + 4043558268 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 4043558268 * (41 : ZMod 258787729201) ^ 4043558268) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 189832630337 := by rw [fermat_31]; decide
      have fermat_33 : (41 : ZMod 258787729201) ^ 16174233075 = 204746943496 := by
        calc
          (41 : ZMod 258787729201) ^ 16174233075 = (41 : ZMod 258787729201) ^ (8087116537 + 8087116537 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 8087116537 * (41 : ZMod 258787729201) ^ 8087116537) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 204746943496 := by rw [fermat_32]; decide
      have fermat_34 : (41 : ZMod 258787729201) ^ 32348466150 = 181415155677 := by
        calc
          (41 : ZMod 258787729201) ^ 32348466150 = (41 : ZMod 258787729201) ^ (16174233075 + 16174233075) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 16174233075 * (41 : ZMod 258787729201) ^ 16174233075 := by rw [pow_add]
          _ = 181415155677 := by rw [fermat_33]; decide
      have fermat_35 : (41 : ZMod 258787729201) ^ 64696932300 = 5861368492 := by
        calc
          (41 : ZMod 258787729201) ^ 64696932300 = (41 : ZMod 258787729201) ^ (32348466150 + 32348466150) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 32348466150 * (41 : ZMod 258787729201) ^ 32348466150 := by rw [pow_add]
          _ = 5861368492 := by rw [fermat_34]; decide
      have fermat_36 : (41 : ZMod 258787729201) ^ 129393864600 = 258787729200 := by
        calc
          (41 : ZMod 258787729201) ^ 129393864600 = (41 : ZMod 258787729201) ^ (64696932300 + 64696932300) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 64696932300 * (41 : ZMod 258787729201) ^ 64696932300 := by rw [pow_add]
          _ = 258787729200 := by rw [fermat_35]; decide
      have fermat_37 : (41 : ZMod 258787729201) ^ 258787729200 = 1 := by
        calc
          (41 : ZMod 258787729201) ^ 258787729200 = (41 : ZMod 258787729201) ^ (129393864600 + 129393864600) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 129393864600 * (41 : ZMod 258787729201) ^ 129393864600 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 258787729201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_0_1 : (41 : ZMod 258787729201) ^ 3 = 68921 := by
        calc
          (41 : ZMod 258787729201) ^ 3 = (41 : ZMod 258787729201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 68921 := by rw [factor_0_0]; decide
      have factor_0_2 : (41 : ZMod 258787729201) ^ 7 = 194754273881 := by
        calc
          (41 : ZMod 258787729201) ^ 7 = (41 : ZMod 258787729201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 3 * (41 : ZMod 258787729201) ^ 3) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 194754273881 := by rw [factor_0_1]; decide
      have factor_0_3 : (41 : ZMod 258787729201) ^ 15 = 172138642820 := by
        calc
          (41 : ZMod 258787729201) ^ 15 = (41 : ZMod 258787729201) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 7 * (41 : ZMod 258787729201) ^ 7) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 172138642820 := by rw [factor_0_2]; decide
      have factor_0_4 : (41 : ZMod 258787729201) ^ 30 = 61540352039 := by
        calc
          (41 : ZMod 258787729201) ^ 30 = (41 : ZMod 258787729201) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 15 * (41 : ZMod 258787729201) ^ 15 := by rw [pow_add]
          _ = 61540352039 := by rw [factor_0_3]; decide
      have factor_0_5 : (41 : ZMod 258787729201) ^ 60 = 189324702383 := by
        calc
          (41 : ZMod 258787729201) ^ 60 = (41 : ZMod 258787729201) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 30 * (41 : ZMod 258787729201) ^ 30 := by rw [pow_add]
          _ = 189324702383 := by rw [factor_0_4]; decide
      have factor_0_6 : (41 : ZMod 258787729201) ^ 120 = 106872668011 := by
        calc
          (41 : ZMod 258787729201) ^ 120 = (41 : ZMod 258787729201) ^ (60 + 60) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 60 * (41 : ZMod 258787729201) ^ 60 := by rw [pow_add]
          _ = 106872668011 := by rw [factor_0_5]; decide
      have factor_0_7 : (41 : ZMod 258787729201) ^ 241 = 22397205330 := by
        calc
          (41 : ZMod 258787729201) ^ 241 = (41 : ZMod 258787729201) ^ (120 + 120 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 120 * (41 : ZMod 258787729201) ^ 120) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 22397205330 := by rw [factor_0_6]; decide
      have factor_0_8 : (41 : ZMod 258787729201) ^ 482 = 239229273903 := by
        calc
          (41 : ZMod 258787729201) ^ 482 = (41 : ZMod 258787729201) ^ (241 + 241) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 241 * (41 : ZMod 258787729201) ^ 241 := by rw [pow_add]
          _ = 239229273903 := by rw [factor_0_7]; decide
      have factor_0_9 : (41 : ZMod 258787729201) ^ 964 = 121048456465 := by
        calc
          (41 : ZMod 258787729201) ^ 964 = (41 : ZMod 258787729201) ^ (482 + 482) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 482 * (41 : ZMod 258787729201) ^ 482 := by rw [pow_add]
          _ = 121048456465 := by rw [factor_0_8]; decide
      have factor_0_10 : (41 : ZMod 258787729201) ^ 1928 = 217067500248 := by
        calc
          (41 : ZMod 258787729201) ^ 1928 = (41 : ZMod 258787729201) ^ (964 + 964) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 964 * (41 : ZMod 258787729201) ^ 964 := by rw [pow_add]
          _ = 217067500248 := by rw [factor_0_9]; decide
      have factor_0_11 : (41 : ZMod 258787729201) ^ 3856 = 246975521354 := by
        calc
          (41 : ZMod 258787729201) ^ 3856 = (41 : ZMod 258787729201) ^ (1928 + 1928) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1928 * (41 : ZMod 258787729201) ^ 1928 := by rw [pow_add]
          _ = 246975521354 := by rw [factor_0_10]; decide
      have factor_0_12 : (41 : ZMod 258787729201) ^ 7712 = 251535263997 := by
        calc
          (41 : ZMod 258787729201) ^ 7712 = (41 : ZMod 258787729201) ^ (3856 + 3856) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3856 * (41 : ZMod 258787729201) ^ 3856 := by rw [pow_add]
          _ = 251535263997 := by rw [factor_0_11]; decide
      have factor_0_13 : (41 : ZMod 258787729201) ^ 15424 = 114316516986 := by
        calc
          (41 : ZMod 258787729201) ^ 15424 = (41 : ZMod 258787729201) ^ (7712 + 7712) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 7712 * (41 : ZMod 258787729201) ^ 7712 := by rw [pow_add]
          _ = 114316516986 := by rw [factor_0_12]; decide
      have factor_0_14 : (41 : ZMod 258787729201) ^ 30849 = 223772964166 := by
        calc
          (41 : ZMod 258787729201) ^ 30849 = (41 : ZMod 258787729201) ^ (15424 + 15424 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 15424 * (41 : ZMod 258787729201) ^ 15424) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 223772964166 := by rw [factor_0_13]; decide
      have factor_0_15 : (41 : ZMod 258787729201) ^ 61699 = 101920989498 := by
        calc
          (41 : ZMod 258787729201) ^ 61699 = (41 : ZMod 258787729201) ^ (30849 + 30849 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 30849 * (41 : ZMod 258787729201) ^ 30849) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 101920989498 := by rw [factor_0_14]; decide
      have factor_0_16 : (41 : ZMod 258787729201) ^ 123399 = 107323811776 := by
        calc
          (41 : ZMod 258787729201) ^ 123399 = (41 : ZMod 258787729201) ^ (61699 + 61699 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 61699 * (41 : ZMod 258787729201) ^ 61699) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 107323811776 := by rw [factor_0_15]; decide
      have factor_0_17 : (41 : ZMod 258787729201) ^ 246799 = 39650838709 := by
        calc
          (41 : ZMod 258787729201) ^ 246799 = (41 : ZMod 258787729201) ^ (123399 + 123399 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 123399 * (41 : ZMod 258787729201) ^ 123399) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 39650838709 := by rw [factor_0_16]; decide
      have factor_0_18 : (41 : ZMod 258787729201) ^ 493598 = 86862827334 := by
        calc
          (41 : ZMod 258787729201) ^ 493598 = (41 : ZMod 258787729201) ^ (246799 + 246799) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 246799 * (41 : ZMod 258787729201) ^ 246799 := by rw [pow_add]
          _ = 86862827334 := by rw [factor_0_17]; decide
      have factor_0_19 : (41 : ZMod 258787729201) ^ 987196 = 229342635469 := by
        calc
          (41 : ZMod 258787729201) ^ 987196 = (41 : ZMod 258787729201) ^ (493598 + 493598) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 493598 * (41 : ZMod 258787729201) ^ 493598 := by rw [pow_add]
          _ = 229342635469 := by rw [factor_0_18]; decide
      have factor_0_20 : (41 : ZMod 258787729201) ^ 1974393 = 89949404383 := by
        calc
          (41 : ZMod 258787729201) ^ 1974393 = (41 : ZMod 258787729201) ^ (987196 + 987196 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 987196 * (41 : ZMod 258787729201) ^ 987196) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 89949404383 := by rw [factor_0_19]; decide
      have factor_0_21 : (41 : ZMod 258787729201) ^ 3948787 = 176276307374 := by
        calc
          (41 : ZMod 258787729201) ^ 3948787 = (41 : ZMod 258787729201) ^ (1974393 + 1974393 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1974393 * (41 : ZMod 258787729201) ^ 1974393) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 176276307374 := by rw [factor_0_20]; decide
      have factor_0_22 : (41 : ZMod 258787729201) ^ 7897574 = 170555070943 := by
        calc
          (41 : ZMod 258787729201) ^ 7897574 = (41 : ZMod 258787729201) ^ (3948787 + 3948787) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3948787 * (41 : ZMod 258787729201) ^ 3948787 := by rw [pow_add]
          _ = 170555070943 := by rw [factor_0_21]; decide
      have factor_0_23 : (41 : ZMod 258787729201) ^ 15795149 = 233226291559 := by
        calc
          (41 : ZMod 258787729201) ^ 15795149 = (41 : ZMod 258787729201) ^ (7897574 + 7897574 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 7897574 * (41 : ZMod 258787729201) ^ 7897574) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 233226291559 := by rw [factor_0_22]; decide
      have factor_0_24 : (41 : ZMod 258787729201) ^ 31590298 = 228165492000 := by
        calc
          (41 : ZMod 258787729201) ^ 31590298 = (41 : ZMod 258787729201) ^ (15795149 + 15795149) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 15795149 * (41 : ZMod 258787729201) ^ 15795149 := by rw [pow_add]
          _ = 228165492000 := by rw [factor_0_23]; decide
      have factor_0_25 : (41 : ZMod 258787729201) ^ 63180597 = 194074477725 := by
        calc
          (41 : ZMod 258787729201) ^ 63180597 = (41 : ZMod 258787729201) ^ (31590298 + 31590298 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 31590298 * (41 : ZMod 258787729201) ^ 31590298) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 194074477725 := by rw [factor_0_24]; decide
      have factor_0_26 : (41 : ZMod 258787729201) ^ 126361195 = 17944988643 := by
        calc
          (41 : ZMod 258787729201) ^ 126361195 = (41 : ZMod 258787729201) ^ (63180597 + 63180597 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 63180597 * (41 : ZMod 258787729201) ^ 63180597) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 17944988643 := by rw [factor_0_25]; decide
      have factor_0_27 : (41 : ZMod 258787729201) ^ 252722391 = 98287788926 := by
        calc
          (41 : ZMod 258787729201) ^ 252722391 = (41 : ZMod 258787729201) ^ (126361195 + 126361195 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 126361195 * (41 : ZMod 258787729201) ^ 126361195) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 98287788926 := by rw [factor_0_26]; decide
      have factor_0_28 : (41 : ZMod 258787729201) ^ 505444783 = 161290476159 := by
        calc
          (41 : ZMod 258787729201) ^ 505444783 = (41 : ZMod 258787729201) ^ (252722391 + 252722391 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 252722391 * (41 : ZMod 258787729201) ^ 252722391) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 161290476159 := by rw [factor_0_27]; decide
      have factor_0_29 : (41 : ZMod 258787729201) ^ 1010889567 = 191619872792 := by
        calc
          (41 : ZMod 258787729201) ^ 1010889567 = (41 : ZMod 258787729201) ^ (505444783 + 505444783 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 505444783 * (41 : ZMod 258787729201) ^ 505444783) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 191619872792 := by rw [factor_0_28]; decide
      have factor_0_30 : (41 : ZMod 258787729201) ^ 2021779134 = 832351988 := by
        calc
          (41 : ZMod 258787729201) ^ 2021779134 = (41 : ZMod 258787729201) ^ (1010889567 + 1010889567) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1010889567 * (41 : ZMod 258787729201) ^ 1010889567 := by rw [pow_add]
          _ = 832351988 := by rw [factor_0_29]; decide
      have factor_0_31 : (41 : ZMod 258787729201) ^ 4043558268 = 144513033009 := by
        calc
          (41 : ZMod 258787729201) ^ 4043558268 = (41 : ZMod 258787729201) ^ (2021779134 + 2021779134) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2021779134 * (41 : ZMod 258787729201) ^ 2021779134 := by rw [pow_add]
          _ = 144513033009 := by rw [factor_0_30]; decide
      have factor_0_32 : (41 : ZMod 258787729201) ^ 8087116537 = 189832630337 := by
        calc
          (41 : ZMod 258787729201) ^ 8087116537 = (41 : ZMod 258787729201) ^ (4043558268 + 4043558268 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 4043558268 * (41 : ZMod 258787729201) ^ 4043558268) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 189832630337 := by rw [factor_0_31]; decide
      have factor_0_33 : (41 : ZMod 258787729201) ^ 16174233075 = 204746943496 := by
        calc
          (41 : ZMod 258787729201) ^ 16174233075 = (41 : ZMod 258787729201) ^ (8087116537 + 8087116537 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 8087116537 * (41 : ZMod 258787729201) ^ 8087116537) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 204746943496 := by rw [factor_0_32]; decide
      have factor_0_34 : (41 : ZMod 258787729201) ^ 32348466150 = 181415155677 := by
        calc
          (41 : ZMod 258787729201) ^ 32348466150 = (41 : ZMod 258787729201) ^ (16174233075 + 16174233075) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 16174233075 * (41 : ZMod 258787729201) ^ 16174233075 := by rw [pow_add]
          _ = 181415155677 := by rw [factor_0_33]; decide
      have factor_0_35 : (41 : ZMod 258787729201) ^ 64696932300 = 5861368492 := by
        calc
          (41 : ZMod 258787729201) ^ 64696932300 = (41 : ZMod 258787729201) ^ (32348466150 + 32348466150) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 32348466150 * (41 : ZMod 258787729201) ^ 32348466150 := by rw [pow_add]
          _ = 5861368492 := by rw [factor_0_34]; decide
      have factor_0_36 : (41 : ZMod 258787729201) ^ 129393864600 = 258787729200 := by
        calc
          (41 : ZMod 258787729201) ^ 129393864600 = (41 : ZMod 258787729201) ^ (64696932300 + 64696932300) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 64696932300 * (41 : ZMod 258787729201) ^ 64696932300 := by rw [pow_add]
          _ = 258787729200 := by rw [factor_0_35]; decide
      change (41 : ZMod 258787729201) ^ 129393864600 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_1_1 : (41 : ZMod 258787729201) ^ 2 = 1681 := by
        calc
          (41 : ZMod 258787729201) ^ 2 = (41 : ZMod 258787729201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1 := by rw [pow_add]
          _ = 1681 := by rw [factor_1_0]; decide
      have factor_1_2 : (41 : ZMod 258787729201) ^ 5 = 115856201 := by
        calc
          (41 : ZMod 258787729201) ^ 5 = (41 : ZMod 258787729201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2 * (41 : ZMod 258787729201) ^ 2) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 115856201 := by rw [factor_1_1]; decide
      have factor_1_3 : (41 : ZMod 258787729201) ^ 10 = 116159684134 := by
        calc
          (41 : ZMod 258787729201) ^ 10 = (41 : ZMod 258787729201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5 * (41 : ZMod 258787729201) ^ 5 := by rw [pow_add]
          _ = 116159684134 := by rw [factor_1_2]; decide
      have factor_1_4 : (41 : ZMod 258787729201) ^ 20 = 101763977189 := by
        calc
          (41 : ZMod 258787729201) ^ 20 = (41 : ZMod 258787729201) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 10 * (41 : ZMod 258787729201) ^ 10 := by rw [pow_add]
          _ = 101763977189 := by rw [factor_1_3]; decide
      have factor_1_5 : (41 : ZMod 258787729201) ^ 40 = 31479291541 := by
        calc
          (41 : ZMod 258787729201) ^ 40 = (41 : ZMod 258787729201) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 20 * (41 : ZMod 258787729201) ^ 20 := by rw [pow_add]
          _ = 31479291541 := by rw [factor_1_4]; decide
      have factor_1_6 : (41 : ZMod 258787729201) ^ 80 = 100754258821 := by
        calc
          (41 : ZMod 258787729201) ^ 80 = (41 : ZMod 258787729201) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 40 * (41 : ZMod 258787729201) ^ 40 := by rw [pow_add]
          _ = 100754258821 := by rw [factor_1_5]; decide
      have factor_1_7 : (41 : ZMod 258787729201) ^ 160 = 72050774181 := by
        calc
          (41 : ZMod 258787729201) ^ 160 = (41 : ZMod 258787729201) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 80 * (41 : ZMod 258787729201) ^ 80 := by rw [pow_add]
          _ = 72050774181 := by rw [factor_1_6]; decide
      have factor_1_8 : (41 : ZMod 258787729201) ^ 321 = 141984250173 := by
        calc
          (41 : ZMod 258787729201) ^ 321 = (41 : ZMod 258787729201) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 160 * (41 : ZMod 258787729201) ^ 160) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 141984250173 := by rw [factor_1_7]; decide
      have factor_1_9 : (41 : ZMod 258787729201) ^ 642 = 68662517360 := by
        calc
          (41 : ZMod 258787729201) ^ 642 = (41 : ZMod 258787729201) ^ (321 + 321) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 321 * (41 : ZMod 258787729201) ^ 321 := by rw [pow_add]
          _ = 68662517360 := by rw [factor_1_8]; decide
      have factor_1_10 : (41 : ZMod 258787729201) ^ 1285 = 133631660024 := by
        calc
          (41 : ZMod 258787729201) ^ 1285 = (41 : ZMod 258787729201) ^ (642 + 642 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 642 * (41 : ZMod 258787729201) ^ 642) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 133631660024 := by rw [factor_1_9]; decide
      have factor_1_11 : (41 : ZMod 258787729201) ^ 2570 = 129940172556 := by
        calc
          (41 : ZMod 258787729201) ^ 2570 = (41 : ZMod 258787729201) ^ (1285 + 1285) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1285 * (41 : ZMod 258787729201) ^ 1285 := by rw [pow_add]
          _ = 129940172556 := by rw [factor_1_10]; decide
      have factor_1_12 : (41 : ZMod 258787729201) ^ 5141 = 153058960780 := by
        calc
          (41 : ZMod 258787729201) ^ 5141 = (41 : ZMod 258787729201) ^ (2570 + 2570 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2570 * (41 : ZMod 258787729201) ^ 2570) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 153058960780 := by rw [factor_1_11]; decide
      have factor_1_13 : (41 : ZMod 258787729201) ^ 10283 = 12732097325 := by
        calc
          (41 : ZMod 258787729201) ^ 10283 = (41 : ZMod 258787729201) ^ (5141 + 5141 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 5141 * (41 : ZMod 258787729201) ^ 5141) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 12732097325 := by rw [factor_1_12]; decide
      have factor_1_14 : (41 : ZMod 258787729201) ^ 20566 = 58487867577 := by
        calc
          (41 : ZMod 258787729201) ^ 20566 = (41 : ZMod 258787729201) ^ (10283 + 10283) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 10283 * (41 : ZMod 258787729201) ^ 10283 := by rw [pow_add]
          _ = 58487867577 := by rw [factor_1_13]; decide
      have factor_1_15 : (41 : ZMod 258787729201) ^ 41133 = 82847269939 := by
        calc
          (41 : ZMod 258787729201) ^ 41133 = (41 : ZMod 258787729201) ^ (20566 + 20566 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 20566 * (41 : ZMod 258787729201) ^ 20566) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 82847269939 := by rw [factor_1_14]; decide
      have factor_1_16 : (41 : ZMod 258787729201) ^ 82266 = 184650721244 := by
        calc
          (41 : ZMod 258787729201) ^ 82266 = (41 : ZMod 258787729201) ^ (41133 + 41133) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 41133 * (41 : ZMod 258787729201) ^ 41133 := by rw [pow_add]
          _ = 184650721244 := by rw [factor_1_15]; decide
      have factor_1_17 : (41 : ZMod 258787729201) ^ 164532 = 171901425651 := by
        calc
          (41 : ZMod 258787729201) ^ 164532 = (41 : ZMod 258787729201) ^ (82266 + 82266) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 82266 * (41 : ZMod 258787729201) ^ 82266 := by rw [pow_add]
          _ = 171901425651 := by rw [factor_1_16]; decide
      have factor_1_18 : (41 : ZMod 258787729201) ^ 329065 = 102341652444 := by
        calc
          (41 : ZMod 258787729201) ^ 329065 = (41 : ZMod 258787729201) ^ (164532 + 164532 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 164532 * (41 : ZMod 258787729201) ^ 164532) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 102341652444 := by rw [factor_1_17]; decide
      have factor_1_19 : (41 : ZMod 258787729201) ^ 658131 = 100909092072 := by
        calc
          (41 : ZMod 258787729201) ^ 658131 = (41 : ZMod 258787729201) ^ (329065 + 329065 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 329065 * (41 : ZMod 258787729201) ^ 329065) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 100909092072 := by rw [factor_1_18]; decide
      have factor_1_20 : (41 : ZMod 258787729201) ^ 1316262 = 194743062111 := by
        calc
          (41 : ZMod 258787729201) ^ 1316262 = (41 : ZMod 258787729201) ^ (658131 + 658131) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 658131 * (41 : ZMod 258787729201) ^ 658131 := by rw [pow_add]
          _ = 194743062111 := by rw [factor_1_19]; decide
      have factor_1_21 : (41 : ZMod 258787729201) ^ 2632524 = 14856778419 := by
        calc
          (41 : ZMod 258787729201) ^ 2632524 = (41 : ZMod 258787729201) ^ (1316262 + 1316262) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1316262 * (41 : ZMod 258787729201) ^ 1316262 := by rw [pow_add]
          _ = 14856778419 := by rw [factor_1_20]; decide
      have factor_1_22 : (41 : ZMod 258787729201) ^ 5265049 = 222565281060 := by
        calc
          (41 : ZMod 258787729201) ^ 5265049 = (41 : ZMod 258787729201) ^ (2632524 + 2632524 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2632524 * (41 : ZMod 258787729201) ^ 2632524) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 222565281060 := by rw [factor_1_21]; decide
      have factor_1_23 : (41 : ZMod 258787729201) ^ 10530099 = 202495501926 := by
        calc
          (41 : ZMod 258787729201) ^ 10530099 = (41 : ZMod 258787729201) ^ (5265049 + 5265049 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 5265049 * (41 : ZMod 258787729201) ^ 5265049) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 202495501926 := by rw [factor_1_22]; decide
      have factor_1_24 : (41 : ZMod 258787729201) ^ 21060199 = 90701258863 := by
        calc
          (41 : ZMod 258787729201) ^ 21060199 = (41 : ZMod 258787729201) ^ (10530099 + 10530099 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 10530099 * (41 : ZMod 258787729201) ^ 10530099) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 90701258863 := by rw [factor_1_23]; decide
      have factor_1_25 : (41 : ZMod 258787729201) ^ 42120398 = 174411139479 := by
        calc
          (41 : ZMod 258787729201) ^ 42120398 = (41 : ZMod 258787729201) ^ (21060199 + 21060199) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 21060199 * (41 : ZMod 258787729201) ^ 21060199 := by rw [pow_add]
          _ = 174411139479 := by rw [factor_1_24]; decide
      have factor_1_26 : (41 : ZMod 258787729201) ^ 84240797 = 229797888425 := by
        calc
          (41 : ZMod 258787729201) ^ 84240797 = (41 : ZMod 258787729201) ^ (42120398 + 42120398 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 42120398 * (41 : ZMod 258787729201) ^ 42120398) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 229797888425 := by rw [factor_1_25]; decide
      have factor_1_27 : (41 : ZMod 258787729201) ^ 168481594 = 145356334996 := by
        calc
          (41 : ZMod 258787729201) ^ 168481594 = (41 : ZMod 258787729201) ^ (84240797 + 84240797) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 84240797 * (41 : ZMod 258787729201) ^ 84240797 := by rw [pow_add]
          _ = 145356334996 := by rw [factor_1_26]; decide
      have factor_1_28 : (41 : ZMod 258787729201) ^ 336963189 = 235012216619 := by
        calc
          (41 : ZMod 258787729201) ^ 336963189 = (41 : ZMod 258787729201) ^ (168481594 + 168481594 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 168481594 * (41 : ZMod 258787729201) ^ 168481594) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 235012216619 := by rw [factor_1_27]; decide
      have factor_1_29 : (41 : ZMod 258787729201) ^ 673926378 = 164751765152 := by
        calc
          (41 : ZMod 258787729201) ^ 673926378 = (41 : ZMod 258787729201) ^ (336963189 + 336963189) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 336963189 * (41 : ZMod 258787729201) ^ 336963189 := by rw [pow_add]
          _ = 164751765152 := by rw [factor_1_28]; decide
      have factor_1_30 : (41 : ZMod 258787729201) ^ 1347852756 = 77852437965 := by
        calc
          (41 : ZMod 258787729201) ^ 1347852756 = (41 : ZMod 258787729201) ^ (673926378 + 673926378) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 673926378 * (41 : ZMod 258787729201) ^ 673926378 := by rw [pow_add]
          _ = 77852437965 := by rw [factor_1_29]; decide
      have factor_1_31 : (41 : ZMod 258787729201) ^ 2695705512 = 184044422389 := by
        calc
          (41 : ZMod 258787729201) ^ 2695705512 = (41 : ZMod 258787729201) ^ (1347852756 + 1347852756) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1347852756 * (41 : ZMod 258787729201) ^ 1347852756 := by rw [pow_add]
          _ = 184044422389 := by rw [factor_1_30]; decide
      have factor_1_32 : (41 : ZMod 258787729201) ^ 5391411025 = 19161352712 := by
        calc
          (41 : ZMod 258787729201) ^ 5391411025 = (41 : ZMod 258787729201) ^ (2695705512 + 2695705512 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2695705512 * (41 : ZMod 258787729201) ^ 2695705512) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 19161352712 := by rw [factor_1_31]; decide
      have factor_1_33 : (41 : ZMod 258787729201) ^ 10782822050 = 3834881075 := by
        calc
          (41 : ZMod 258787729201) ^ 10782822050 = (41 : ZMod 258787729201) ^ (5391411025 + 5391411025) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5391411025 * (41 : ZMod 258787729201) ^ 5391411025 := by rw [pow_add]
          _ = 3834881075 := by rw [factor_1_32]; decide
      have factor_1_34 : (41 : ZMod 258787729201) ^ 21565644100 = 126738841920 := by
        calc
          (41 : ZMod 258787729201) ^ 21565644100 = (41 : ZMod 258787729201) ^ (10782822050 + 10782822050) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 10782822050 * (41 : ZMod 258787729201) ^ 10782822050 := by rw [pow_add]
          _ = 126738841920 := by rw [factor_1_33]; decide
      have factor_1_35 : (41 : ZMod 258787729201) ^ 43131288200 = 17218055278 := by
        calc
          (41 : ZMod 258787729201) ^ 43131288200 = (41 : ZMod 258787729201) ^ (21565644100 + 21565644100) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 21565644100 * (41 : ZMod 258787729201) ^ 21565644100 := by rw [pow_add]
          _ = 17218055278 := by rw [factor_1_34]; decide
      have factor_1_36 : (41 : ZMod 258787729201) ^ 86262576400 = 17218055277 := by
        calc
          (41 : ZMod 258787729201) ^ 86262576400 = (41 : ZMod 258787729201) ^ (43131288200 + 43131288200) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 43131288200 * (41 : ZMod 258787729201) ^ 43131288200 := by rw [pow_add]
          _ = 17218055277 := by rw [factor_1_35]; decide
      change (41 : ZMod 258787729201) ^ 86262576400 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_2_1 : (41 : ZMod 258787729201) ^ 3 = 68921 := by
        calc
          (41 : ZMod 258787729201) ^ 3 = (41 : ZMod 258787729201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 68921 := by rw [factor_2_0]; decide
      have factor_2_2 : (41 : ZMod 258787729201) ^ 6 = 4750104241 := by
        calc
          (41 : ZMod 258787729201) ^ 6 = (41 : ZMod 258787729201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3 * (41 : ZMod 258787729201) ^ 3 := by rw [pow_add]
          _ = 4750104241 := by rw [factor_2_1]; decide
      have factor_2_3 : (41 : ZMod 258787729201) ^ 12 = 138481211700 := by
        calc
          (41 : ZMod 258787729201) ^ 12 = (41 : ZMod 258787729201) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 6 * (41 : ZMod 258787729201) ^ 6 := by rw [pow_add]
          _ = 138481211700 := by rw [factor_2_2]; decide
      have factor_2_4 : (41 : ZMod 258787729201) ^ 24 = 152648811046 := by
        calc
          (41 : ZMod 258787729201) ^ 24 = (41 : ZMod 258787729201) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 12 * (41 : ZMod 258787729201) ^ 12 := by rw [pow_add]
          _ = 152648811046 := by rw [factor_2_3]; decide
      have factor_2_5 : (41 : ZMod 258787729201) ^ 48 = 64403925023 := by
        calc
          (41 : ZMod 258787729201) ^ 48 = (41 : ZMod 258787729201) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 24 * (41 : ZMod 258787729201) ^ 24 := by rw [pow_add]
          _ = 64403925023 := by rw [factor_2_4]; decide
      have factor_2_6 : (41 : ZMod 258787729201) ^ 96 = 31003199741 := by
        calc
          (41 : ZMod 258787729201) ^ 96 = (41 : ZMod 258787729201) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 48 * (41 : ZMod 258787729201) ^ 48 := by rw [pow_add]
          _ = 31003199741 := by rw [factor_2_5]; decide
      have factor_2_7 : (41 : ZMod 258787729201) ^ 192 = 169620675864 := by
        calc
          (41 : ZMod 258787729201) ^ 192 = (41 : ZMod 258787729201) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 96 * (41 : ZMod 258787729201) ^ 96 := by rw [pow_add]
          _ = 169620675864 := by rw [factor_2_6]; decide
      have factor_2_8 : (41 : ZMod 258787729201) ^ 385 = 79284451206 := by
        calc
          (41 : ZMod 258787729201) ^ 385 = (41 : ZMod 258787729201) ^ (192 + 192 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 192 * (41 : ZMod 258787729201) ^ 192) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 79284451206 := by rw [factor_2_7]; decide
      have factor_2_9 : (41 : ZMod 258787729201) ^ 771 = 84652684396 := by
        calc
          (41 : ZMod 258787729201) ^ 771 = (41 : ZMod 258787729201) ^ (385 + 385 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 385 * (41 : ZMod 258787729201) ^ 385) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 84652684396 := by rw [factor_2_8]; decide
      have factor_2_10 : (41 : ZMod 258787729201) ^ 1542 = 202445455046 := by
        calc
          (41 : ZMod 258787729201) ^ 1542 = (41 : ZMod 258787729201) ^ (771 + 771) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 771 * (41 : ZMod 258787729201) ^ 771 := by rw [pow_add]
          _ = 202445455046 := by rw [factor_2_9]; decide
      have factor_2_11 : (41 : ZMod 258787729201) ^ 3084 = 82016528489 := by
        calc
          (41 : ZMod 258787729201) ^ 3084 = (41 : ZMod 258787729201) ^ (1542 + 1542) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1542 * (41 : ZMod 258787729201) ^ 1542 := by rw [pow_add]
          _ = 82016528489 := by rw [factor_2_10]; decide
      have factor_2_12 : (41 : ZMod 258787729201) ^ 6169 = 192800475433 := by
        calc
          (41 : ZMod 258787729201) ^ 6169 = (41 : ZMod 258787729201) ^ (3084 + 3084 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 3084 * (41 : ZMod 258787729201) ^ 3084) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 192800475433 := by rw [factor_2_11]; decide
      have factor_2_13 : (41 : ZMod 258787729201) ^ 12339 = 179040142566 := by
        calc
          (41 : ZMod 258787729201) ^ 12339 = (41 : ZMod 258787729201) ^ (6169 + 6169 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 6169 * (41 : ZMod 258787729201) ^ 6169) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 179040142566 := by rw [factor_2_12]; decide
      have factor_2_14 : (41 : ZMod 258787729201) ^ 24679 = 56922953150 := by
        calc
          (41 : ZMod 258787729201) ^ 24679 = (41 : ZMod 258787729201) ^ (12339 + 12339 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 12339 * (41 : ZMod 258787729201) ^ 12339) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 56922953150 := by rw [factor_2_13]; decide
      have factor_2_15 : (41 : ZMod 258787729201) ^ 49359 = 31791410138 := by
        calc
          (41 : ZMod 258787729201) ^ 49359 = (41 : ZMod 258787729201) ^ (24679 + 24679 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 24679 * (41 : ZMod 258787729201) ^ 24679) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 31791410138 := by rw [factor_2_14]; decide
      have factor_2_16 : (41 : ZMod 258787729201) ^ 98719 = 39774726562 := by
        calc
          (41 : ZMod 258787729201) ^ 98719 = (41 : ZMod 258787729201) ^ (49359 + 49359 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 49359 * (41 : ZMod 258787729201) ^ 49359) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 39774726562 := by rw [factor_2_15]; decide
      have factor_2_17 : (41 : ZMod 258787729201) ^ 197439 = 86648807419 := by
        calc
          (41 : ZMod 258787729201) ^ 197439 = (41 : ZMod 258787729201) ^ (98719 + 98719 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 98719 * (41 : ZMod 258787729201) ^ 98719) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 86648807419 := by rw [factor_2_16]; decide
      have factor_2_18 : (41 : ZMod 258787729201) ^ 394878 = 152606696847 := by
        calc
          (41 : ZMod 258787729201) ^ 394878 = (41 : ZMod 258787729201) ^ (197439 + 197439) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 197439 * (41 : ZMod 258787729201) ^ 197439 := by rw [pow_add]
          _ = 152606696847 := by rw [factor_2_17]; decide
      have factor_2_19 : (41 : ZMod 258787729201) ^ 789757 = 162863009980 := by
        calc
          (41 : ZMod 258787729201) ^ 789757 = (41 : ZMod 258787729201) ^ (394878 + 394878 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 394878 * (41 : ZMod 258787729201) ^ 394878) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 162863009980 := by rw [factor_2_18]; decide
      have factor_2_20 : (41 : ZMod 258787729201) ^ 1579514 = 205326063148 := by
        calc
          (41 : ZMod 258787729201) ^ 1579514 = (41 : ZMod 258787729201) ^ (789757 + 789757) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 789757 * (41 : ZMod 258787729201) ^ 789757 := by rw [pow_add]
          _ = 205326063148 := by rw [factor_2_19]; decide
      have factor_2_21 : (41 : ZMod 258787729201) ^ 3159029 = 127347117280 := by
        calc
          (41 : ZMod 258787729201) ^ 3159029 = (41 : ZMod 258787729201) ^ (1579514 + 1579514 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1579514 * (41 : ZMod 258787729201) ^ 1579514) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 127347117280 := by rw [factor_2_20]; decide
      have factor_2_22 : (41 : ZMod 258787729201) ^ 6318059 = 125894403090 := by
        calc
          (41 : ZMod 258787729201) ^ 6318059 = (41 : ZMod 258787729201) ^ (3159029 + 3159029 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 3159029 * (41 : ZMod 258787729201) ^ 3159029) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 125894403090 := by rw [factor_2_21]; decide
      have factor_2_23 : (41 : ZMod 258787729201) ^ 12636119 = 3480360658 := by
        calc
          (41 : ZMod 258787729201) ^ 12636119 = (41 : ZMod 258787729201) ^ (6318059 + 6318059 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 6318059 * (41 : ZMod 258787729201) ^ 6318059) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 3480360658 := by rw [factor_2_22]; decide
      have factor_2_24 : (41 : ZMod 258787729201) ^ 25272239 = 248624332572 := by
        calc
          (41 : ZMod 258787729201) ^ 25272239 = (41 : ZMod 258787729201) ^ (12636119 + 12636119 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 12636119 * (41 : ZMod 258787729201) ^ 12636119) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 248624332572 := by rw [factor_2_23]; decide
      have factor_2_25 : (41 : ZMod 258787729201) ^ 50544478 = 106899437139 := by
        calc
          (41 : ZMod 258787729201) ^ 50544478 = (41 : ZMod 258787729201) ^ (25272239 + 25272239) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 25272239 * (41 : ZMod 258787729201) ^ 25272239 := by rw [pow_add]
          _ = 106899437139 := by rw [factor_2_24]; decide
      have factor_2_26 : (41 : ZMod 258787729201) ^ 101088956 = 172307817665 := by
        calc
          (41 : ZMod 258787729201) ^ 101088956 = (41 : ZMod 258787729201) ^ (50544478 + 50544478) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 50544478 * (41 : ZMod 258787729201) ^ 50544478 := by rw [pow_add]
          _ = 172307817665 := by rw [factor_2_25]; decide
      have factor_2_27 : (41 : ZMod 258787729201) ^ 202177913 = 114352334938 := by
        calc
          (41 : ZMod 258787729201) ^ 202177913 = (41 : ZMod 258787729201) ^ (101088956 + 101088956 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 101088956 * (41 : ZMod 258787729201) ^ 101088956) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 114352334938 := by rw [factor_2_26]; decide
      have factor_2_28 : (41 : ZMod 258787729201) ^ 404355826 = 89395711769 := by
        calc
          (41 : ZMod 258787729201) ^ 404355826 = (41 : ZMod 258787729201) ^ (202177913 + 202177913) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 202177913 * (41 : ZMod 258787729201) ^ 202177913 := by rw [pow_add]
          _ = 89395711769 := by rw [factor_2_27]; decide
      have factor_2_29 : (41 : ZMod 258787729201) ^ 808711653 = 5809191860 := by
        calc
          (41 : ZMod 258787729201) ^ 808711653 = (41 : ZMod 258787729201) ^ (404355826 + 404355826 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 404355826 * (41 : ZMod 258787729201) ^ 404355826) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 5809191860 := by rw [factor_2_28]; decide
      have factor_2_30 : (41 : ZMod 258787729201) ^ 1617423307 = 199431028812 := by
        calc
          (41 : ZMod 258787729201) ^ 1617423307 = (41 : ZMod 258787729201) ^ (808711653 + 808711653 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 808711653 * (41 : ZMod 258787729201) ^ 808711653) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 199431028812 := by rw [factor_2_29]; decide
      have factor_2_31 : (41 : ZMod 258787729201) ^ 3234846615 = 99029143088 := by
        calc
          (41 : ZMod 258787729201) ^ 3234846615 = (41 : ZMod 258787729201) ^ (1617423307 + 1617423307 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1617423307 * (41 : ZMod 258787729201) ^ 1617423307) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 99029143088 := by rw [factor_2_30]; decide
      have factor_2_32 : (41 : ZMod 258787729201) ^ 6469693230 = 150902303997 := by
        calc
          (41 : ZMod 258787729201) ^ 6469693230 = (41 : ZMod 258787729201) ^ (3234846615 + 3234846615) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3234846615 * (41 : ZMod 258787729201) ^ 3234846615 := by rw [pow_add]
          _ = 150902303997 := by rw [factor_2_31]; decide
      have factor_2_33 : (41 : ZMod 258787729201) ^ 12939386460 = 221135614377 := by
        calc
          (41 : ZMod 258787729201) ^ 12939386460 = (41 : ZMod 258787729201) ^ (6469693230 + 6469693230) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 6469693230 * (41 : ZMod 258787729201) ^ 6469693230 := by rw [pow_add]
          _ = 221135614377 := by rw [factor_2_32]; decide
      have factor_2_34 : (41 : ZMod 258787729201) ^ 25878772920 = 92724444878 := by
        calc
          (41 : ZMod 258787729201) ^ 25878772920 = (41 : ZMod 258787729201) ^ (12939386460 + 12939386460) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 12939386460 * (41 : ZMod 258787729201) ^ 12939386460 := by rw [pow_add]
          _ = 92724444878 := by rw [factor_2_33]; decide
      have factor_2_35 : (41 : ZMod 258787729201) ^ 51757545840 = 158434473903 := by
        calc
          (41 : ZMod 258787729201) ^ 51757545840 = (41 : ZMod 258787729201) ^ (25878772920 + 25878772920) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 25878772920 * (41 : ZMod 258787729201) ^ 25878772920 := by rw [pow_add]
          _ = 158434473903 := by rw [factor_2_34]; decide
      change (41 : ZMod 258787729201) ^ 51757545840 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_3_1 : (41 : ZMod 258787729201) ^ 2 = 1681 := by
        calc
          (41 : ZMod 258787729201) ^ 2 = (41 : ZMod 258787729201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1 := by rw [pow_add]
          _ = 1681 := by rw [factor_3_0]; decide
      have factor_3_2 : (41 : ZMod 258787729201) ^ 4 = 2825761 := by
        calc
          (41 : ZMod 258787729201) ^ 4 = (41 : ZMod 258787729201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2 * (41 : ZMod 258787729201) ^ 2 := by rw [pow_add]
          _ = 2825761 := by rw [factor_3_1]; decide
      have factor_3_3 : (41 : ZMod 258787729201) ^ 8 = 221293353091 := by
        calc
          (41 : ZMod 258787729201) ^ 8 = (41 : ZMod 258787729201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4 * (41 : ZMod 258787729201) ^ 4 := by rw [pow_add]
          _ = 221293353091 := by rw [factor_3_2]; decide
      have factor_3_4 : (41 : ZMod 258787729201) ^ 17 = 40377333702 := by
        calc
          (41 : ZMod 258787729201) ^ 17 = (41 : ZMod 258787729201) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 8 * (41 : ZMod 258787729201) ^ 8) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 40377333702 := by rw [factor_3_3]; decide
      have factor_3_5 : (41 : ZMod 258787729201) ^ 34 = 218751422307 := by
        calc
          (41 : ZMod 258787729201) ^ 34 = (41 : ZMod 258787729201) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 17 * (41 : ZMod 258787729201) ^ 17 := by rw [pow_add]
          _ = 218751422307 := by rw [factor_3_4]; decide
      have factor_3_6 : (41 : ZMod 258787729201) ^ 68 = 6737537096 := by
        calc
          (41 : ZMod 258787729201) ^ 68 = (41 : ZMod 258787729201) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 34 * (41 : ZMod 258787729201) ^ 34 := by rw [pow_add]
          _ = 6737537096 := by rw [factor_3_5]; decide
      have factor_3_7 : (41 : ZMod 258787729201) ^ 137 = 164654193677 := by
        calc
          (41 : ZMod 258787729201) ^ 137 = (41 : ZMod 258787729201) ^ (68 + 68 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 68 * (41 : ZMod 258787729201) ^ 68) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 164654193677 := by rw [factor_3_6]; decide
      have factor_3_8 : (41 : ZMod 258787729201) ^ 275 = 199339374340 := by
        calc
          (41 : ZMod 258787729201) ^ 275 = (41 : ZMod 258787729201) ^ (137 + 137 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 137 * (41 : ZMod 258787729201) ^ 137) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 199339374340 := by rw [factor_3_7]; decide
      have factor_3_9 : (41 : ZMod 258787729201) ^ 550 = 174746528868 := by
        calc
          (41 : ZMod 258787729201) ^ 550 = (41 : ZMod 258787729201) ^ (275 + 275) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 275 * (41 : ZMod 258787729201) ^ 275 := by rw [pow_add]
          _ = 174746528868 := by rw [factor_3_8]; decide
      have factor_3_10 : (41 : ZMod 258787729201) ^ 1101 = 226103381849 := by
        calc
          (41 : ZMod 258787729201) ^ 1101 = (41 : ZMod 258787729201) ^ (550 + 550 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 550 * (41 : ZMod 258787729201) ^ 550) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 226103381849 := by rw [factor_3_9]; decide
      have factor_3_11 : (41 : ZMod 258787729201) ^ 2203 = 170711408345 := by
        calc
          (41 : ZMod 258787729201) ^ 2203 = (41 : ZMod 258787729201) ^ (1101 + 1101 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1101 * (41 : ZMod 258787729201) ^ 1101) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 170711408345 := by rw [factor_3_10]; decide
      have factor_3_12 : (41 : ZMod 258787729201) ^ 4407 = 36765180959 := by
        calc
          (41 : ZMod 258787729201) ^ 4407 = (41 : ZMod 258787729201) ^ (2203 + 2203 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2203 * (41 : ZMod 258787729201) ^ 2203) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 36765180959 := by rw [factor_3_11]; decide
      have factor_3_13 : (41 : ZMod 258787729201) ^ 8814 = 100177066901 := by
        calc
          (41 : ZMod 258787729201) ^ 8814 = (41 : ZMod 258787729201) ^ (4407 + 4407) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4407 * (41 : ZMod 258787729201) ^ 4407 := by rw [pow_add]
          _ = 100177066901 := by rw [factor_3_12]; decide
      have factor_3_14 : (41 : ZMod 258787729201) ^ 17628 = 95969428379 := by
        calc
          (41 : ZMod 258787729201) ^ 17628 = (41 : ZMod 258787729201) ^ (8814 + 8814) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 8814 * (41 : ZMod 258787729201) ^ 8814 := by rw [pow_add]
          _ = 95969428379 := by rw [factor_3_13]; decide
      have factor_3_15 : (41 : ZMod 258787729201) ^ 35257 = 16926617190 := by
        calc
          (41 : ZMod 258787729201) ^ 35257 = (41 : ZMod 258787729201) ^ (17628 + 17628 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 17628 * (41 : ZMod 258787729201) ^ 17628) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 16926617190 := by rw [factor_3_14]; decide
      have factor_3_16 : (41 : ZMod 258787729201) ^ 70514 = 146967245482 := by
        calc
          (41 : ZMod 258787729201) ^ 70514 = (41 : ZMod 258787729201) ^ (35257 + 35257) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 35257 * (41 : ZMod 258787729201) ^ 35257 := by rw [pow_add]
          _ = 146967245482 := by rw [factor_3_15]; decide
      have factor_3_17 : (41 : ZMod 258787729201) ^ 141028 = 248897246343 := by
        calc
          (41 : ZMod 258787729201) ^ 141028 = (41 : ZMod 258787729201) ^ (70514 + 70514) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 70514 * (41 : ZMod 258787729201) ^ 70514 := by rw [pow_add]
          _ = 248897246343 := by rw [factor_3_16]; decide
      have factor_3_18 : (41 : ZMod 258787729201) ^ 282056 = 28774216991 := by
        calc
          (41 : ZMod 258787729201) ^ 282056 = (41 : ZMod 258787729201) ^ (141028 + 141028) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 141028 * (41 : ZMod 258787729201) ^ 141028 := by rw [pow_add]
          _ = 28774216991 := by rw [factor_3_17]; decide
      have factor_3_19 : (41 : ZMod 258787729201) ^ 564112 = 234964715527 := by
        calc
          (41 : ZMod 258787729201) ^ 564112 = (41 : ZMod 258787729201) ^ (282056 + 282056) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 282056 * (41 : ZMod 258787729201) ^ 282056 := by rw [pow_add]
          _ = 234964715527 := by rw [factor_3_18]; decide
      have factor_3_20 : (41 : ZMod 258787729201) ^ 1128224 = 72476826683 := by
        calc
          (41 : ZMod 258787729201) ^ 1128224 = (41 : ZMod 258787729201) ^ (564112 + 564112) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 564112 * (41 : ZMod 258787729201) ^ 564112 := by rw [pow_add]
          _ = 72476826683 := by rw [factor_3_19]; decide
      have factor_3_21 : (41 : ZMod 258787729201) ^ 2256449 = 24537474651 := by
        calc
          (41 : ZMod 258787729201) ^ 2256449 = (41 : ZMod 258787729201) ^ (1128224 + 1128224 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1128224 * (41 : ZMod 258787729201) ^ 1128224) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 24537474651 := by rw [factor_3_20]; decide
      have factor_3_22 : (41 : ZMod 258787729201) ^ 4512899 = 248873206858 := by
        calc
          (41 : ZMod 258787729201) ^ 4512899 = (41 : ZMod 258787729201) ^ (2256449 + 2256449 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2256449 * (41 : ZMod 258787729201) ^ 2256449) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 248873206858 := by rw [factor_3_21]; decide
      have factor_3_23 : (41 : ZMod 258787729201) ^ 9025799 = 192066101774 := by
        calc
          (41 : ZMod 258787729201) ^ 9025799 = (41 : ZMod 258787729201) ^ (4512899 + 4512899 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 4512899 * (41 : ZMod 258787729201) ^ 4512899) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 192066101774 := by rw [factor_3_22]; decide
      have factor_3_24 : (41 : ZMod 258787729201) ^ 18051599 = 173485773980 := by
        calc
          (41 : ZMod 258787729201) ^ 18051599 = (41 : ZMod 258787729201) ^ (9025799 + 9025799 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 9025799 * (41 : ZMod 258787729201) ^ 9025799) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 173485773980 := by rw [factor_3_23]; decide
      have factor_3_25 : (41 : ZMod 258787729201) ^ 36103198 = 231800499398 := by
        calc
          (41 : ZMod 258787729201) ^ 36103198 = (41 : ZMod 258787729201) ^ (18051599 + 18051599) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 18051599 * (41 : ZMod 258787729201) ^ 18051599 := by rw [pow_add]
          _ = 231800499398 := by rw [factor_3_24]; decide
      have factor_3_26 : (41 : ZMod 258787729201) ^ 72206397 = 93552207279 := by
        calc
          (41 : ZMod 258787729201) ^ 72206397 = (41 : ZMod 258787729201) ^ (36103198 + 36103198 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 36103198 * (41 : ZMod 258787729201) ^ 36103198) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 93552207279 := by rw [factor_3_25]; decide
      have factor_3_27 : (41 : ZMod 258787729201) ^ 144412795 = 10486101178 := by
        calc
          (41 : ZMod 258787729201) ^ 144412795 = (41 : ZMod 258787729201) ^ (72206397 + 72206397 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 72206397 * (41 : ZMod 258787729201) ^ 72206397) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 10486101178 := by rw [factor_3_26]; decide
      have factor_3_28 : (41 : ZMod 258787729201) ^ 288825590 = 2256561557 := by
        calc
          (41 : ZMod 258787729201) ^ 288825590 = (41 : ZMod 258787729201) ^ (144412795 + 144412795) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 144412795 * (41 : ZMod 258787729201) ^ 144412795 := by rw [pow_add]
          _ = 2256561557 := by rw [factor_3_27]; decide
      have factor_3_29 : (41 : ZMod 258787729201) ^ 577651181 = 219119033233 := by
        calc
          (41 : ZMod 258787729201) ^ 577651181 = (41 : ZMod 258787729201) ^ (288825590 + 288825590 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 288825590 * (41 : ZMod 258787729201) ^ 288825590) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 219119033233 := by rw [factor_3_28]; decide
      have factor_3_30 : (41 : ZMod 258787729201) ^ 1155302362 = 213420434352 := by
        calc
          (41 : ZMod 258787729201) ^ 1155302362 = (41 : ZMod 258787729201) ^ (577651181 + 577651181) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 577651181 * (41 : ZMod 258787729201) ^ 577651181 := by rw [pow_add]
          _ = 213420434352 := by rw [factor_3_29]; decide
      have factor_3_31 : (41 : ZMod 258787729201) ^ 2310604725 = 51044665567 := by
        calc
          (41 : ZMod 258787729201) ^ 2310604725 = (41 : ZMod 258787729201) ^ (1155302362 + 1155302362 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1155302362 * (41 : ZMod 258787729201) ^ 1155302362) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 51044665567 := by rw [factor_3_30]; decide
      have factor_3_32 : (41 : ZMod 258787729201) ^ 4621209450 = 195561979066 := by
        calc
          (41 : ZMod 258787729201) ^ 4621209450 = (41 : ZMod 258787729201) ^ (2310604725 + 2310604725) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2310604725 * (41 : ZMod 258787729201) ^ 2310604725 := by rw [pow_add]
          _ = 195561979066 := by rw [factor_3_31]; decide
      have factor_3_33 : (41 : ZMod 258787729201) ^ 9242418900 = 210066703911 := by
        calc
          (41 : ZMod 258787729201) ^ 9242418900 = (41 : ZMod 258787729201) ^ (4621209450 + 4621209450) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4621209450 * (41 : ZMod 258787729201) ^ 4621209450 := by rw [pow_add]
          _ = 210066703911 := by rw [factor_3_32]; decide
      have factor_3_34 : (41 : ZMod 258787729201) ^ 18484837800 = 88098978931 := by
        calc
          (41 : ZMod 258787729201) ^ 18484837800 = (41 : ZMod 258787729201) ^ (9242418900 + 9242418900) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 9242418900 * (41 : ZMod 258787729201) ^ 9242418900 := by rw [pow_add]
          _ = 88098978931 := by rw [factor_3_33]; decide
      have factor_3_35 : (41 : ZMod 258787729201) ^ 36969675600 = 134205534444 := by
        calc
          (41 : ZMod 258787729201) ^ 36969675600 = (41 : ZMod 258787729201) ^ (18484837800 + 18484837800) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 18484837800 * (41 : ZMod 258787729201) ^ 18484837800 := by rw [pow_add]
          _ = 134205534444 := by rw [factor_3_34]; decide
      change (41 : ZMod 258787729201) ^ 36969675600 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_4_1 : (41 : ZMod 258787729201) ^ 2 = 1681 := by
        calc
          (41 : ZMod 258787729201) ^ 2 = (41 : ZMod 258787729201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1 := by rw [pow_add]
          _ = 1681 := by rw [factor_4_0]; decide
      have factor_4_2 : (41 : ZMod 258787729201) ^ 5 = 115856201 := by
        calc
          (41 : ZMod 258787729201) ^ 5 = (41 : ZMod 258787729201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2 * (41 : ZMod 258787729201) ^ 2) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 115856201 := by rw [factor_4_1]; decide
      have factor_4_3 : (41 : ZMod 258787729201) ^ 10 = 116159684134 := by
        calc
          (41 : ZMod 258787729201) ^ 10 = (41 : ZMod 258787729201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5 * (41 : ZMod 258787729201) ^ 5 := by rw [pow_add]
          _ = 116159684134 := by rw [factor_4_2]; decide
      have factor_4_4 : (41 : ZMod 258787729201) ^ 21 = 31719397533 := by
        calc
          (41 : ZMod 258787729201) ^ 21 = (41 : ZMod 258787729201) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 10 * (41 : ZMod 258787729201) ^ 10) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 31719397533 := by rw [factor_4_3]; decide
      have factor_4_5 : (41 : ZMod 258787729201) ^ 43 = 166718405278 := by
        calc
          (41 : ZMod 258787729201) ^ 43 = (41 : ZMod 258787729201) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 21 * (41 : ZMod 258787729201) ^ 21) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 166718405278 := by rw [factor_4_4]; decide
      have factor_4_6 : (41 : ZMod 258787729201) ^ 87 = 147180840385 := by
        calc
          (41 : ZMod 258787729201) ^ 87 = (41 : ZMod 258787729201) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 43 * (41 : ZMod 258787729201) ^ 43) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 147180840385 := by rw [factor_4_5]; decide
      have factor_4_7 : (41 : ZMod 258787729201) ^ 175 = 105913939323 := by
        calc
          (41 : ZMod 258787729201) ^ 175 = (41 : ZMod 258787729201) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 87 * (41 : ZMod 258787729201) ^ 87) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 105913939323 := by rw [factor_4_6]; decide
      have factor_4_8 : (41 : ZMod 258787729201) ^ 350 = 137132250088 := by
        calc
          (41 : ZMod 258787729201) ^ 350 = (41 : ZMod 258787729201) ^ (175 + 175) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 175 * (41 : ZMod 258787729201) ^ 175 := by rw [pow_add]
          _ = 137132250088 := by rw [factor_4_7]; decide
      have factor_4_9 : (41 : ZMod 258787729201) ^ 701 = 66824022134 := by
        calc
          (41 : ZMod 258787729201) ^ 701 = (41 : ZMod 258787729201) ^ (350 + 350 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 350 * (41 : ZMod 258787729201) ^ 350) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 66824022134 := by rw [factor_4_8]; decide
      have factor_4_10 : (41 : ZMod 258787729201) ^ 1402 = 21786353280 := by
        calc
          (41 : ZMod 258787729201) ^ 1402 = (41 : ZMod 258787729201) ^ (701 + 701) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 701 * (41 : ZMod 258787729201) ^ 701 := by rw [pow_add]
          _ = 21786353280 := by rw [factor_4_9]; decide
      have factor_4_11 : (41 : ZMod 258787729201) ^ 2804 = 63409082295 := by
        calc
          (41 : ZMod 258787729201) ^ 2804 = (41 : ZMod 258787729201) ^ (1402 + 1402) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1402 * (41 : ZMod 258787729201) ^ 1402 := by rw [pow_add]
          _ = 63409082295 := by rw [factor_4_10]; decide
      have factor_4_12 : (41 : ZMod 258787729201) ^ 5609 = 243597027703 := by
        calc
          (41 : ZMod 258787729201) ^ 5609 = (41 : ZMod 258787729201) ^ (2804 + 2804 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2804 * (41 : ZMod 258787729201) ^ 2804) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 243597027703 := by rw [factor_4_11]; decide
      have factor_4_13 : (41 : ZMod 258787729201) ^ 11218 = 79814159939 := by
        calc
          (41 : ZMod 258787729201) ^ 11218 = (41 : ZMod 258787729201) ^ (5609 + 5609) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5609 * (41 : ZMod 258787729201) ^ 5609 := by rw [pow_add]
          _ = 79814159939 := by rw [factor_4_12]; decide
      have factor_4_14 : (41 : ZMod 258787729201) ^ 22436 = 134181099254 := by
        calc
          (41 : ZMod 258787729201) ^ 22436 = (41 : ZMod 258787729201) ^ (11218 + 11218) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 11218 * (41 : ZMod 258787729201) ^ 11218 := by rw [pow_add]
          _ = 134181099254 := by rw [factor_4_13]; decide
      have factor_4_15 : (41 : ZMod 258787729201) ^ 44872 = 13662980780 := by
        calc
          (41 : ZMod 258787729201) ^ 44872 = (41 : ZMod 258787729201) ^ (22436 + 22436) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 22436 * (41 : ZMod 258787729201) ^ 22436 := by rw [pow_add]
          _ = 13662980780 := by rw [factor_4_14]; decide
      have factor_4_16 : (41 : ZMod 258787729201) ^ 89745 = 31679778755 := by
        calc
          (41 : ZMod 258787729201) ^ 89745 = (41 : ZMod 258787729201) ^ (44872 + 44872 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 44872 * (41 : ZMod 258787729201) ^ 44872) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 31679778755 := by rw [factor_4_15]; decide
      have factor_4_17 : (41 : ZMod 258787729201) ^ 179490 = 73483760569 := by
        calc
          (41 : ZMod 258787729201) ^ 179490 = (41 : ZMod 258787729201) ^ (89745 + 89745) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 89745 * (41 : ZMod 258787729201) ^ 89745 := by rw [pow_add]
          _ = 73483760569 := by rw [factor_4_16]; decide
      have factor_4_18 : (41 : ZMod 258787729201) ^ 358980 = 255500344693 := by
        calc
          (41 : ZMod 258787729201) ^ 358980 = (41 : ZMod 258787729201) ^ (179490 + 179490) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 179490 * (41 : ZMod 258787729201) ^ 179490 := by rw [pow_add]
          _ = 255500344693 := by rw [factor_4_17]; decide
      have factor_4_19 : (41 : ZMod 258787729201) ^ 717961 = 142447085888 := by
        calc
          (41 : ZMod 258787729201) ^ 717961 = (41 : ZMod 258787729201) ^ (358980 + 358980 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 358980 * (41 : ZMod 258787729201) ^ 358980) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 142447085888 := by rw [factor_4_18]; decide
      have factor_4_20 : (41 : ZMod 258787729201) ^ 1435922 = 218723184878 := by
        calc
          (41 : ZMod 258787729201) ^ 1435922 = (41 : ZMod 258787729201) ^ (717961 + 717961) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 717961 * (41 : ZMod 258787729201) ^ 717961 := by rw [pow_add]
          _ = 218723184878 := by rw [factor_4_19]; decide
      have factor_4_21 : (41 : ZMod 258787729201) ^ 2871845 = 209622643432 := by
        calc
          (41 : ZMod 258787729201) ^ 2871845 = (41 : ZMod 258787729201) ^ (1435922 + 1435922 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1435922 * (41 : ZMod 258787729201) ^ 1435922) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 209622643432 := by rw [factor_4_20]; decide
      have factor_4_22 : (41 : ZMod 258787729201) ^ 5743690 = 56595574912 := by
        calc
          (41 : ZMod 258787729201) ^ 5743690 = (41 : ZMod 258787729201) ^ (2871845 + 2871845) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2871845 * (41 : ZMod 258787729201) ^ 2871845 := by rw [pow_add]
          _ = 56595574912 := by rw [factor_4_21]; decide
      have factor_4_23 : (41 : ZMod 258787729201) ^ 11487381 = 55331679112 := by
        calc
          (41 : ZMod 258787729201) ^ 11487381 = (41 : ZMod 258787729201) ^ (5743690 + 5743690 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 5743690 * (41 : ZMod 258787729201) ^ 5743690) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 55331679112 := by rw [factor_4_22]; decide
      have factor_4_24 : (41 : ZMod 258787729201) ^ 22974762 = 149502394293 := by
        calc
          (41 : ZMod 258787729201) ^ 22974762 = (41 : ZMod 258787729201) ^ (11487381 + 11487381) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 11487381 * (41 : ZMod 258787729201) ^ 11487381 := by rw [pow_add]
          _ = 149502394293 := by rw [factor_4_23]; decide
      have factor_4_25 : (41 : ZMod 258787729201) ^ 45949525 = 167557095696 := by
        calc
          (41 : ZMod 258787729201) ^ 45949525 = (41 : ZMod 258787729201) ^ (22974762 + 22974762 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 22974762 * (41 : ZMod 258787729201) ^ 22974762) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 167557095696 := by rw [factor_4_24]; decide
      have factor_4_26 : (41 : ZMod 258787729201) ^ 91899051 = 11948546365 := by
        calc
          (41 : ZMod 258787729201) ^ 91899051 = (41 : ZMod 258787729201) ^ (45949525 + 45949525 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 45949525 * (41 : ZMod 258787729201) ^ 45949525) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 11948546365 := by rw [factor_4_25]; decide
      have factor_4_27 : (41 : ZMod 258787729201) ^ 183798103 = 104621932500 := by
        calc
          (41 : ZMod 258787729201) ^ 183798103 = (41 : ZMod 258787729201) ^ (91899051 + 91899051 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 91899051 * (41 : ZMod 258787729201) ^ 91899051) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 104621932500 := by rw [factor_4_26]; decide
      have factor_4_28 : (41 : ZMod 258787729201) ^ 367596206 = 106668354690 := by
        calc
          (41 : ZMod 258787729201) ^ 367596206 = (41 : ZMod 258787729201) ^ (183798103 + 183798103) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 183798103 * (41 : ZMod 258787729201) ^ 183798103 := by rw [pow_add]
          _ = 106668354690 := by rw [factor_4_27]; decide
      have factor_4_29 : (41 : ZMod 258787729201) ^ 735192412 = 224598530109 := by
        calc
          (41 : ZMod 258787729201) ^ 735192412 = (41 : ZMod 258787729201) ^ (367596206 + 367596206) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 367596206 * (41 : ZMod 258787729201) ^ 367596206 := by rw [pow_add]
          _ = 224598530109 := by rw [factor_4_28]; decide
      have factor_4_30 : (41 : ZMod 258787729201) ^ 1470384825 = 62189974331 := by
        calc
          (41 : ZMod 258787729201) ^ 1470384825 = (41 : ZMod 258787729201) ^ (735192412 + 735192412 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 735192412 * (41 : ZMod 258787729201) ^ 735192412) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 62189974331 := by rw [factor_4_29]; decide
      have factor_4_31 : (41 : ZMod 258787729201) ^ 2940769650 = 64414010982 := by
        calc
          (41 : ZMod 258787729201) ^ 2940769650 = (41 : ZMod 258787729201) ^ (1470384825 + 1470384825) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1470384825 * (41 : ZMod 258787729201) ^ 1470384825 := by rw [pow_add]
          _ = 64414010982 := by rw [factor_4_30]; decide
      have factor_4_32 : (41 : ZMod 258787729201) ^ 5881539300 = 117565569403 := by
        calc
          (41 : ZMod 258787729201) ^ 5881539300 = (41 : ZMod 258787729201) ^ (2940769650 + 2940769650) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2940769650 * (41 : ZMod 258787729201) ^ 2940769650 := by rw [pow_add]
          _ = 117565569403 := by rw [factor_4_31]; decide
      have factor_4_33 : (41 : ZMod 258787729201) ^ 11763078600 = 92416376699 := by
        calc
          (41 : ZMod 258787729201) ^ 11763078600 = (41 : ZMod 258787729201) ^ (5881539300 + 5881539300) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5881539300 * (41 : ZMod 258787729201) ^ 5881539300 := by rw [pow_add]
          _ = 92416376699 := by rw [factor_4_32]; decide
      have factor_4_34 : (41 : ZMod 258787729201) ^ 23526157200 = 73018466852 := by
        calc
          (41 : ZMod 258787729201) ^ 23526157200 = (41 : ZMod 258787729201) ^ (11763078600 + 11763078600) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 11763078600 * (41 : ZMod 258787729201) ^ 11763078600 := by rw [pow_add]
          _ = 73018466852 := by rw [factor_4_33]; decide
      change (41 : ZMod 258787729201) ^ 23526157200 ≠ 1
      rw [factor_4_34]
      decide
    ·
      have factor_5_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_5_1 : (41 : ZMod 258787729201) ^ 2 = 1681 := by
        calc
          (41 : ZMod 258787729201) ^ 2 = (41 : ZMod 258787729201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1 := by rw [pow_add]
          _ = 1681 := by rw [factor_5_0]; decide
      have factor_5_2 : (41 : ZMod 258787729201) ^ 4 = 2825761 := by
        calc
          (41 : ZMod 258787729201) ^ 4 = (41 : ZMod 258787729201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2 * (41 : ZMod 258787729201) ^ 2 := by rw [pow_add]
          _ = 2825761 := by rw [factor_5_1]; decide
      have factor_5_3 : (41 : ZMod 258787729201) ^ 9 = 15456954696 := by
        calc
          (41 : ZMod 258787729201) ^ 9 = (41 : ZMod 258787729201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 4 * (41 : ZMod 258787729201) ^ 4) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 15456954696 := by rw [factor_5_2]; decide
      have factor_5_4 : (41 : ZMod 258787729201) ^ 18 = 102744306576 := by
        calc
          (41 : ZMod 258787729201) ^ 18 = (41 : ZMod 258787729201) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 9 * (41 : ZMod 258787729201) ^ 9 := by rw [pow_add]
          _ = 102744306576 := by rw [factor_5_3]; decide
      have factor_5_5 : (41 : ZMod 258787729201) ^ 37 = 111249028889 := by
        calc
          (41 : ZMod 258787729201) ^ 37 = (41 : ZMod 258787729201) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 18 * (41 : ZMod 258787729201) ^ 18) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 111249028889 := by rw [factor_5_4]; decide
      have factor_5_6 : (41 : ZMod 258787729201) ^ 74 = 154672894799 := by
        calc
          (41 : ZMod 258787729201) ^ 74 = (41 : ZMod 258787729201) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 37 * (41 : ZMod 258787729201) ^ 37 := by rw [pow_add]
          _ = 154672894799 := by rw [factor_5_5]; decide
      have factor_5_7 : (41 : ZMod 258787729201) ^ 148 = 52072743246 := by
        calc
          (41 : ZMod 258787729201) ^ 148 = (41 : ZMod 258787729201) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 74 * (41 : ZMod 258787729201) ^ 74 := by rw [pow_add]
          _ = 52072743246 := by rw [factor_5_6]; decide
      have factor_5_8 : (41 : ZMod 258787729201) ^ 296 = 112183180883 := by
        calc
          (41 : ZMod 258787729201) ^ 296 = (41 : ZMod 258787729201) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 148 * (41 : ZMod 258787729201) ^ 148 := by rw [pow_add]
          _ = 112183180883 := by rw [factor_5_7]; decide
      have factor_5_9 : (41 : ZMod 258787729201) ^ 593 = 23001256631 := by
        calc
          (41 : ZMod 258787729201) ^ 593 = (41 : ZMod 258787729201) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 296 * (41 : ZMod 258787729201) ^ 296) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 23001256631 := by rw [factor_5_8]; decide
      have factor_5_10 : (41 : ZMod 258787729201) ^ 1186 = 61466754406 := by
        calc
          (41 : ZMod 258787729201) ^ 1186 = (41 : ZMod 258787729201) ^ (593 + 593) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 593 * (41 : ZMod 258787729201) ^ 593 := by rw [pow_add]
          _ = 61466754406 := by rw [factor_5_9]; decide
      have factor_5_11 : (41 : ZMod 258787729201) ^ 2373 = 42208360126 := by
        calc
          (41 : ZMod 258787729201) ^ 2373 = (41 : ZMod 258787729201) ^ (1186 + 1186 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1186 * (41 : ZMod 258787729201) ^ 1186) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 42208360126 := by rw [factor_5_10]; decide
      have factor_5_12 : (41 : ZMod 258787729201) ^ 4746 = 35259561448 := by
        calc
          (41 : ZMod 258787729201) ^ 4746 = (41 : ZMod 258787729201) ^ (2373 + 2373) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2373 * (41 : ZMod 258787729201) ^ 2373 := by rw [pow_add]
          _ = 35259561448 := by rw [factor_5_11]; decide
      have factor_5_13 : (41 : ZMod 258787729201) ^ 9492 = 190033959789 := by
        calc
          (41 : ZMod 258787729201) ^ 9492 = (41 : ZMod 258787729201) ^ (4746 + 4746) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4746 * (41 : ZMod 258787729201) ^ 4746 := by rw [pow_add]
          _ = 190033959789 := by rw [factor_5_12]; decide
      have factor_5_14 : (41 : ZMod 258787729201) ^ 18984 = 23412857070 := by
        calc
          (41 : ZMod 258787729201) ^ 18984 = (41 : ZMod 258787729201) ^ (9492 + 9492) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 9492 * (41 : ZMod 258787729201) ^ 9492 := by rw [pow_add]
          _ = 23412857070 := by rw [factor_5_13]; decide
      have factor_5_15 : (41 : ZMod 258787729201) ^ 37969 = 184856417995 := by
        calc
          (41 : ZMod 258787729201) ^ 37969 = (41 : ZMod 258787729201) ^ (18984 + 18984 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 18984 * (41 : ZMod 258787729201) ^ 18984) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 184856417995 := by rw [factor_5_14]; decide
      have factor_5_16 : (41 : ZMod 258787729201) ^ 75938 = 182238014355 := by
        calc
          (41 : ZMod 258787729201) ^ 75938 = (41 : ZMod 258787729201) ^ (37969 + 37969) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 37969 * (41 : ZMod 258787729201) ^ 37969 := by rw [pow_add]
          _ = 182238014355 := by rw [factor_5_15]; decide
      have factor_5_17 : (41 : ZMod 258787729201) ^ 151876 = 53158887579 := by
        calc
          (41 : ZMod 258787729201) ^ 151876 = (41 : ZMod 258787729201) ^ (75938 + 75938) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 75938 * (41 : ZMod 258787729201) ^ 75938 := by rw [pow_add]
          _ = 53158887579 := by rw [factor_5_16]; decide
      have factor_5_18 : (41 : ZMod 258787729201) ^ 303752 = 147115916679 := by
        calc
          (41 : ZMod 258787729201) ^ 303752 = (41 : ZMod 258787729201) ^ (151876 + 151876) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 151876 * (41 : ZMod 258787729201) ^ 151876 := by rw [pow_add]
          _ = 147115916679 := by rw [factor_5_17]; decide
      have factor_5_19 : (41 : ZMod 258787729201) ^ 607505 = 255692428029 := by
        calc
          (41 : ZMod 258787729201) ^ 607505 = (41 : ZMod 258787729201) ^ (303752 + 303752 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 303752 * (41 : ZMod 258787729201) ^ 303752) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 255692428029 := by rw [factor_5_18]; decide
      have factor_5_20 : (41 : ZMod 258787729201) ^ 1215011 = 20781838617 := by
        calc
          (41 : ZMod 258787729201) ^ 1215011 = (41 : ZMod 258787729201) ^ (607505 + 607505 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 607505 * (41 : ZMod 258787729201) ^ 607505) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 20781838617 := by rw [factor_5_19]; decide
      have factor_5_21 : (41 : ZMod 258787729201) ^ 2430022 = 135394830371 := by
        calc
          (41 : ZMod 258787729201) ^ 2430022 = (41 : ZMod 258787729201) ^ (1215011 + 1215011) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1215011 * (41 : ZMod 258787729201) ^ 1215011 := by rw [pow_add]
          _ = 135394830371 := by rw [factor_5_20]; decide
      have factor_5_22 : (41 : ZMod 258787729201) ^ 4860045 = 199292056760 := by
        calc
          (41 : ZMod 258787729201) ^ 4860045 = (41 : ZMod 258787729201) ^ (2430022 + 2430022 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2430022 * (41 : ZMod 258787729201) ^ 2430022) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 199292056760 := by rw [factor_5_21]; decide
      have factor_5_23 : (41 : ZMod 258787729201) ^ 9720091 = 155330056286 := by
        calc
          (41 : ZMod 258787729201) ^ 9720091 = (41 : ZMod 258787729201) ^ (4860045 + 4860045 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 4860045 * (41 : ZMod 258787729201) ^ 4860045) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 155330056286 := by rw [factor_5_22]; decide
      have factor_5_24 : (41 : ZMod 258787729201) ^ 19440183 = 242332324639 := by
        calc
          (41 : ZMod 258787729201) ^ 19440183 = (41 : ZMod 258787729201) ^ (9720091 + 9720091 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 9720091 * (41 : ZMod 258787729201) ^ 9720091) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 242332324639 := by rw [factor_5_23]; decide
      have factor_5_25 : (41 : ZMod 258787729201) ^ 38880367 = 138178529535 := by
        calc
          (41 : ZMod 258787729201) ^ 38880367 = (41 : ZMod 258787729201) ^ (19440183 + 19440183 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 19440183 * (41 : ZMod 258787729201) ^ 19440183) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 138178529535 := by rw [factor_5_24]; decide
      have factor_5_26 : (41 : ZMod 258787729201) ^ 77760735 = 111451985199 := by
        calc
          (41 : ZMod 258787729201) ^ 77760735 = (41 : ZMod 258787729201) ^ (38880367 + 38880367 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 38880367 * (41 : ZMod 258787729201) ^ 38880367) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 111451985199 := by rw [factor_5_25]; decide
      have factor_5_27 : (41 : ZMod 258787729201) ^ 155521471 = 198078046590 := by
        calc
          (41 : ZMod 258787729201) ^ 155521471 = (41 : ZMod 258787729201) ^ (77760735 + 77760735 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 77760735 * (41 : ZMod 258787729201) ^ 77760735) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 198078046590 := by rw [factor_5_26]; decide
      have factor_5_28 : (41 : ZMod 258787729201) ^ 311042943 = 154644332035 := by
        calc
          (41 : ZMod 258787729201) ^ 311042943 = (41 : ZMod 258787729201) ^ (155521471 + 155521471 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 155521471 * (41 : ZMod 258787729201) ^ 155521471) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 154644332035 := by rw [factor_5_27]; decide
      have factor_5_29 : (41 : ZMod 258787729201) ^ 622085887 = 220123520454 := by
        calc
          (41 : ZMod 258787729201) ^ 622085887 = (41 : ZMod 258787729201) ^ (311042943 + 311042943 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 311042943 * (41 : ZMod 258787729201) ^ 311042943) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 220123520454 := by rw [factor_5_28]; decide
      have factor_5_30 : (41 : ZMod 258787729201) ^ 1244171775 = 86599810828 := by
        calc
          (41 : ZMod 258787729201) ^ 1244171775 = (41 : ZMod 258787729201) ^ (622085887 + 622085887 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 622085887 * (41 : ZMod 258787729201) ^ 622085887) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 86599810828 := by rw [factor_5_29]; decide
      have factor_5_31 : (41 : ZMod 258787729201) ^ 2488343550 = 2449647838 := by
        calc
          (41 : ZMod 258787729201) ^ 2488343550 = (41 : ZMod 258787729201) ^ (1244171775 + 1244171775) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1244171775 * (41 : ZMod 258787729201) ^ 1244171775 := by rw [pow_add]
          _ = 2449647838 := by rw [factor_5_30]; decide
      have factor_5_32 : (41 : ZMod 258787729201) ^ 4976687100 = 7326160626 := by
        calc
          (41 : ZMod 258787729201) ^ 4976687100 = (41 : ZMod 258787729201) ^ (2488343550 + 2488343550) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2488343550 * (41 : ZMod 258787729201) ^ 2488343550 := by rw [pow_add]
          _ = 7326160626 := by rw [factor_5_31]; decide
      have factor_5_33 : (41 : ZMod 258787729201) ^ 9953374200 = 136242179666 := by
        calc
          (41 : ZMod 258787729201) ^ 9953374200 = (41 : ZMod 258787729201) ^ (4976687100 + 4976687100) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4976687100 * (41 : ZMod 258787729201) ^ 4976687100 := by rw [pow_add]
          _ = 136242179666 := by rw [factor_5_32]; decide
      have factor_5_34 : (41 : ZMod 258787729201) ^ 19906748400 = 137863364022 := by
        calc
          (41 : ZMod 258787729201) ^ 19906748400 = (41 : ZMod 258787729201) ^ (9953374200 + 9953374200) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 9953374200 * (41 : ZMod 258787729201) ^ 9953374200 := by rw [pow_add]
          _ = 137863364022 := by rw [factor_5_33]; decide
      change (41 : ZMod 258787729201) ^ 19906748400 ≠ 1
      rw [factor_5_34]
      decide
    ·
      have factor_6_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_6_1 : (41 : ZMod 258787729201) ^ 3 = 68921 := by
        calc
          (41 : ZMod 258787729201) ^ 3 = (41 : ZMod 258787729201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 68921 := by rw [factor_6_0]; decide
      have factor_6_2 : (41 : ZMod 258787729201) ^ 7 = 194754273881 := by
        calc
          (41 : ZMod 258787729201) ^ 7 = (41 : ZMod 258787729201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 3 * (41 : ZMod 258787729201) ^ 3) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 194754273881 := by rw [factor_6_1]; decide
      have factor_6_3 : (41 : ZMod 258787729201) ^ 14 = 136748316001 := by
        calc
          (41 : ZMod 258787729201) ^ 14 = (41 : ZMod 258787729201) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 7 * (41 : ZMod 258787729201) ^ 7 := by rw [pow_add]
          _ = 136748316001 := by rw [factor_6_2]; decide
      have factor_6_4 : (41 : ZMod 258787729201) ^ 28 = 117191554000 := by
        calc
          (41 : ZMod 258787729201) ^ 28 = (41 : ZMod 258787729201) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 14 * (41 : ZMod 258787729201) ^ 14 := by rw [pow_add]
          _ = 117191554000 := by rw [factor_6_3]; decide
      have factor_6_5 : (41 : ZMod 258787729201) ^ 56 = 185571050034 := by
        calc
          (41 : ZMod 258787729201) ^ 56 = (41 : ZMod 258787729201) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 28 * (41 : ZMod 258787729201) ^ 28 := by rw [pow_add]
          _ = 185571050034 := by rw [factor_6_4]; decide
      have factor_6_6 : (41 : ZMod 258787729201) ^ 113 = 80846186748 := by
        calc
          (41 : ZMod 258787729201) ^ 113 = (41 : ZMod 258787729201) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 56 * (41 : ZMod 258787729201) ^ 56) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 80846186748 := by rw [factor_6_5]; decide
      have factor_6_7 : (41 : ZMod 258787729201) ^ 226 = 179600103956 := by
        calc
          (41 : ZMod 258787729201) ^ 226 = (41 : ZMod 258787729201) ^ (113 + 113) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 113 * (41 : ZMod 258787729201) ^ 113 := by rw [pow_add]
          _ = 179600103956 := by rw [factor_6_6]; decide
      have factor_6_8 : (41 : ZMod 258787729201) ^ 453 = 231029655129 := by
        calc
          (41 : ZMod 258787729201) ^ 453 = (41 : ZMod 258787729201) ^ (226 + 226 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 226 * (41 : ZMod 258787729201) ^ 226) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 231029655129 := by rw [factor_6_7]; decide
      have factor_6_9 : (41 : ZMod 258787729201) ^ 907 = 248743095010 := by
        calc
          (41 : ZMod 258787729201) ^ 907 = (41 : ZMod 258787729201) ^ (453 + 453 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 453 * (41 : ZMod 258787729201) ^ 453) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 248743095010 := by rw [factor_6_8]; decide
      have factor_6_10 : (41 : ZMod 258787729201) ^ 1814 = 58959583015 := by
        calc
          (41 : ZMod 258787729201) ^ 1814 = (41 : ZMod 258787729201) ^ (907 + 907) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 907 * (41 : ZMod 258787729201) ^ 907 := by rw [pow_add]
          _ = 58959583015 := by rw [factor_6_9]; decide
      have factor_6_11 : (41 : ZMod 258787729201) ^ 3629 = 7812718492 := by
        calc
          (41 : ZMod 258787729201) ^ 3629 = (41 : ZMod 258787729201) ^ (1814 + 1814 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1814 * (41 : ZMod 258787729201) ^ 1814) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 7812718492 := by rw [factor_6_10]; decide
      have factor_6_12 : (41 : ZMod 258787729201) ^ 7258 = 243984671001 := by
        calc
          (41 : ZMod 258787729201) ^ 7258 = (41 : ZMod 258787729201) ^ (3629 + 3629) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3629 * (41 : ZMod 258787729201) ^ 3629 := by rw [pow_add]
          _ = 243984671001 := by rw [factor_6_11]; decide
      have factor_6_13 : (41 : ZMod 258787729201) ^ 14517 = 96097714394 := by
        calc
          (41 : ZMod 258787729201) ^ 14517 = (41 : ZMod 258787729201) ^ (7258 + 7258 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 7258 * (41 : ZMod 258787729201) ^ 7258) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 96097714394 := by rw [factor_6_12]; decide
      have factor_6_14 : (41 : ZMod 258787729201) ^ 29035 = 224178405747 := by
        calc
          (41 : ZMod 258787729201) ^ 29035 = (41 : ZMod 258787729201) ^ (14517 + 14517 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 14517 * (41 : ZMod 258787729201) ^ 14517) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 224178405747 := by rw [factor_6_13]; decide
      have factor_6_15 : (41 : ZMod 258787729201) ^ 58070 = 85842033906 := by
        calc
          (41 : ZMod 258787729201) ^ 58070 = (41 : ZMod 258787729201) ^ (29035 + 29035) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 29035 * (41 : ZMod 258787729201) ^ 29035 := by rw [pow_add]
          _ = 85842033906 := by rw [factor_6_14]; decide
      have factor_6_16 : (41 : ZMod 258787729201) ^ 116140 = 81599640564 := by
        calc
          (41 : ZMod 258787729201) ^ 116140 = (41 : ZMod 258787729201) ^ (58070 + 58070) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 58070 * (41 : ZMod 258787729201) ^ 58070 := by rw [pow_add]
          _ = 81599640564 := by rw [factor_6_15]; decide
      have factor_6_17 : (41 : ZMod 258787729201) ^ 232281 = 53475436507 := by
        calc
          (41 : ZMod 258787729201) ^ 232281 = (41 : ZMod 258787729201) ^ (116140 + 116140 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 116140 * (41 : ZMod 258787729201) ^ 116140) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 53475436507 := by rw [factor_6_16]; decide
      have factor_6_18 : (41 : ZMod 258787729201) ^ 464563 = 217782884387 := by
        calc
          (41 : ZMod 258787729201) ^ 464563 = (41 : ZMod 258787729201) ^ (232281 + 232281 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 232281 * (41 : ZMod 258787729201) ^ 232281) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 217782884387 := by rw [factor_6_17]; decide
      have factor_6_19 : (41 : ZMod 258787729201) ^ 929126 = 50386732166 := by
        calc
          (41 : ZMod 258787729201) ^ 929126 = (41 : ZMod 258787729201) ^ (464563 + 464563) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 464563 * (41 : ZMod 258787729201) ^ 464563 := by rw [pow_add]
          _ = 50386732166 := by rw [factor_6_18]; decide
      have factor_6_20 : (41 : ZMod 258787729201) ^ 1858252 = 60244648978 := by
        calc
          (41 : ZMod 258787729201) ^ 1858252 = (41 : ZMod 258787729201) ^ (929126 + 929126) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 929126 * (41 : ZMod 258787729201) ^ 929126 := by rw [pow_add]
          _ = 60244648978 := by rw [factor_6_19]; decide
      have factor_6_21 : (41 : ZMod 258787729201) ^ 3716505 = 240927855906 := by
        calc
          (41 : ZMod 258787729201) ^ 3716505 = (41 : ZMod 258787729201) ^ (1858252 + 1858252 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1858252 * (41 : ZMod 258787729201) ^ 1858252) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 240927855906 := by rw [factor_6_20]; decide
      have factor_6_22 : (41 : ZMod 258787729201) ^ 7433011 = 89789386887 := by
        calc
          (41 : ZMod 258787729201) ^ 7433011 = (41 : ZMod 258787729201) ^ (3716505 + 3716505 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 3716505 * (41 : ZMod 258787729201) ^ 3716505) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 89789386887 := by rw [factor_6_21]; decide
      have factor_6_23 : (41 : ZMod 258787729201) ^ 14866023 = 25771137645 := by
        calc
          (41 : ZMod 258787729201) ^ 14866023 = (41 : ZMod 258787729201) ^ (7433011 + 7433011 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 7433011 * (41 : ZMod 258787729201) ^ 7433011) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 25771137645 := by rw [factor_6_22]; decide
      have factor_6_24 : (41 : ZMod 258787729201) ^ 29732046 = 199584834221 := by
        calc
          (41 : ZMod 258787729201) ^ 29732046 = (41 : ZMod 258787729201) ^ (14866023 + 14866023) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 14866023 * (41 : ZMod 258787729201) ^ 14866023 := by rw [pow_add]
          _ = 199584834221 := by rw [factor_6_23]; decide
      have factor_6_25 : (41 : ZMod 258787729201) ^ 59464092 = 167012334929 := by
        calc
          (41 : ZMod 258787729201) ^ 59464092 = (41 : ZMod 258787729201) ^ (29732046 + 29732046) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 29732046 * (41 : ZMod 258787729201) ^ 29732046 := by rw [pow_add]
          _ = 167012334929 := by rw [factor_6_24]; decide
      have factor_6_26 : (41 : ZMod 258787729201) ^ 118928184 = 243181067299 := by
        calc
          (41 : ZMod 258787729201) ^ 118928184 = (41 : ZMod 258787729201) ^ (59464092 + 59464092) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 59464092 * (41 : ZMod 258787729201) ^ 59464092 := by rw [pow_add]
          _ = 243181067299 := by rw [factor_6_25]; decide
      have factor_6_27 : (41 : ZMod 258787729201) ^ 237856368 = 27253450041 := by
        calc
          (41 : ZMod 258787729201) ^ 237856368 = (41 : ZMod 258787729201) ^ (118928184 + 118928184) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 118928184 * (41 : ZMod 258787729201) ^ 118928184 := by rw [pow_add]
          _ = 27253450041 := by rw [factor_6_26]; decide
      have factor_6_28 : (41 : ZMod 258787729201) ^ 475712737 = 85463464596 := by
        calc
          (41 : ZMod 258787729201) ^ 475712737 = (41 : ZMod 258787729201) ^ (237856368 + 237856368 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 237856368 * (41 : ZMod 258787729201) ^ 237856368) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 85463464596 := by rw [factor_6_27]; decide
      have factor_6_29 : (41 : ZMod 258787729201) ^ 951425475 = 140896130484 := by
        calc
          (41 : ZMod 258787729201) ^ 951425475 = (41 : ZMod 258787729201) ^ (475712737 + 475712737 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 475712737 * (41 : ZMod 258787729201) ^ 475712737) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 140896130484 := by rw [factor_6_28]; decide
      have factor_6_30 : (41 : ZMod 258787729201) ^ 1902850950 = 65133452875 := by
        calc
          (41 : ZMod 258787729201) ^ 1902850950 = (41 : ZMod 258787729201) ^ (951425475 + 951425475) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 951425475 * (41 : ZMod 258787729201) ^ 951425475 := by rw [pow_add]
          _ = 65133452875 := by rw [factor_6_29]; decide
      have factor_6_31 : (41 : ZMod 258787729201) ^ 3805701900 = 3422150744 := by
        calc
          (41 : ZMod 258787729201) ^ 3805701900 = (41 : ZMod 258787729201) ^ (1902850950 + 1902850950) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1902850950 * (41 : ZMod 258787729201) ^ 1902850950 := by rw [pow_add]
          _ = 3422150744 := by rw [factor_6_30]; decide
      have factor_6_32 : (41 : ZMod 258787729201) ^ 7611403800 = 255542270585 := by
        calc
          (41 : ZMod 258787729201) ^ 7611403800 = (41 : ZMod 258787729201) ^ (3805701900 + 3805701900) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3805701900 * (41 : ZMod 258787729201) ^ 3805701900 := by rw [pow_add]
          _ = 255542270585 := by rw [factor_6_31]; decide
      have factor_6_33 : (41 : ZMod 258787729201) ^ 15222807600 = 226248577739 := by
        calc
          (41 : ZMod 258787729201) ^ 15222807600 = (41 : ZMod 258787729201) ^ (7611403800 + 7611403800) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 7611403800 * (41 : ZMod 258787729201) ^ 7611403800 := by rw [pow_add]
          _ = 226248577739 := by rw [factor_6_32]; decide
      change (41 : ZMod 258787729201) ^ 15222807600 ≠ 1
      rw [factor_6_33]
      decide
    ·
      have factor_7_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_7_1 : (41 : ZMod 258787729201) ^ 3 = 68921 := by
        calc
          (41 : ZMod 258787729201) ^ 3 = (41 : ZMod 258787729201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 68921 := by rw [factor_7_0]; decide
      have factor_7_2 : (41 : ZMod 258787729201) ^ 6 = 4750104241 := by
        calc
          (41 : ZMod 258787729201) ^ 6 = (41 : ZMod 258787729201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3 * (41 : ZMod 258787729201) ^ 3 := by rw [pow_add]
          _ = 4750104241 := by rw [factor_7_1]; decide
      have factor_7_3 : (41 : ZMod 258787729201) ^ 12 = 138481211700 := by
        calc
          (41 : ZMod 258787729201) ^ 12 = (41 : ZMod 258787729201) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 6 * (41 : ZMod 258787729201) ^ 6 := by rw [pow_add]
          _ = 138481211700 := by rw [factor_7_2]; decide
      have factor_7_4 : (41 : ZMod 258787729201) ^ 25 = 47695752062 := by
        calc
          (41 : ZMod 258787729201) ^ 25 = (41 : ZMod 258787729201) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 12 * (41 : ZMod 258787729201) ^ 12) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 47695752062 := by rw [factor_7_3]; decide
      have factor_7_5 : (41 : ZMod 258787729201) ^ 50 = 89727157645 := by
        calc
          (41 : ZMod 258787729201) ^ 50 = (41 : ZMod 258787729201) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 25 * (41 : ZMod 258787729201) ^ 25 := by rw [pow_add]
          _ = 89727157645 := by rw [factor_7_4]; decide
      have factor_7_6 : (41 : ZMod 258787729201) ^ 101 = 74642926176 := by
        calc
          (41 : ZMod 258787729201) ^ 101 = (41 : ZMod 258787729201) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 50 * (41 : ZMod 258787729201) ^ 50) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 74642926176 := by rw [factor_7_5]; decide
      have factor_7_7 : (41 : ZMod 258787729201) ^ 202 = 201763470386 := by
        calc
          (41 : ZMod 258787729201) ^ 202 = (41 : ZMod 258787729201) ^ (101 + 101) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 101 * (41 : ZMod 258787729201) ^ 101 := by rw [pow_add]
          _ = 201763470386 := by rw [factor_7_6]; decide
      have factor_7_8 : (41 : ZMod 258787729201) ^ 405 = 202634783662 := by
        calc
          (41 : ZMod 258787729201) ^ 405 = (41 : ZMod 258787729201) ^ (202 + 202 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 202 * (41 : ZMod 258787729201) ^ 202) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 202634783662 := by rw [factor_7_7]; decide
      have factor_7_9 : (41 : ZMod 258787729201) ^ 811 = 43660427310 := by
        calc
          (41 : ZMod 258787729201) ^ 811 = (41 : ZMod 258787729201) ^ (405 + 405 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 405 * (41 : ZMod 258787729201) ^ 405) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 43660427310 := by rw [factor_7_8]; decide
      have factor_7_10 : (41 : ZMod 258787729201) ^ 1623 = 181337204487 := by
        calc
          (41 : ZMod 258787729201) ^ 1623 = (41 : ZMod 258787729201) ^ (811 + 811 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 811 * (41 : ZMod 258787729201) ^ 811) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 181337204487 := by rw [factor_7_9]; decide
      have factor_7_11 : (41 : ZMod 258787729201) ^ 3247 = 82962525476 := by
        calc
          (41 : ZMod 258787729201) ^ 3247 = (41 : ZMod 258787729201) ^ (1623 + 1623 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1623 * (41 : ZMod 258787729201) ^ 1623) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 82962525476 := by rw [factor_7_10]; decide
      have factor_7_12 : (41 : ZMod 258787729201) ^ 6494 = 58462838673 := by
        calc
          (41 : ZMod 258787729201) ^ 6494 = (41 : ZMod 258787729201) ^ (3247 + 3247) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3247 * (41 : ZMod 258787729201) ^ 3247 := by rw [pow_add]
          _ = 58462838673 := by rw [factor_7_11]; decide
      have factor_7_13 : (41 : ZMod 258787729201) ^ 12989 = 50751041738 := by
        calc
          (41 : ZMod 258787729201) ^ 12989 = (41 : ZMod 258787729201) ^ (6494 + 6494 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 6494 * (41 : ZMod 258787729201) ^ 6494) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 50751041738 := by rw [factor_7_12]; decide
      have factor_7_14 : (41 : ZMod 258787729201) ^ 25978 = 104421230117 := by
        calc
          (41 : ZMod 258787729201) ^ 25978 = (41 : ZMod 258787729201) ^ (12989 + 12989) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 12989 * (41 : ZMod 258787729201) ^ 12989 := by rw [pow_add]
          _ = 104421230117 := by rw [factor_7_13]; decide
      have factor_7_15 : (41 : ZMod 258787729201) ^ 51957 = 102850088153 := by
        calc
          (41 : ZMod 258787729201) ^ 51957 = (41 : ZMod 258787729201) ^ (25978 + 25978 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 25978 * (41 : ZMod 258787729201) ^ 25978) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 102850088153 := by rw [factor_7_14]; decide
      have factor_7_16 : (41 : ZMod 258787729201) ^ 103915 = 68715740215 := by
        calc
          (41 : ZMod 258787729201) ^ 103915 = (41 : ZMod 258787729201) ^ (51957 + 51957 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 51957 * (41 : ZMod 258787729201) ^ 51957) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 68715740215 := by rw [factor_7_15]; decide
      have factor_7_17 : (41 : ZMod 258787729201) ^ 207830 = 242703398077 := by
        calc
          (41 : ZMod 258787729201) ^ 207830 = (41 : ZMod 258787729201) ^ (103915 + 103915) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 103915 * (41 : ZMod 258787729201) ^ 103915 := by rw [pow_add]
          _ = 242703398077 := by rw [factor_7_16]; decide
      have factor_7_18 : (41 : ZMod 258787729201) ^ 415661 = 50938474764 := by
        calc
          (41 : ZMod 258787729201) ^ 415661 = (41 : ZMod 258787729201) ^ (207830 + 207830 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 207830 * (41 : ZMod 258787729201) ^ 207830) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 50938474764 := by rw [factor_7_17]; decide
      have factor_7_19 : (41 : ZMod 258787729201) ^ 831323 = 10258855511 := by
        calc
          (41 : ZMod 258787729201) ^ 831323 = (41 : ZMod 258787729201) ^ (415661 + 415661 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 415661 * (41 : ZMod 258787729201) ^ 415661) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 10258855511 := by rw [factor_7_18]; decide
      have factor_7_20 : (41 : ZMod 258787729201) ^ 1662647 = 43528093238 := by
        calc
          (41 : ZMod 258787729201) ^ 1662647 = (41 : ZMod 258787729201) ^ (831323 + 831323 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 831323 * (41 : ZMod 258787729201) ^ 831323) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 43528093238 := by rw [factor_7_19]; decide
      have factor_7_21 : (41 : ZMod 258787729201) ^ 3325294 = 99046177035 := by
        calc
          (41 : ZMod 258787729201) ^ 3325294 = (41 : ZMod 258787729201) ^ (1662647 + 1662647) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1662647 * (41 : ZMod 258787729201) ^ 1662647 := by rw [pow_add]
          _ = 99046177035 := by rw [factor_7_20]; decide
      have factor_7_22 : (41 : ZMod 258787729201) ^ 6650589 = 67061270050 := by
        calc
          (41 : ZMod 258787729201) ^ 6650589 = (41 : ZMod 258787729201) ^ (3325294 + 3325294 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 3325294 * (41 : ZMod 258787729201) ^ 3325294) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 67061270050 := by rw [factor_7_21]; decide
      have factor_7_23 : (41 : ZMod 258787729201) ^ 13301178 = 89955898676 := by
        calc
          (41 : ZMod 258787729201) ^ 13301178 = (41 : ZMod 258787729201) ^ (6650589 + 6650589) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 6650589 * (41 : ZMod 258787729201) ^ 6650589 := by rw [pow_add]
          _ = 89955898676 := by rw [factor_7_22]; decide
      have factor_7_24 : (41 : ZMod 258787729201) ^ 26602357 = 46072221448 := by
        calc
          (41 : ZMod 258787729201) ^ 26602357 = (41 : ZMod 258787729201) ^ (13301178 + 13301178 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 13301178 * (41 : ZMod 258787729201) ^ 13301178) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 46072221448 := by rw [factor_7_23]; decide
      have factor_7_25 : (41 : ZMod 258787729201) ^ 53204714 = 36206642833 := by
        calc
          (41 : ZMod 258787729201) ^ 53204714 = (41 : ZMod 258787729201) ^ (26602357 + 26602357) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 26602357 * (41 : ZMod 258787729201) ^ 26602357 := by rw [pow_add]
          _ = 36206642833 := by rw [factor_7_24]; decide
      have factor_7_26 : (41 : ZMod 258787729201) ^ 106409428 = 65900971229 := by
        calc
          (41 : ZMod 258787729201) ^ 106409428 = (41 : ZMod 258787729201) ^ (53204714 + 53204714) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 53204714 * (41 : ZMod 258787729201) ^ 53204714 := by rw [pow_add]
          _ = 65900971229 := by rw [factor_7_25]; decide
      have factor_7_27 : (41 : ZMod 258787729201) ^ 212818856 = 146473037976 := by
        calc
          (41 : ZMod 258787729201) ^ 212818856 = (41 : ZMod 258787729201) ^ (106409428 + 106409428) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 106409428 * (41 : ZMod 258787729201) ^ 106409428 := by rw [pow_add]
          _ = 146473037976 := by rw [factor_7_26]; decide
      have factor_7_28 : (41 : ZMod 258787729201) ^ 425637712 = 127884721361 := by
        calc
          (41 : ZMod 258787729201) ^ 425637712 = (41 : ZMod 258787729201) ^ (212818856 + 212818856) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 212818856 * (41 : ZMod 258787729201) ^ 212818856 := by rw [pow_add]
          _ = 127884721361 := by rw [factor_7_27]; decide
      have factor_7_29 : (41 : ZMod 258787729201) ^ 851275425 = 90107156147 := by
        calc
          (41 : ZMod 258787729201) ^ 851275425 = (41 : ZMod 258787729201) ^ (425637712 + 425637712 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 425637712 * (41 : ZMod 258787729201) ^ 425637712) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 90107156147 := by rw [factor_7_28]; decide
      have factor_7_30 : (41 : ZMod 258787729201) ^ 1702550850 = 5880602000 := by
        calc
          (41 : ZMod 258787729201) ^ 1702550850 = (41 : ZMod 258787729201) ^ (851275425 + 851275425) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 851275425 * (41 : ZMod 258787729201) ^ 851275425 := by rw [pow_add]
          _ = 5880602000 := by rw [factor_7_29]; decide
      have factor_7_31 : (41 : ZMod 258787729201) ^ 3405101700 = 149086788054 := by
        calc
          (41 : ZMod 258787729201) ^ 3405101700 = (41 : ZMod 258787729201) ^ (1702550850 + 1702550850) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1702550850 * (41 : ZMod 258787729201) ^ 1702550850 := by rw [pow_add]
          _ = 149086788054 := by rw [factor_7_30]; decide
      have factor_7_32 : (41 : ZMod 258787729201) ^ 6810203400 = 197255778296 := by
        calc
          (41 : ZMod 258787729201) ^ 6810203400 = (41 : ZMod 258787729201) ^ (3405101700 + 3405101700) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 3405101700 * (41 : ZMod 258787729201) ^ 3405101700 := by rw [pow_add]
          _ = 197255778296 := by rw [factor_7_31]; decide
      have factor_7_33 : (41 : ZMod 258787729201) ^ 13620406800 = 58103591634 := by
        calc
          (41 : ZMod 258787729201) ^ 13620406800 = (41 : ZMod 258787729201) ^ (6810203400 + 6810203400) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 6810203400 * (41 : ZMod 258787729201) ^ 6810203400 := by rw [pow_add]
          _ = 58103591634 := by rw [factor_7_32]; decide
      change (41 : ZMod 258787729201) ^ 13620406800 ≠ 1
      rw [factor_7_33]
      decide
    ·
      have factor_8_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_8_1 : (41 : ZMod 258787729201) ^ 2 = 1681 := by
        calc
          (41 : ZMod 258787729201) ^ 2 = (41 : ZMod 258787729201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1 := by rw [pow_add]
          _ = 1681 := by rw [factor_8_0]; decide
      have factor_8_2 : (41 : ZMod 258787729201) ^ 5 = 115856201 := by
        calc
          (41 : ZMod 258787729201) ^ 5 = (41 : ZMod 258787729201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2 * (41 : ZMod 258787729201) ^ 2) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 115856201 := by rw [factor_8_1]; decide
      have factor_8_3 : (41 : ZMod 258787729201) ^ 10 = 116159684134 := by
        calc
          (41 : ZMod 258787729201) ^ 10 = (41 : ZMod 258787729201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5 * (41 : ZMod 258787729201) ^ 5 := by rw [pow_add]
          _ = 116159684134 := by rw [factor_8_2]; decide
      have factor_8_4 : (41 : ZMod 258787729201) ^ 20 = 101763977189 := by
        calc
          (41 : ZMod 258787729201) ^ 20 = (41 : ZMod 258787729201) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 10 * (41 : ZMod 258787729201) ^ 10 := by rw [pow_add]
          _ = 101763977189 := by rw [factor_8_3]; decide
      have factor_8_5 : (41 : ZMod 258787729201) ^ 41 = 255500036377 := by
        calc
          (41 : ZMod 258787729201) ^ 41 = (41 : ZMod 258787729201) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 20 * (41 : ZMod 258787729201) ^ 20) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 255500036377 := by rw [factor_8_4]; decide
      have factor_8_6 : (41 : ZMod 258787729201) ^ 83 = 33134551708 := by
        calc
          (41 : ZMod 258787729201) ^ 83 = (41 : ZMod 258787729201) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 41 * (41 : ZMod 258787729201) ^ 41) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 33134551708 := by rw [factor_8_5]; decide
      have factor_8_7 : (41 : ZMod 258787729201) ^ 167 = 98442772886 := by
        calc
          (41 : ZMod 258787729201) ^ 167 = (41 : ZMod 258787729201) ^ (83 + 83 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 83 * (41 : ZMod 258787729201) ^ 83) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 98442772886 := by rw [factor_8_6]; decide
      have factor_8_8 : (41 : ZMod 258787729201) ^ 335 = 142830383023 := by
        calc
          (41 : ZMod 258787729201) ^ 335 = (41 : ZMod 258787729201) ^ (167 + 167 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 167 * (41 : ZMod 258787729201) ^ 167) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 142830383023 := by rw [factor_8_7]; decide
      have factor_8_9 : (41 : ZMod 258787729201) ^ 670 = 235145026696 := by
        calc
          (41 : ZMod 258787729201) ^ 670 = (41 : ZMod 258787729201) ^ (335 + 335) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 335 * (41 : ZMod 258787729201) ^ 335 := by rw [pow_add]
          _ = 235145026696 := by rw [factor_8_8]; decide
      have factor_8_10 : (41 : ZMod 258787729201) ^ 1341 = 84069983705 := by
        calc
          (41 : ZMod 258787729201) ^ 1341 = (41 : ZMod 258787729201) ^ (670 + 670 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 670 * (41 : ZMod 258787729201) ^ 670) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 84069983705 := by rw [factor_8_9]; decide
      have factor_8_11 : (41 : ZMod 258787729201) ^ 2682 = 60153198098 := by
        calc
          (41 : ZMod 258787729201) ^ 2682 = (41 : ZMod 258787729201) ^ (1341 + 1341) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1341 * (41 : ZMod 258787729201) ^ 1341 := by rw [pow_add]
          _ = 60153198098 := by rw [factor_8_10]; decide
      have factor_8_12 : (41 : ZMod 258787729201) ^ 5365 = 154386589073 := by
        calc
          (41 : ZMod 258787729201) ^ 5365 = (41 : ZMod 258787729201) ^ (2682 + 2682 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2682 * (41 : ZMod 258787729201) ^ 2682) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 154386589073 := by rw [factor_8_11]; decide
      have factor_8_13 : (41 : ZMod 258787729201) ^ 10730 = 167403643264 := by
        calc
          (41 : ZMod 258787729201) ^ 10730 = (41 : ZMod 258787729201) ^ (5365 + 5365) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5365 * (41 : ZMod 258787729201) ^ 5365 := by rw [pow_add]
          _ = 167403643264 := by rw [factor_8_12]; decide
      have factor_8_14 : (41 : ZMod 258787729201) ^ 21460 = 197140746685 := by
        calc
          (41 : ZMod 258787729201) ^ 21460 = (41 : ZMod 258787729201) ^ (10730 + 10730) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 10730 * (41 : ZMod 258787729201) ^ 10730 := by rw [pow_add]
          _ = 197140746685 := by rw [factor_8_13]; decide
      have factor_8_15 : (41 : ZMod 258787729201) ^ 42921 = 52681454302 := by
        calc
          (41 : ZMod 258787729201) ^ 42921 = (41 : ZMod 258787729201) ^ (21460 + 21460 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 21460 * (41 : ZMod 258787729201) ^ 21460) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 52681454302 := by rw [factor_8_14]; decide
      have factor_8_16 : (41 : ZMod 258787729201) ^ 85843 = 142355655311 := by
        calc
          (41 : ZMod 258787729201) ^ 85843 = (41 : ZMod 258787729201) ^ (42921 + 42921 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 42921 * (41 : ZMod 258787729201) ^ 42921) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 142355655311 := by rw [factor_8_15]; decide
      have factor_8_17 : (41 : ZMod 258787729201) ^ 171686 = 108626790423 := by
        calc
          (41 : ZMod 258787729201) ^ 171686 = (41 : ZMod 258787729201) ^ (85843 + 85843) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 85843 * (41 : ZMod 258787729201) ^ 85843 := by rw [pow_add]
          _ = 108626790423 := by rw [factor_8_16]; decide
      have factor_8_18 : (41 : ZMod 258787729201) ^ 343372 = 139589987750 := by
        calc
          (41 : ZMod 258787729201) ^ 343372 = (41 : ZMod 258787729201) ^ (171686 + 171686) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 171686 * (41 : ZMod 258787729201) ^ 171686 := by rw [pow_add]
          _ = 139589987750 := by rw [factor_8_17]; decide
      have factor_8_19 : (41 : ZMod 258787729201) ^ 686745 = 204502421679 := by
        calc
          (41 : ZMod 258787729201) ^ 686745 = (41 : ZMod 258787729201) ^ (343372 + 343372 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 343372 * (41 : ZMod 258787729201) ^ 343372) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 204502421679 := by rw [factor_8_18]; decide
      have factor_8_20 : (41 : ZMod 258787729201) ^ 1373491 = 50771694532 := by
        calc
          (41 : ZMod 258787729201) ^ 1373491 = (41 : ZMod 258787729201) ^ (686745 + 686745 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 686745 * (41 : ZMod 258787729201) ^ 686745) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 50771694532 := by rw [factor_8_19]; decide
      have factor_8_21 : (41 : ZMod 258787729201) ^ 2746982 = 61558779181 := by
        calc
          (41 : ZMod 258787729201) ^ 2746982 = (41 : ZMod 258787729201) ^ (1373491 + 1373491) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1373491 * (41 : ZMod 258787729201) ^ 1373491 := by rw [pow_add]
          _ = 61558779181 := by rw [factor_8_20]; decide
      have factor_8_22 : (41 : ZMod 258787729201) ^ 5493965 = 152102253540 := by
        calc
          (41 : ZMod 258787729201) ^ 5493965 = (41 : ZMod 258787729201) ^ (2746982 + 2746982 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2746982 * (41 : ZMod 258787729201) ^ 2746982) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 152102253540 := by rw [factor_8_21]; decide
      have factor_8_23 : (41 : ZMod 258787729201) ^ 10987930 = 197610446991 := by
        calc
          (41 : ZMod 258787729201) ^ 10987930 = (41 : ZMod 258787729201) ^ (5493965 + 5493965) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5493965 * (41 : ZMod 258787729201) ^ 5493965 := by rw [pow_add]
          _ = 197610446991 := by rw [factor_8_22]; decide
      have factor_8_24 : (41 : ZMod 258787729201) ^ 21975860 = 18576094166 := by
        calc
          (41 : ZMod 258787729201) ^ 21975860 = (41 : ZMod 258787729201) ^ (10987930 + 10987930) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 10987930 * (41 : ZMod 258787729201) ^ 10987930 := by rw [pow_add]
          _ = 18576094166 := by rw [factor_8_23]; decide
      have factor_8_25 : (41 : ZMod 258787729201) ^ 43951720 = 155694509196 := by
        calc
          (41 : ZMod 258787729201) ^ 43951720 = (41 : ZMod 258787729201) ^ (21975860 + 21975860) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 21975860 * (41 : ZMod 258787729201) ^ 21975860 := by rw [pow_add]
          _ = 155694509196 := by rw [factor_8_24]; decide
      have factor_8_26 : (41 : ZMod 258787729201) ^ 87903440 = 101670820965 := by
        calc
          (41 : ZMod 258787729201) ^ 87903440 = (41 : ZMod 258787729201) ^ (43951720 + 43951720) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 43951720 * (41 : ZMod 258787729201) ^ 43951720 := by rw [pow_add]
          _ = 101670820965 := by rw [factor_8_25]; decide
      have factor_8_27 : (41 : ZMod 258787729201) ^ 175806881 = 227794594094 := by
        calc
          (41 : ZMod 258787729201) ^ 175806881 = (41 : ZMod 258787729201) ^ (87903440 + 87903440 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 87903440 * (41 : ZMod 258787729201) ^ 87903440) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 227794594094 := by rw [factor_8_26]; decide
      have factor_8_28 : (41 : ZMod 258787729201) ^ 351613762 = 89967058960 := by
        calc
          (41 : ZMod 258787729201) ^ 351613762 = (41 : ZMod 258787729201) ^ (175806881 + 175806881) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 175806881 * (41 : ZMod 258787729201) ^ 175806881 := by rw [pow_add]
          _ = 89967058960 := by rw [factor_8_27]; decide
      have factor_8_29 : (41 : ZMod 258787729201) ^ 703227525 = 146645030952 := by
        calc
          (41 : ZMod 258787729201) ^ 703227525 = (41 : ZMod 258787729201) ^ (351613762 + 351613762 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 351613762 * (41 : ZMod 258787729201) ^ 351613762) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 146645030952 := by rw [factor_8_28]; decide
      have factor_8_30 : (41 : ZMod 258787729201) ^ 1406455050 = 252792348618 := by
        calc
          (41 : ZMod 258787729201) ^ 1406455050 = (41 : ZMod 258787729201) ^ (703227525 + 703227525) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 703227525 * (41 : ZMod 258787729201) ^ 703227525 := by rw [pow_add]
          _ = 252792348618 := by rw [factor_8_29]; decide
      have factor_8_31 : (41 : ZMod 258787729201) ^ 2812910100 = 136279447859 := by
        calc
          (41 : ZMod 258787729201) ^ 2812910100 = (41 : ZMod 258787729201) ^ (1406455050 + 1406455050) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1406455050 * (41 : ZMod 258787729201) ^ 1406455050 := by rw [pow_add]
          _ = 136279447859 := by rw [factor_8_30]; decide
      have factor_8_32 : (41 : ZMod 258787729201) ^ 5625820200 = 94374417126 := by
        calc
          (41 : ZMod 258787729201) ^ 5625820200 = (41 : ZMod 258787729201) ^ (2812910100 + 2812910100) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2812910100 * (41 : ZMod 258787729201) ^ 2812910100 := by rw [pow_add]
          _ = 94374417126 := by rw [factor_8_31]; decide
      have factor_8_33 : (41 : ZMod 258787729201) ^ 11251640400 = 57813336710 := by
        calc
          (41 : ZMod 258787729201) ^ 11251640400 = (41 : ZMod 258787729201) ^ (5625820200 + 5625820200) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 5625820200 * (41 : ZMod 258787729201) ^ 5625820200 := by rw [pow_add]
          _ = 57813336710 := by rw [factor_8_32]; decide
      change (41 : ZMod 258787729201) ^ 11251640400 ≠ 1
      rw [factor_8_33]
      decide
    ·
      have factor_9_0 : (41 : ZMod 258787729201) ^ 1 = 41 := by norm_num
      have factor_9_1 : (41 : ZMod 258787729201) ^ 2 = 1681 := by
        calc
          (41 : ZMod 258787729201) ^ 2 = (41 : ZMod 258787729201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1 * (41 : ZMod 258787729201) ^ 1 := by rw [pow_add]
          _ = 1681 := by rw [factor_9_0]; decide
      have factor_9_2 : (41 : ZMod 258787729201) ^ 4 = 2825761 := by
        calc
          (41 : ZMod 258787729201) ^ 4 = (41 : ZMod 258787729201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2 * (41 : ZMod 258787729201) ^ 2 := by rw [pow_add]
          _ = 2825761 := by rw [factor_9_1]; decide
      have factor_9_3 : (41 : ZMod 258787729201) ^ 8 = 221293353091 := by
        calc
          (41 : ZMod 258787729201) ^ 8 = (41 : ZMod 258787729201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4 * (41 : ZMod 258787729201) ^ 4 := by rw [pow_add]
          _ = 221293353091 := by rw [factor_9_2]; decide
      have factor_9_4 : (41 : ZMod 258787729201) ^ 16 = 70415667193 := by
        calc
          (41 : ZMod 258787729201) ^ 16 = (41 : ZMod 258787729201) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 8 * (41 : ZMod 258787729201) ^ 8 := by rw [pow_add]
          _ = 70415667193 := by rw [factor_9_3]; decide
      have factor_9_5 : (41 : ZMod 258787729201) ^ 33 = 150509004730 := by
        calc
          (41 : ZMod 258787729201) ^ 33 = (41 : ZMod 258787729201) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 16 * (41 : ZMod 258787729201) ^ 16) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 150509004730 := by rw [factor_9_4]; decide
      have factor_9_6 : (41 : ZMod 258787729201) ^ 66 = 66663786009 := by
        calc
          (41 : ZMod 258787729201) ^ 66 = (41 : ZMod 258787729201) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 33 * (41 : ZMod 258787729201) ^ 33 := by rw [pow_add]
          _ = 66663786009 := by rw [factor_9_5]; decide
      have factor_9_7 : (41 : ZMod 258787729201) ^ 132 = 152472380355 := by
        calc
          (41 : ZMod 258787729201) ^ 132 = (41 : ZMod 258787729201) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 66 * (41 : ZMod 258787729201) ^ 66 := by rw [pow_add]
          _ = 152472380355 := by rw [factor_9_6]; decide
      have factor_9_8 : (41 : ZMod 258787729201) ^ 265 = 43346006516 := by
        calc
          (41 : ZMod 258787729201) ^ 265 = (41 : ZMod 258787729201) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 132 * (41 : ZMod 258787729201) ^ 132) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 43346006516 := by rw [factor_9_7]; decide
      have factor_9_9 : (41 : ZMod 258787729201) ^ 531 = 122656891583 := by
        calc
          (41 : ZMod 258787729201) ^ 531 = (41 : ZMod 258787729201) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 265 * (41 : ZMod 258787729201) ^ 265) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 122656891583 := by rw [factor_9_8]; decide
      have factor_9_10 : (41 : ZMod 258787729201) ^ 1063 = 203282064061 := by
        calc
          (41 : ZMod 258787729201) ^ 1063 = (41 : ZMod 258787729201) ^ (531 + 531 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 531 * (41 : ZMod 258787729201) ^ 531) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 203282064061 := by rw [factor_9_9]; decide
      have factor_9_11 : (41 : ZMod 258787729201) ^ 2127 = 89759960536 := by
        calc
          (41 : ZMod 258787729201) ^ 2127 = (41 : ZMod 258787729201) ^ (1063 + 1063 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1063 * (41 : ZMod 258787729201) ^ 1063) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 89759960536 := by rw [factor_9_10]; decide
      have factor_9_12 : (41 : ZMod 258787729201) ^ 4255 = 119081277034 := by
        calc
          (41 : ZMod 258787729201) ^ 4255 = (41 : ZMod 258787729201) ^ (2127 + 2127 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 2127 * (41 : ZMod 258787729201) ^ 2127) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 119081277034 := by rw [factor_9_11]; decide
      have factor_9_13 : (41 : ZMod 258787729201) ^ 8510 = 37861340730 := by
        calc
          (41 : ZMod 258787729201) ^ 8510 = (41 : ZMod 258787729201) ^ (4255 + 4255) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4255 * (41 : ZMod 258787729201) ^ 4255 := by rw [pow_add]
          _ = 37861340730 := by rw [factor_9_12]; decide
      have factor_9_14 : (41 : ZMod 258787729201) ^ 17020 = 219305580533 := by
        calc
          (41 : ZMod 258787729201) ^ 17020 = (41 : ZMod 258787729201) ^ (8510 + 8510) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 8510 * (41 : ZMod 258787729201) ^ 8510 := by rw [pow_add]
          _ = 219305580533 := by rw [factor_9_13]; decide
      have factor_9_15 : (41 : ZMod 258787729201) ^ 34041 = 11980932213 := by
        calc
          (41 : ZMod 258787729201) ^ 34041 = (41 : ZMod 258787729201) ^ (17020 + 17020 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 17020 * (41 : ZMod 258787729201) ^ 17020) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 11980932213 := by rw [factor_9_14]; decide
      have factor_9_16 : (41 : ZMod 258787729201) ^ 68082 = 32281260910 := by
        calc
          (41 : ZMod 258787729201) ^ 68082 = (41 : ZMod 258787729201) ^ (34041 + 34041) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 34041 * (41 : ZMod 258787729201) ^ 34041 := by rw [pow_add]
          _ = 32281260910 := by rw [factor_9_15]; decide
      have factor_9_17 : (41 : ZMod 258787729201) ^ 136165 = 197108455632 := by
        calc
          (41 : ZMod 258787729201) ^ 136165 = (41 : ZMod 258787729201) ^ (68082 + 68082 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 68082 * (41 : ZMod 258787729201) ^ 68082) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 197108455632 := by rw [factor_9_16]; decide
      have factor_9_18 : (41 : ZMod 258787729201) ^ 272330 = 51559801891 := by
        calc
          (41 : ZMod 258787729201) ^ 272330 = (41 : ZMod 258787729201) ^ (136165 + 136165) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 136165 * (41 : ZMod 258787729201) ^ 136165 := by rw [pow_add]
          _ = 51559801891 := by rw [factor_9_17]; decide
      have factor_9_19 : (41 : ZMod 258787729201) ^ 544660 = 195514252794 := by
        calc
          (41 : ZMod 258787729201) ^ 544660 = (41 : ZMod 258787729201) ^ (272330 + 272330) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 272330 * (41 : ZMod 258787729201) ^ 272330 := by rw [pow_add]
          _ = 195514252794 := by rw [factor_9_18]; decide
      have factor_9_20 : (41 : ZMod 258787729201) ^ 1089320 = 132950926035 := by
        calc
          (41 : ZMod 258787729201) ^ 1089320 = (41 : ZMod 258787729201) ^ (544660 + 544660) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 544660 * (41 : ZMod 258787729201) ^ 544660 := by rw [pow_add]
          _ = 132950926035 := by rw [factor_9_19]; decide
      have factor_9_21 : (41 : ZMod 258787729201) ^ 2178641 = 125232361335 := by
        calc
          (41 : ZMod 258787729201) ^ 2178641 = (41 : ZMod 258787729201) ^ (1089320 + 1089320 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 1089320 * (41 : ZMod 258787729201) ^ 1089320) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 125232361335 := by rw [factor_9_20]; decide
      have factor_9_22 : (41 : ZMod 258787729201) ^ 4357282 = 107171327457 := by
        calc
          (41 : ZMod 258787729201) ^ 4357282 = (41 : ZMod 258787729201) ^ (2178641 + 2178641) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2178641 * (41 : ZMod 258787729201) ^ 2178641 := by rw [pow_add]
          _ = 107171327457 := by rw [factor_9_21]; decide
      have factor_9_23 : (41 : ZMod 258787729201) ^ 8714565 = 85204513790 := by
        calc
          (41 : ZMod 258787729201) ^ 8714565 = (41 : ZMod 258787729201) ^ (4357282 + 4357282 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 4357282 * (41 : ZMod 258787729201) ^ 4357282) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 85204513790 := by rw [factor_9_22]; decide
      have factor_9_24 : (41 : ZMod 258787729201) ^ 17429130 = 151187359115 := by
        calc
          (41 : ZMod 258787729201) ^ 17429130 = (41 : ZMod 258787729201) ^ (8714565 + 8714565) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 8714565 * (41 : ZMod 258787729201) ^ 8714565 := by rw [pow_add]
          _ = 151187359115 := by rw [factor_9_23]; decide
      have factor_9_25 : (41 : ZMod 258787729201) ^ 34858260 = 187541256122 := by
        calc
          (41 : ZMod 258787729201) ^ 34858260 = (41 : ZMod 258787729201) ^ (17429130 + 17429130) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 17429130 * (41 : ZMod 258787729201) ^ 17429130 := by rw [pow_add]
          _ = 187541256122 := by rw [factor_9_24]; decide
      have factor_9_26 : (41 : ZMod 258787729201) ^ 69716521 = 59953464706 := by
        calc
          (41 : ZMod 258787729201) ^ 69716521 = (41 : ZMod 258787729201) ^ (34858260 + 34858260 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 34858260 * (41 : ZMod 258787729201) ^ 34858260) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 59953464706 := by rw [factor_9_25]; decide
      have factor_9_27 : (41 : ZMod 258787729201) ^ 139433043 = 114515251860 := by
        calc
          (41 : ZMod 258787729201) ^ 139433043 = (41 : ZMod 258787729201) ^ (69716521 + 69716521 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 69716521 * (41 : ZMod 258787729201) ^ 69716521) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 114515251860 := by rw [factor_9_26]; decide
      have factor_9_28 : (41 : ZMod 258787729201) ^ 278866087 = 196531297848 := by
        calc
          (41 : ZMod 258787729201) ^ 278866087 = (41 : ZMod 258787729201) ^ (139433043 + 139433043 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 139433043 * (41 : ZMod 258787729201) ^ 139433043) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 196531297848 := by rw [factor_9_27]; decide
      have factor_9_29 : (41 : ZMod 258787729201) ^ 557732175 = 165308902536 := by
        calc
          (41 : ZMod 258787729201) ^ 557732175 = (41 : ZMod 258787729201) ^ (278866087 + 278866087 + 1) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = ((41 : ZMod 258787729201) ^ 278866087 * (41 : ZMod 258787729201) ^ 278866087) * (41 : ZMod 258787729201) := by rw [pow_succ, pow_add]
          _ = 165308902536 := by rw [factor_9_28]; decide
      have factor_9_30 : (41 : ZMod 258787729201) ^ 1115464350 = 79048351514 := by
        calc
          (41 : ZMod 258787729201) ^ 1115464350 = (41 : ZMod 258787729201) ^ (557732175 + 557732175) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 557732175 * (41 : ZMod 258787729201) ^ 557732175 := by rw [pow_add]
          _ = 79048351514 := by rw [factor_9_29]; decide
      have factor_9_31 : (41 : ZMod 258787729201) ^ 2230928700 = 48423466391 := by
        calc
          (41 : ZMod 258787729201) ^ 2230928700 = (41 : ZMod 258787729201) ^ (1115464350 + 1115464350) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 1115464350 * (41 : ZMod 258787729201) ^ 1115464350 := by rw [pow_add]
          _ = 48423466391 := by rw [factor_9_30]; decide
      have factor_9_32 : (41 : ZMod 258787729201) ^ 4461857400 = 257012546639 := by
        calc
          (41 : ZMod 258787729201) ^ 4461857400 = (41 : ZMod 258787729201) ^ (2230928700 + 2230928700) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 2230928700 * (41 : ZMod 258787729201) ^ 2230928700 := by rw [pow_add]
          _ = 257012546639 := by rw [factor_9_31]; decide
      have factor_9_33 : (41 : ZMod 258787729201) ^ 8923714800 = 199047742387 := by
        calc
          (41 : ZMod 258787729201) ^ 8923714800 = (41 : ZMod 258787729201) ^ (4461857400 + 4461857400) :=
            congrArg (fun n : ℕ => (41 : ZMod 258787729201) ^ n) (by norm_num)
          _ = (41 : ZMod 258787729201) ^ 4461857400 * (41 : ZMod 258787729201) ^ 4461857400 := by rw [pow_add]
          _ = 199047742387 := by rw [factor_9_32]; decide
      change (41 : ZMod 258787729201) ^ 8923714800 ≠ 1
      rw [factor_9_33]
      decide

#print axioms prime_lucas_258787729201

end TotientTailPeriodKiller
end Erdos249257
