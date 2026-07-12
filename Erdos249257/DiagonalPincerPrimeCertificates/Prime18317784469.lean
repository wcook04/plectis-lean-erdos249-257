import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1526482039

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_18317784469 : Nat.Prime 18317784469 := by
  apply lucas_primality 18317784469 (6 : ZMod 18317784469)
  ·
      have fermat_0 : (6 : ZMod 18317784469) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 18317784469) ^ 2 = 36 := by
        calc
          (6 : ZMod 18317784469) ^ 2 = (6 : ZMod 18317784469) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 1 * (6 : ZMod 18317784469) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 18317784469) ^ 4 = 1296 := by
        calc
          (6 : ZMod 18317784469) ^ 4 = (6 : ZMod 18317784469) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 2 * (6 : ZMod 18317784469) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 18317784469) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 18317784469) ^ 8 = (6 : ZMod 18317784469) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4 * (6 : ZMod 18317784469) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 18317784469) ^ 17 = 1026595380 := by
        calc
          (6 : ZMod 18317784469) ^ 17 = (6 : ZMod 18317784469) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 8 * (6 : ZMod 18317784469) ^ 8) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 1026595380 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 18317784469) ^ 34 = 6519150395 := by
        calc
          (6 : ZMod 18317784469) ^ 34 = (6 : ZMod 18317784469) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 17 * (6 : ZMod 18317784469) ^ 17 := by rw [pow_add]
          _ = 6519150395 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 18317784469) ^ 68 = 18093256447 := by
        calc
          (6 : ZMod 18317784469) ^ 68 = (6 : ZMod 18317784469) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 34 * (6 : ZMod 18317784469) ^ 34 := by rw [pow_add]
          _ = 18093256447 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 18317784469) ^ 136 = 81485859 := by
        calc
          (6 : ZMod 18317784469) ^ 136 = (6 : ZMod 18317784469) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 68 * (6 : ZMod 18317784469) ^ 68 := by rw [pow_add]
          _ = 81485859 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 18317784469) ^ 272 = 4795937947 := by
        calc
          (6 : ZMod 18317784469) ^ 272 = (6 : ZMod 18317784469) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 136 * (6 : ZMod 18317784469) ^ 136 := by rw [pow_add]
          _ = 4795937947 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 18317784469) ^ 545 = 12206849470 := by
        calc
          (6 : ZMod 18317784469) ^ 545 = (6 : ZMod 18317784469) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 272 * (6 : ZMod 18317784469) ^ 272) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 12206849470 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 18317784469) ^ 1091 = 9618585720 := by
        calc
          (6 : ZMod 18317784469) ^ 1091 = (6 : ZMod 18317784469) ^ (545 + 545 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 545 * (6 : ZMod 18317784469) ^ 545) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 9618585720 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 18317784469) ^ 2183 = 4103680532 := by
        calc
          (6 : ZMod 18317784469) ^ 2183 = (6 : ZMod 18317784469) ^ (1091 + 1091 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 1091 * (6 : ZMod 18317784469) ^ 1091) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 4103680532 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 18317784469) ^ 4367 = 13978714943 := by
        calc
          (6 : ZMod 18317784469) ^ 4367 = (6 : ZMod 18317784469) ^ (2183 + 2183 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2183 * (6 : ZMod 18317784469) ^ 2183) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 13978714943 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 18317784469) ^ 8734 = 13279027090 := by
        calc
          (6 : ZMod 18317784469) ^ 8734 = (6 : ZMod 18317784469) ^ (4367 + 4367) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4367 * (6 : ZMod 18317784469) ^ 4367 := by rw [pow_add]
          _ = 13279027090 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 18317784469) ^ 17469 = 12235375375 := by
        calc
          (6 : ZMod 18317784469) ^ 17469 = (6 : ZMod 18317784469) ^ (8734 + 8734 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 8734 * (6 : ZMod 18317784469) ^ 8734) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 12235375375 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 18317784469) ^ 34938 = 14331975753 := by
        calc
          (6 : ZMod 18317784469) ^ 34938 = (6 : ZMod 18317784469) ^ (17469 + 17469) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 17469 * (6 : ZMod 18317784469) ^ 17469 := by rw [pow_add]
          _ = 14331975753 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 18317784469) ^ 69876 = 17447740061 := by
        calc
          (6 : ZMod 18317784469) ^ 69876 = (6 : ZMod 18317784469) ^ (34938 + 34938) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 34938 * (6 : ZMod 18317784469) ^ 34938 := by rw [pow_add]
          _ = 17447740061 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 18317784469) ^ 139753 = 2590763270 := by
        calc
          (6 : ZMod 18317784469) ^ 139753 = (6 : ZMod 18317784469) ^ (69876 + 69876 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 69876 * (6 : ZMod 18317784469) ^ 69876) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 2590763270 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 18317784469) ^ 279507 = 3125065726 := by
        calc
          (6 : ZMod 18317784469) ^ 279507 = (6 : ZMod 18317784469) ^ (139753 + 139753 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 139753 * (6 : ZMod 18317784469) ^ 139753) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 3125065726 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 18317784469) ^ 559014 = 4925799068 := by
        calc
          (6 : ZMod 18317784469) ^ 559014 = (6 : ZMod 18317784469) ^ (279507 + 279507) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 279507 * (6 : ZMod 18317784469) ^ 279507 := by rw [pow_add]
          _ = 4925799068 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 18317784469) ^ 1118028 = 11220251505 := by
        calc
          (6 : ZMod 18317784469) ^ 1118028 = (6 : ZMod 18317784469) ^ (559014 + 559014) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 559014 * (6 : ZMod 18317784469) ^ 559014 := by rw [pow_add]
          _ = 11220251505 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 18317784469) ^ 2236057 = 15574783974 := by
        calc
          (6 : ZMod 18317784469) ^ 2236057 = (6 : ZMod 18317784469) ^ (1118028 + 1118028 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 1118028 * (6 : ZMod 18317784469) ^ 1118028) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 15574783974 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 18317784469) ^ 4472115 = 10309981932 := by
        calc
          (6 : ZMod 18317784469) ^ 4472115 = (6 : ZMod 18317784469) ^ (2236057 + 2236057 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2236057 * (6 : ZMod 18317784469) ^ 2236057) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 10309981932 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 18317784469) ^ 8944230 = 17840650862 := by
        calc
          (6 : ZMod 18317784469) ^ 8944230 = (6 : ZMod 18317784469) ^ (4472115 + 4472115) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4472115 * (6 : ZMod 18317784469) ^ 4472115 := by rw [pow_add]
          _ = 17840650862 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 18317784469) ^ 17888461 = 3504121694 := by
        calc
          (6 : ZMod 18317784469) ^ 17888461 = (6 : ZMod 18317784469) ^ (8944230 + 8944230 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 8944230 * (6 : ZMod 18317784469) ^ 8944230) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 3504121694 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 18317784469) ^ 35776922 = 8814573574 := by
        calc
          (6 : ZMod 18317784469) ^ 35776922 = (6 : ZMod 18317784469) ^ (17888461 + 17888461) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 17888461 * (6 : ZMod 18317784469) ^ 17888461 := by rw [pow_add]
          _ = 8814573574 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 18317784469) ^ 71553845 = 15903988580 := by
        calc
          (6 : ZMod 18317784469) ^ 71553845 = (6 : ZMod 18317784469) ^ (35776922 + 35776922 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 35776922 * (6 : ZMod 18317784469) ^ 35776922) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 15903988580 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 18317784469) ^ 143107691 = 7404409020 := by
        calc
          (6 : ZMod 18317784469) ^ 143107691 = (6 : ZMod 18317784469) ^ (71553845 + 71553845 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 71553845 * (6 : ZMod 18317784469) ^ 71553845) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 7404409020 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 18317784469) ^ 286215382 = 5318865122 := by
        calc
          (6 : ZMod 18317784469) ^ 286215382 = (6 : ZMod 18317784469) ^ (143107691 + 143107691) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 143107691 * (6 : ZMod 18317784469) ^ 143107691 := by rw [pow_add]
          _ = 5318865122 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 18317784469) ^ 572430764 = 2249221527 := by
        calc
          (6 : ZMod 18317784469) ^ 572430764 = (6 : ZMod 18317784469) ^ (286215382 + 286215382) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 286215382 * (6 : ZMod 18317784469) ^ 286215382 := by rw [pow_add]
          _ = 2249221527 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 18317784469) ^ 1144861529 = 16931032205 := by
        calc
          (6 : ZMod 18317784469) ^ 1144861529 = (6 : ZMod 18317784469) ^ (572430764 + 572430764 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 572430764 * (6 : ZMod 18317784469) ^ 572430764) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 16931032205 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 18317784469) ^ 2289723058 = 10088428468 := by
        calc
          (6 : ZMod 18317784469) ^ 2289723058 = (6 : ZMod 18317784469) ^ (1144861529 + 1144861529) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 1144861529 * (6 : ZMod 18317784469) ^ 1144861529 := by rw [pow_add]
          _ = 10088428468 := by rw [fermat_30]; decide
      have fermat_32 : (6 : ZMod 18317784469) ^ 4579446117 = 15843414624 := by
        calc
          (6 : ZMod 18317784469) ^ 4579446117 = (6 : ZMod 18317784469) ^ (2289723058 + 2289723058 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2289723058 * (6 : ZMod 18317784469) ^ 2289723058) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 15843414624 := by rw [fermat_31]; decide
      have fermat_33 : (6 : ZMod 18317784469) ^ 9158892234 = 18317784468 := by
        calc
          (6 : ZMod 18317784469) ^ 9158892234 = (6 : ZMod 18317784469) ^ (4579446117 + 4579446117) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4579446117 * (6 : ZMod 18317784469) ^ 4579446117 := by rw [pow_add]
          _ = 18317784468 := by rw [fermat_32]; decide
      have fermat_34 : (6 : ZMod 18317784469) ^ 18317784468 = 1 := by
        calc
          (6 : ZMod 18317784469) ^ 18317784468 = (6 : ZMod 18317784469) ^ (9158892234 + 9158892234) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 9158892234 * (6 : ZMod 18317784469) ^ 9158892234 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1526482039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1526482039, 1)] : List FactorBlock).map factorBlockValue).prod = 18317784469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1526482039) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 18317784469) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 18317784469) ^ 2 = 36 := by
        calc
          (6 : ZMod 18317784469) ^ 2 = (6 : ZMod 18317784469) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 1 * (6 : ZMod 18317784469) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 18317784469) ^ 4 = 1296 := by
        calc
          (6 : ZMod 18317784469) ^ 4 = (6 : ZMod 18317784469) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 2 * (6 : ZMod 18317784469) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 18317784469) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 18317784469) ^ 8 = (6 : ZMod 18317784469) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4 * (6 : ZMod 18317784469) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 18317784469) ^ 17 = 1026595380 := by
        calc
          (6 : ZMod 18317784469) ^ 17 = (6 : ZMod 18317784469) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 8 * (6 : ZMod 18317784469) ^ 8) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 1026595380 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 18317784469) ^ 34 = 6519150395 := by
        calc
          (6 : ZMod 18317784469) ^ 34 = (6 : ZMod 18317784469) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 17 * (6 : ZMod 18317784469) ^ 17 := by rw [pow_add]
          _ = 6519150395 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 18317784469) ^ 68 = 18093256447 := by
        calc
          (6 : ZMod 18317784469) ^ 68 = (6 : ZMod 18317784469) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 34 * (6 : ZMod 18317784469) ^ 34 := by rw [pow_add]
          _ = 18093256447 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 18317784469) ^ 136 = 81485859 := by
        calc
          (6 : ZMod 18317784469) ^ 136 = (6 : ZMod 18317784469) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 68 * (6 : ZMod 18317784469) ^ 68 := by rw [pow_add]
          _ = 81485859 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 18317784469) ^ 272 = 4795937947 := by
        calc
          (6 : ZMod 18317784469) ^ 272 = (6 : ZMod 18317784469) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 136 * (6 : ZMod 18317784469) ^ 136 := by rw [pow_add]
          _ = 4795937947 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 18317784469) ^ 545 = 12206849470 := by
        calc
          (6 : ZMod 18317784469) ^ 545 = (6 : ZMod 18317784469) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 272 * (6 : ZMod 18317784469) ^ 272) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 12206849470 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 18317784469) ^ 1091 = 9618585720 := by
        calc
          (6 : ZMod 18317784469) ^ 1091 = (6 : ZMod 18317784469) ^ (545 + 545 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 545 * (6 : ZMod 18317784469) ^ 545) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 9618585720 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 18317784469) ^ 2183 = 4103680532 := by
        calc
          (6 : ZMod 18317784469) ^ 2183 = (6 : ZMod 18317784469) ^ (1091 + 1091 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 1091 * (6 : ZMod 18317784469) ^ 1091) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 4103680532 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 18317784469) ^ 4367 = 13978714943 := by
        calc
          (6 : ZMod 18317784469) ^ 4367 = (6 : ZMod 18317784469) ^ (2183 + 2183 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2183 * (6 : ZMod 18317784469) ^ 2183) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 13978714943 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 18317784469) ^ 8734 = 13279027090 := by
        calc
          (6 : ZMod 18317784469) ^ 8734 = (6 : ZMod 18317784469) ^ (4367 + 4367) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4367 * (6 : ZMod 18317784469) ^ 4367 := by rw [pow_add]
          _ = 13279027090 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 18317784469) ^ 17469 = 12235375375 := by
        calc
          (6 : ZMod 18317784469) ^ 17469 = (6 : ZMod 18317784469) ^ (8734 + 8734 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 8734 * (6 : ZMod 18317784469) ^ 8734) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 12235375375 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 18317784469) ^ 34938 = 14331975753 := by
        calc
          (6 : ZMod 18317784469) ^ 34938 = (6 : ZMod 18317784469) ^ (17469 + 17469) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 17469 * (6 : ZMod 18317784469) ^ 17469 := by rw [pow_add]
          _ = 14331975753 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 18317784469) ^ 69876 = 17447740061 := by
        calc
          (6 : ZMod 18317784469) ^ 69876 = (6 : ZMod 18317784469) ^ (34938 + 34938) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 34938 * (6 : ZMod 18317784469) ^ 34938 := by rw [pow_add]
          _ = 17447740061 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 18317784469) ^ 139753 = 2590763270 := by
        calc
          (6 : ZMod 18317784469) ^ 139753 = (6 : ZMod 18317784469) ^ (69876 + 69876 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 69876 * (6 : ZMod 18317784469) ^ 69876) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 2590763270 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 18317784469) ^ 279507 = 3125065726 := by
        calc
          (6 : ZMod 18317784469) ^ 279507 = (6 : ZMod 18317784469) ^ (139753 + 139753 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 139753 * (6 : ZMod 18317784469) ^ 139753) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 3125065726 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 18317784469) ^ 559014 = 4925799068 := by
        calc
          (6 : ZMod 18317784469) ^ 559014 = (6 : ZMod 18317784469) ^ (279507 + 279507) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 279507 * (6 : ZMod 18317784469) ^ 279507 := by rw [pow_add]
          _ = 4925799068 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 18317784469) ^ 1118028 = 11220251505 := by
        calc
          (6 : ZMod 18317784469) ^ 1118028 = (6 : ZMod 18317784469) ^ (559014 + 559014) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 559014 * (6 : ZMod 18317784469) ^ 559014 := by rw [pow_add]
          _ = 11220251505 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 18317784469) ^ 2236057 = 15574783974 := by
        calc
          (6 : ZMod 18317784469) ^ 2236057 = (6 : ZMod 18317784469) ^ (1118028 + 1118028 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 1118028 * (6 : ZMod 18317784469) ^ 1118028) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 15574783974 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 18317784469) ^ 4472115 = 10309981932 := by
        calc
          (6 : ZMod 18317784469) ^ 4472115 = (6 : ZMod 18317784469) ^ (2236057 + 2236057 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2236057 * (6 : ZMod 18317784469) ^ 2236057) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 10309981932 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 18317784469) ^ 8944230 = 17840650862 := by
        calc
          (6 : ZMod 18317784469) ^ 8944230 = (6 : ZMod 18317784469) ^ (4472115 + 4472115) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4472115 * (6 : ZMod 18317784469) ^ 4472115 := by rw [pow_add]
          _ = 17840650862 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 18317784469) ^ 17888461 = 3504121694 := by
        calc
          (6 : ZMod 18317784469) ^ 17888461 = (6 : ZMod 18317784469) ^ (8944230 + 8944230 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 8944230 * (6 : ZMod 18317784469) ^ 8944230) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 3504121694 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 18317784469) ^ 35776922 = 8814573574 := by
        calc
          (6 : ZMod 18317784469) ^ 35776922 = (6 : ZMod 18317784469) ^ (17888461 + 17888461) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 17888461 * (6 : ZMod 18317784469) ^ 17888461 := by rw [pow_add]
          _ = 8814573574 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 18317784469) ^ 71553845 = 15903988580 := by
        calc
          (6 : ZMod 18317784469) ^ 71553845 = (6 : ZMod 18317784469) ^ (35776922 + 35776922 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 35776922 * (6 : ZMod 18317784469) ^ 35776922) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 15903988580 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 18317784469) ^ 143107691 = 7404409020 := by
        calc
          (6 : ZMod 18317784469) ^ 143107691 = (6 : ZMod 18317784469) ^ (71553845 + 71553845 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 71553845 * (6 : ZMod 18317784469) ^ 71553845) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 7404409020 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 18317784469) ^ 286215382 = 5318865122 := by
        calc
          (6 : ZMod 18317784469) ^ 286215382 = (6 : ZMod 18317784469) ^ (143107691 + 143107691) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 143107691 * (6 : ZMod 18317784469) ^ 143107691 := by rw [pow_add]
          _ = 5318865122 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 18317784469) ^ 572430764 = 2249221527 := by
        calc
          (6 : ZMod 18317784469) ^ 572430764 = (6 : ZMod 18317784469) ^ (286215382 + 286215382) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 286215382 * (6 : ZMod 18317784469) ^ 286215382 := by rw [pow_add]
          _ = 2249221527 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 18317784469) ^ 1144861529 = 16931032205 := by
        calc
          (6 : ZMod 18317784469) ^ 1144861529 = (6 : ZMod 18317784469) ^ (572430764 + 572430764 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 572430764 * (6 : ZMod 18317784469) ^ 572430764) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 16931032205 := by rw [factor_0_29]; decide
      have factor_0_31 : (6 : ZMod 18317784469) ^ 2289723058 = 10088428468 := by
        calc
          (6 : ZMod 18317784469) ^ 2289723058 = (6 : ZMod 18317784469) ^ (1144861529 + 1144861529) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 1144861529 * (6 : ZMod 18317784469) ^ 1144861529 := by rw [pow_add]
          _ = 10088428468 := by rw [factor_0_30]; decide
      have factor_0_32 : (6 : ZMod 18317784469) ^ 4579446117 = 15843414624 := by
        calc
          (6 : ZMod 18317784469) ^ 4579446117 = (6 : ZMod 18317784469) ^ (2289723058 + 2289723058 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2289723058 * (6 : ZMod 18317784469) ^ 2289723058) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 15843414624 := by rw [factor_0_31]; decide
      have factor_0_33 : (6 : ZMod 18317784469) ^ 9158892234 = 18317784468 := by
        calc
          (6 : ZMod 18317784469) ^ 9158892234 = (6 : ZMod 18317784469) ^ (4579446117 + 4579446117) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 4579446117 * (6 : ZMod 18317784469) ^ 4579446117 := by rw [pow_add]
          _ = 18317784468 := by rw [factor_0_32]; decide
      change (6 : ZMod 18317784469) ^ 9158892234 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (6 : ZMod 18317784469) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 18317784469) ^ 2 = 36 := by
        calc
          (6 : ZMod 18317784469) ^ 2 = (6 : ZMod 18317784469) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 1 * (6 : ZMod 18317784469) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 18317784469) ^ 5 = 7776 := by
        calc
          (6 : ZMod 18317784469) ^ 5 = (6 : ZMod 18317784469) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2 * (6 : ZMod 18317784469) ^ 2) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 18317784469) ^ 11 = 362797056 := by
        calc
          (6 : ZMod 18317784469) ^ 11 = (6 : ZMod 18317784469) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 5 * (6 : ZMod 18317784469) ^ 5) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 362797056 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 18317784469) ^ 22 = 14569430865 := by
        calc
          (6 : ZMod 18317784469) ^ 22 = (6 : ZMod 18317784469) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 11 * (6 : ZMod 18317784469) ^ 11 := by rw [pow_add]
          _ = 14569430865 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 18317784469) ^ 45 = 4497693709 := by
        calc
          (6 : ZMod 18317784469) ^ 45 = (6 : ZMod 18317784469) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 22 * (6 : ZMod 18317784469) ^ 22) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 4497693709 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 18317784469) ^ 90 = 14530115447 := by
        calc
          (6 : ZMod 18317784469) ^ 90 = (6 : ZMod 18317784469) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 45 * (6 : ZMod 18317784469) ^ 45 := by rw [pow_add]
          _ = 14530115447 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 18317784469) ^ 181 = 13840178583 := by
        calc
          (6 : ZMod 18317784469) ^ 181 = (6 : ZMod 18317784469) ^ (90 + 90 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 90 * (6 : ZMod 18317784469) ^ 90) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 13840178583 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 18317784469) ^ 363 = 7267060126 := by
        calc
          (6 : ZMod 18317784469) ^ 363 = (6 : ZMod 18317784469) ^ (181 + 181 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 181 * (6 : ZMod 18317784469) ^ 181) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 7267060126 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 18317784469) ^ 727 = 11636409242 := by
        calc
          (6 : ZMod 18317784469) ^ 727 = (6 : ZMod 18317784469) ^ (363 + 363 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 363 * (6 : ZMod 18317784469) ^ 363) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 11636409242 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 18317784469) ^ 1455 = 10045401372 := by
        calc
          (6 : ZMod 18317784469) ^ 1455 = (6 : ZMod 18317784469) ^ (727 + 727 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 727 * (6 : ZMod 18317784469) ^ 727) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 10045401372 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 18317784469) ^ 2911 = 2316257746 := by
        calc
          (6 : ZMod 18317784469) ^ 2911 = (6 : ZMod 18317784469) ^ (1455 + 1455 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 1455 * (6 : ZMod 18317784469) ^ 1455) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 2316257746 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 18317784469) ^ 5823 = 17651586015 := by
        calc
          (6 : ZMod 18317784469) ^ 5823 = (6 : ZMod 18317784469) ^ (2911 + 2911 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 2911 * (6 : ZMod 18317784469) ^ 2911) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 17651586015 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 18317784469) ^ 11646 = 7504148539 := by
        calc
          (6 : ZMod 18317784469) ^ 11646 = (6 : ZMod 18317784469) ^ (5823 + 5823) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 5823 * (6 : ZMod 18317784469) ^ 5823 := by rw [pow_add]
          _ = 7504148539 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 18317784469) ^ 23292 = 16534473573 := by
        calc
          (6 : ZMod 18317784469) ^ 23292 = (6 : ZMod 18317784469) ^ (11646 + 11646) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 11646 * (6 : ZMod 18317784469) ^ 11646 := by rw [pow_add]
          _ = 16534473573 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 18317784469) ^ 46584 = 3516440672 := by
        calc
          (6 : ZMod 18317784469) ^ 46584 = (6 : ZMod 18317784469) ^ (23292 + 23292) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 23292 * (6 : ZMod 18317784469) ^ 23292 := by rw [pow_add]
          _ = 3516440672 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 18317784469) ^ 93169 = 3598633360 := by
        calc
          (6 : ZMod 18317784469) ^ 93169 = (6 : ZMod 18317784469) ^ (46584 + 46584 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 46584 * (6 : ZMod 18317784469) ^ 46584) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 3598633360 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 18317784469) ^ 186338 = 888755363 := by
        calc
          (6 : ZMod 18317784469) ^ 186338 = (6 : ZMod 18317784469) ^ (93169 + 93169) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 93169 * (6 : ZMod 18317784469) ^ 93169 := by rw [pow_add]
          _ = 888755363 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 18317784469) ^ 372676 = 2007275077 := by
        calc
          (6 : ZMod 18317784469) ^ 372676 = (6 : ZMod 18317784469) ^ (186338 + 186338) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 186338 * (6 : ZMod 18317784469) ^ 186338 := by rw [pow_add]
          _ = 2007275077 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 18317784469) ^ 745352 = 15320518324 := by
        calc
          (6 : ZMod 18317784469) ^ 745352 = (6 : ZMod 18317784469) ^ (372676 + 372676) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 372676 * (6 : ZMod 18317784469) ^ 372676 := by rw [pow_add]
          _ = 15320518324 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 18317784469) ^ 1490705 = 12084230248 := by
        calc
          (6 : ZMod 18317784469) ^ 1490705 = (6 : ZMod 18317784469) ^ (745352 + 745352 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 745352 * (6 : ZMod 18317784469) ^ 745352) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 12084230248 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 18317784469) ^ 2981410 = 10477814212 := by
        calc
          (6 : ZMod 18317784469) ^ 2981410 = (6 : ZMod 18317784469) ^ (1490705 + 1490705) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 1490705 * (6 : ZMod 18317784469) ^ 1490705 := by rw [pow_add]
          _ = 10477814212 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 18317784469) ^ 5962820 = 16792010328 := by
        calc
          (6 : ZMod 18317784469) ^ 5962820 = (6 : ZMod 18317784469) ^ (2981410 + 2981410) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 2981410 * (6 : ZMod 18317784469) ^ 2981410 := by rw [pow_add]
          _ = 16792010328 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 18317784469) ^ 11925640 = 17097683161 := by
        calc
          (6 : ZMod 18317784469) ^ 11925640 = (6 : ZMod 18317784469) ^ (5962820 + 5962820) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 5962820 * (6 : ZMod 18317784469) ^ 5962820 := by rw [pow_add]
          _ = 17097683161 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 18317784469) ^ 23851281 = 240762233 := by
        calc
          (6 : ZMod 18317784469) ^ 23851281 = (6 : ZMod 18317784469) ^ (11925640 + 11925640 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 11925640 * (6 : ZMod 18317784469) ^ 11925640) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 240762233 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 18317784469) ^ 47702563 = 5753473936 := by
        calc
          (6 : ZMod 18317784469) ^ 47702563 = (6 : ZMod 18317784469) ^ (23851281 + 23851281 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 23851281 * (6 : ZMod 18317784469) ^ 23851281) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 5753473936 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 18317784469) ^ 95405127 = 16545023436 := by
        calc
          (6 : ZMod 18317784469) ^ 95405127 = (6 : ZMod 18317784469) ^ (47702563 + 47702563 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 47702563 * (6 : ZMod 18317784469) ^ 47702563) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 16545023436 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 18317784469) ^ 190810254 = 49200837 := by
        calc
          (6 : ZMod 18317784469) ^ 190810254 = (6 : ZMod 18317784469) ^ (95405127 + 95405127) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 95405127 * (6 : ZMod 18317784469) ^ 95405127 := by rw [pow_add]
          _ = 49200837 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 18317784469) ^ 381620509 = 16321257562 := by
        calc
          (6 : ZMod 18317784469) ^ 381620509 = (6 : ZMod 18317784469) ^ (190810254 + 190810254 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 190810254 * (6 : ZMod 18317784469) ^ 190810254) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 16321257562 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 18317784469) ^ 763241019 = 14258060928 := by
        calc
          (6 : ZMod 18317784469) ^ 763241019 = (6 : ZMod 18317784469) ^ (381620509 + 381620509 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 381620509 * (6 : ZMod 18317784469) ^ 381620509) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 14258060928 := by rw [factor_1_28]; decide
      have factor_1_30 : (6 : ZMod 18317784469) ^ 1526482039 = 6824012616 := by
        calc
          (6 : ZMod 18317784469) ^ 1526482039 = (6 : ZMod 18317784469) ^ (763241019 + 763241019 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 763241019 * (6 : ZMod 18317784469) ^ 763241019) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 6824012616 := by rw [factor_1_29]; decide
      have factor_1_31 : (6 : ZMod 18317784469) ^ 3052964078 = 16626870465 := by
        calc
          (6 : ZMod 18317784469) ^ 3052964078 = (6 : ZMod 18317784469) ^ (1526482039 + 1526482039) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 1526482039 * (6 : ZMod 18317784469) ^ 1526482039 := by rw [pow_add]
          _ = 16626870465 := by rw [factor_1_30]; decide
      have factor_1_32 : (6 : ZMod 18317784469) ^ 6105928156 = 16626870464 := by
        calc
          (6 : ZMod 18317784469) ^ 6105928156 = (6 : ZMod 18317784469) ^ (3052964078 + 3052964078) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 3052964078 * (6 : ZMod 18317784469) ^ 3052964078 := by rw [pow_add]
          _ = 16626870464 := by rw [factor_1_31]; decide
      change (6 : ZMod 18317784469) ^ 6105928156 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (6 : ZMod 18317784469) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 18317784469) ^ 3 = 216 := by
        calc
          (6 : ZMod 18317784469) ^ 3 = (6 : ZMod 18317784469) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = ((6 : ZMod 18317784469) ^ 1 * (6 : ZMod 18317784469) ^ 1) * (6 : ZMod 18317784469) := by rw [pow_succ, pow_add]
          _ = 216 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 18317784469) ^ 6 = 46656 := by
        calc
          (6 : ZMod 18317784469) ^ 6 = (6 : ZMod 18317784469) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 3 * (6 : ZMod 18317784469) ^ 3 := by rw [pow_add]
          _ = 46656 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 18317784469) ^ 12 = 2176782336 := by
        calc
          (6 : ZMod 18317784469) ^ 12 = (6 : ZMod 18317784469) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (6 : ZMod 18317784469) ^ n) (by norm_num)
          _ = (6 : ZMod 18317784469) ^ 6 * (6 : ZMod 18317784469) ^ 6 := by rw [pow_add]
          _ = 2176782336 := by rw [factor_2_2]; decide
      change (6 : ZMod 18317784469) ^ 12 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_18317784469

end TotientTailPeriodKiller
end Erdos249257
