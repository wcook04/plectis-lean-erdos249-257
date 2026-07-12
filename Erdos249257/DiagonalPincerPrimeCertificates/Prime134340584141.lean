import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime50503979

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_134340584141 : Nat.Prime 134340584141 := by
  apply lucas_primality 134340584141 (3 : ZMod 134340584141)
  ·
      have fermat_0 : (3 : ZMod 134340584141) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 134340584141) ^ 3 = 27 := by
        calc
          (3 : ZMod 134340584141) ^ 3 = (3 : ZMod 134340584141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1 * (3 : ZMod 134340584141) ^ 1) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 134340584141) ^ 7 = 2187 := by
        calc
          (3 : ZMod 134340584141) ^ 7 = (3 : ZMod 134340584141) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 3 * (3 : ZMod 134340584141) ^ 3) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 134340584141) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 134340584141) ^ 15 = (3 : ZMod 134340584141) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 7 * (3 : ZMod 134340584141) ^ 7) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 134340584141) ^ 31 = 109730987770 := by
        calc
          (3 : ZMod 134340584141) ^ 31 = (3 : ZMod 134340584141) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 15 * (3 : ZMod 134340584141) ^ 15) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 109730987770 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 134340584141) ^ 62 = 91044288159 := by
        calc
          (3 : ZMod 134340584141) ^ 62 = (3 : ZMod 134340584141) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 31 * (3 : ZMod 134340584141) ^ 31 := by rw [pow_add]
          _ = 91044288159 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 134340584141) ^ 125 = 112755758133 := by
        calc
          (3 : ZMod 134340584141) ^ 125 = (3 : ZMod 134340584141) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 62 * (3 : ZMod 134340584141) ^ 62) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 112755758133 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 134340584141) ^ 250 = 61285418695 := by
        calc
          (3 : ZMod 134340584141) ^ 250 = (3 : ZMod 134340584141) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 125 * (3 : ZMod 134340584141) ^ 125 := by rw [pow_add]
          _ = 61285418695 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 134340584141) ^ 500 = 61307524864 := by
        calc
          (3 : ZMod 134340584141) ^ 500 = (3 : ZMod 134340584141) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 250 * (3 : ZMod 134340584141) ^ 250 := by rw [pow_add]
          _ = 61307524864 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 134340584141) ^ 1000 = 128540551298 := by
        calc
          (3 : ZMod 134340584141) ^ 1000 = (3 : ZMod 134340584141) ^ (500 + 500) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 500 * (3 : ZMod 134340584141) ^ 500 := by rw [pow_add]
          _ = 128540551298 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 134340584141) ^ 2001 = 22246756959 := by
        calc
          (3 : ZMod 134340584141) ^ 2001 = (3 : ZMod 134340584141) ^ (1000 + 1000 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1000 * (3 : ZMod 134340584141) ^ 1000) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 22246756959 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 134340584141) ^ 4003 = 131437564674 := by
        calc
          (3 : ZMod 134340584141) ^ 4003 = (3 : ZMod 134340584141) ^ (2001 + 2001 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2001 * (3 : ZMod 134340584141) ^ 2001) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 131437564674 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 134340584141) ^ 8007 = 97590104678 := by
        calc
          (3 : ZMod 134340584141) ^ 8007 = (3 : ZMod 134340584141) ^ (4003 + 4003 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 4003 * (3 : ZMod 134340584141) ^ 4003) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 97590104678 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 134340584141) ^ 16014 = 91020310467 := by
        calc
          (3 : ZMod 134340584141) ^ 16014 = (3 : ZMod 134340584141) ^ (8007 + 8007) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 8007 * (3 : ZMod 134340584141) ^ 8007 := by rw [pow_add]
          _ = 91020310467 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 134340584141) ^ 32029 = 74362157902 := by
        calc
          (3 : ZMod 134340584141) ^ 32029 = (3 : ZMod 134340584141) ^ (16014 + 16014 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 16014 * (3 : ZMod 134340584141) ^ 16014) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 74362157902 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 134340584141) ^ 64058 = 45780413510 := by
        calc
          (3 : ZMod 134340584141) ^ 64058 = (3 : ZMod 134340584141) ^ (32029 + 32029) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 32029 * (3 : ZMod 134340584141) ^ 32029 := by rw [pow_add]
          _ = 45780413510 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 134340584141) ^ 128117 = 34898393720 := by
        calc
          (3 : ZMod 134340584141) ^ 128117 = (3 : ZMod 134340584141) ^ (64058 + 64058 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 64058 * (3 : ZMod 134340584141) ^ 64058) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 34898393720 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 134340584141) ^ 256234 = 91583624144 := by
        calc
          (3 : ZMod 134340584141) ^ 256234 = (3 : ZMod 134340584141) ^ (128117 + 128117) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 128117 * (3 : ZMod 134340584141) ^ 128117 := by rw [pow_add]
          _ = 91583624144 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 134340584141) ^ 512468 = 49229202761 := by
        calc
          (3 : ZMod 134340584141) ^ 512468 = (3 : ZMod 134340584141) ^ (256234 + 256234) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 256234 * (3 : ZMod 134340584141) ^ 256234 := by rw [pow_add]
          _ = 49229202761 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 134340584141) ^ 1024937 = 11666398857 := by
        calc
          (3 : ZMod 134340584141) ^ 1024937 = (3 : ZMod 134340584141) ^ (512468 + 512468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 512468 * (3 : ZMod 134340584141) ^ 512468) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 11666398857 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 134340584141) ^ 2049874 = 50660171074 := by
        calc
          (3 : ZMod 134340584141) ^ 2049874 = (3 : ZMod 134340584141) ^ (1024937 + 1024937) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1024937 * (3 : ZMod 134340584141) ^ 1024937 := by rw [pow_add]
          _ = 50660171074 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 134340584141) ^ 4099749 = 11642614314 := by
        calc
          (3 : ZMod 134340584141) ^ 4099749 = (3 : ZMod 134340584141) ^ (2049874 + 2049874 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2049874 * (3 : ZMod 134340584141) ^ 2049874) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 11642614314 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 134340584141) ^ 8199498 = 129109519483 := by
        calc
          (3 : ZMod 134340584141) ^ 8199498 = (3 : ZMod 134340584141) ^ (4099749 + 4099749) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 4099749 * (3 : ZMod 134340584141) ^ 4099749 := by rw [pow_add]
          _ = 129109519483 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 134340584141) ^ 16398997 = 99150091060 := by
        calc
          (3 : ZMod 134340584141) ^ 16398997 = (3 : ZMod 134340584141) ^ (8199498 + 8199498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 8199498 * (3 : ZMod 134340584141) ^ 8199498) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 99150091060 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 134340584141) ^ 32797994 = 109896681347 := by
        calc
          (3 : ZMod 134340584141) ^ 32797994 = (3 : ZMod 134340584141) ^ (16398997 + 16398997) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 16398997 * (3 : ZMod 134340584141) ^ 16398997 := by rw [pow_add]
          _ = 109896681347 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 134340584141) ^ 65595988 = 56081977433 := by
        calc
          (3 : ZMod 134340584141) ^ 65595988 = (3 : ZMod 134340584141) ^ (32797994 + 32797994) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 32797994 * (3 : ZMod 134340584141) ^ 32797994 := by rw [pow_add]
          _ = 56081977433 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 134340584141) ^ 131191976 = 91680737615 := by
        calc
          (3 : ZMod 134340584141) ^ 131191976 = (3 : ZMod 134340584141) ^ (65595988 + 65595988) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 65595988 * (3 : ZMod 134340584141) ^ 65595988 := by rw [pow_add]
          _ = 91680737615 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 134340584141) ^ 262383953 = 81106825941 := by
        calc
          (3 : ZMod 134340584141) ^ 262383953 = (3 : ZMod 134340584141) ^ (131191976 + 131191976 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 131191976 * (3 : ZMod 134340584141) ^ 131191976) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 81106825941 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 134340584141) ^ 524767906 = 68791471949 := by
        calc
          (3 : ZMod 134340584141) ^ 524767906 = (3 : ZMod 134340584141) ^ (262383953 + 262383953) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 262383953 * (3 : ZMod 134340584141) ^ 262383953 := by rw [pow_add]
          _ = 68791471949 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 134340584141) ^ 1049535813 = 68637085557 := by
        calc
          (3 : ZMod 134340584141) ^ 1049535813 = (3 : ZMod 134340584141) ^ (524767906 + 524767906 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 524767906 * (3 : ZMod 134340584141) ^ 524767906) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 68637085557 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 134340584141) ^ 2099071627 = 44623691285 := by
        calc
          (3 : ZMod 134340584141) ^ 2099071627 = (3 : ZMod 134340584141) ^ (1049535813 + 1049535813 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1049535813 * (3 : ZMod 134340584141) ^ 1049535813) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 44623691285 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 134340584141) ^ 4198143254 = 94129398591 := by
        calc
          (3 : ZMod 134340584141) ^ 4198143254 = (3 : ZMod 134340584141) ^ (2099071627 + 2099071627) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 2099071627 * (3 : ZMod 134340584141) ^ 2099071627 := by rw [pow_add]
          _ = 94129398591 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 134340584141) ^ 8396286508 = 24230988215 := by
        calc
          (3 : ZMod 134340584141) ^ 8396286508 = (3 : ZMod 134340584141) ^ (4198143254 + 4198143254) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 4198143254 * (3 : ZMod 134340584141) ^ 4198143254 := by rw [pow_add]
          _ = 24230988215 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 134340584141) ^ 16792573017 = 59540830819 := by
        calc
          (3 : ZMod 134340584141) ^ 16792573017 = (3 : ZMod 134340584141) ^ (8396286508 + 8396286508 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 8396286508 * (3 : ZMod 134340584141) ^ 8396286508) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 59540830819 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 134340584141) ^ 33585146035 = 61937688190 := by
        calc
          (3 : ZMod 134340584141) ^ 33585146035 = (3 : ZMod 134340584141) ^ (16792573017 + 16792573017 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 16792573017 * (3 : ZMod 134340584141) ^ 16792573017) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 61937688190 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 134340584141) ^ 67170292070 = 134340584140 := by
        calc
          (3 : ZMod 134340584141) ^ 67170292070 = (3 : ZMod 134340584141) ^ (33585146035 + 33585146035) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 33585146035 * (3 : ZMod 134340584141) ^ 33585146035 := by rw [pow_add]
          _ = 134340584140 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 134340584141) ^ 134340584140 = 1 := by
        calc
          (3 : ZMod 134340584141) ^ 134340584140 = (3 : ZMod 134340584141) ^ (67170292070 + 67170292070) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 67170292070 * (3 : ZMod 134340584141) ^ 67170292070 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (19, 1), (50503979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (19, 1), (50503979, 1)] : List FactorBlock).map factorBlockValue).prod = 134340584141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_50503979) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 134340584141) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 134340584141) ^ 3 = 27 := by
        calc
          (3 : ZMod 134340584141) ^ 3 = (3 : ZMod 134340584141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1 * (3 : ZMod 134340584141) ^ 1) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 134340584141) ^ 7 = 2187 := by
        calc
          (3 : ZMod 134340584141) ^ 7 = (3 : ZMod 134340584141) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 3 * (3 : ZMod 134340584141) ^ 3) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 134340584141) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 134340584141) ^ 15 = (3 : ZMod 134340584141) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 7 * (3 : ZMod 134340584141) ^ 7) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 134340584141) ^ 31 = 109730987770 := by
        calc
          (3 : ZMod 134340584141) ^ 31 = (3 : ZMod 134340584141) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 15 * (3 : ZMod 134340584141) ^ 15) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 109730987770 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 134340584141) ^ 62 = 91044288159 := by
        calc
          (3 : ZMod 134340584141) ^ 62 = (3 : ZMod 134340584141) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 31 * (3 : ZMod 134340584141) ^ 31 := by rw [pow_add]
          _ = 91044288159 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 134340584141) ^ 125 = 112755758133 := by
        calc
          (3 : ZMod 134340584141) ^ 125 = (3 : ZMod 134340584141) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 62 * (3 : ZMod 134340584141) ^ 62) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 112755758133 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 134340584141) ^ 250 = 61285418695 := by
        calc
          (3 : ZMod 134340584141) ^ 250 = (3 : ZMod 134340584141) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 125 * (3 : ZMod 134340584141) ^ 125 := by rw [pow_add]
          _ = 61285418695 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 134340584141) ^ 500 = 61307524864 := by
        calc
          (3 : ZMod 134340584141) ^ 500 = (3 : ZMod 134340584141) ^ (250 + 250) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 250 * (3 : ZMod 134340584141) ^ 250 := by rw [pow_add]
          _ = 61307524864 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 134340584141) ^ 1000 = 128540551298 := by
        calc
          (3 : ZMod 134340584141) ^ 1000 = (3 : ZMod 134340584141) ^ (500 + 500) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 500 * (3 : ZMod 134340584141) ^ 500 := by rw [pow_add]
          _ = 128540551298 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 134340584141) ^ 2001 = 22246756959 := by
        calc
          (3 : ZMod 134340584141) ^ 2001 = (3 : ZMod 134340584141) ^ (1000 + 1000 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1000 * (3 : ZMod 134340584141) ^ 1000) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 22246756959 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 134340584141) ^ 4003 = 131437564674 := by
        calc
          (3 : ZMod 134340584141) ^ 4003 = (3 : ZMod 134340584141) ^ (2001 + 2001 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2001 * (3 : ZMod 134340584141) ^ 2001) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 131437564674 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 134340584141) ^ 8007 = 97590104678 := by
        calc
          (3 : ZMod 134340584141) ^ 8007 = (3 : ZMod 134340584141) ^ (4003 + 4003 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 4003 * (3 : ZMod 134340584141) ^ 4003) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 97590104678 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 134340584141) ^ 16014 = 91020310467 := by
        calc
          (3 : ZMod 134340584141) ^ 16014 = (3 : ZMod 134340584141) ^ (8007 + 8007) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 8007 * (3 : ZMod 134340584141) ^ 8007 := by rw [pow_add]
          _ = 91020310467 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 134340584141) ^ 32029 = 74362157902 := by
        calc
          (3 : ZMod 134340584141) ^ 32029 = (3 : ZMod 134340584141) ^ (16014 + 16014 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 16014 * (3 : ZMod 134340584141) ^ 16014) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 74362157902 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 134340584141) ^ 64058 = 45780413510 := by
        calc
          (3 : ZMod 134340584141) ^ 64058 = (3 : ZMod 134340584141) ^ (32029 + 32029) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 32029 * (3 : ZMod 134340584141) ^ 32029 := by rw [pow_add]
          _ = 45780413510 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 134340584141) ^ 128117 = 34898393720 := by
        calc
          (3 : ZMod 134340584141) ^ 128117 = (3 : ZMod 134340584141) ^ (64058 + 64058 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 64058 * (3 : ZMod 134340584141) ^ 64058) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 34898393720 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 134340584141) ^ 256234 = 91583624144 := by
        calc
          (3 : ZMod 134340584141) ^ 256234 = (3 : ZMod 134340584141) ^ (128117 + 128117) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 128117 * (3 : ZMod 134340584141) ^ 128117 := by rw [pow_add]
          _ = 91583624144 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 134340584141) ^ 512468 = 49229202761 := by
        calc
          (3 : ZMod 134340584141) ^ 512468 = (3 : ZMod 134340584141) ^ (256234 + 256234) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 256234 * (3 : ZMod 134340584141) ^ 256234 := by rw [pow_add]
          _ = 49229202761 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 134340584141) ^ 1024937 = 11666398857 := by
        calc
          (3 : ZMod 134340584141) ^ 1024937 = (3 : ZMod 134340584141) ^ (512468 + 512468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 512468 * (3 : ZMod 134340584141) ^ 512468) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 11666398857 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 134340584141) ^ 2049874 = 50660171074 := by
        calc
          (3 : ZMod 134340584141) ^ 2049874 = (3 : ZMod 134340584141) ^ (1024937 + 1024937) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1024937 * (3 : ZMod 134340584141) ^ 1024937 := by rw [pow_add]
          _ = 50660171074 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 134340584141) ^ 4099749 = 11642614314 := by
        calc
          (3 : ZMod 134340584141) ^ 4099749 = (3 : ZMod 134340584141) ^ (2049874 + 2049874 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2049874 * (3 : ZMod 134340584141) ^ 2049874) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 11642614314 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 134340584141) ^ 8199498 = 129109519483 := by
        calc
          (3 : ZMod 134340584141) ^ 8199498 = (3 : ZMod 134340584141) ^ (4099749 + 4099749) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 4099749 * (3 : ZMod 134340584141) ^ 4099749 := by rw [pow_add]
          _ = 129109519483 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 134340584141) ^ 16398997 = 99150091060 := by
        calc
          (3 : ZMod 134340584141) ^ 16398997 = (3 : ZMod 134340584141) ^ (8199498 + 8199498 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 8199498 * (3 : ZMod 134340584141) ^ 8199498) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 99150091060 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 134340584141) ^ 32797994 = 109896681347 := by
        calc
          (3 : ZMod 134340584141) ^ 32797994 = (3 : ZMod 134340584141) ^ (16398997 + 16398997) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 16398997 * (3 : ZMod 134340584141) ^ 16398997 := by rw [pow_add]
          _ = 109896681347 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 134340584141) ^ 65595988 = 56081977433 := by
        calc
          (3 : ZMod 134340584141) ^ 65595988 = (3 : ZMod 134340584141) ^ (32797994 + 32797994) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 32797994 * (3 : ZMod 134340584141) ^ 32797994 := by rw [pow_add]
          _ = 56081977433 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 134340584141) ^ 131191976 = 91680737615 := by
        calc
          (3 : ZMod 134340584141) ^ 131191976 = (3 : ZMod 134340584141) ^ (65595988 + 65595988) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 65595988 * (3 : ZMod 134340584141) ^ 65595988 := by rw [pow_add]
          _ = 91680737615 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 134340584141) ^ 262383953 = 81106825941 := by
        calc
          (3 : ZMod 134340584141) ^ 262383953 = (3 : ZMod 134340584141) ^ (131191976 + 131191976 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 131191976 * (3 : ZMod 134340584141) ^ 131191976) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 81106825941 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 134340584141) ^ 524767906 = 68791471949 := by
        calc
          (3 : ZMod 134340584141) ^ 524767906 = (3 : ZMod 134340584141) ^ (262383953 + 262383953) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 262383953 * (3 : ZMod 134340584141) ^ 262383953 := by rw [pow_add]
          _ = 68791471949 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 134340584141) ^ 1049535813 = 68637085557 := by
        calc
          (3 : ZMod 134340584141) ^ 1049535813 = (3 : ZMod 134340584141) ^ (524767906 + 524767906 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 524767906 * (3 : ZMod 134340584141) ^ 524767906) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 68637085557 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 134340584141) ^ 2099071627 = 44623691285 := by
        calc
          (3 : ZMod 134340584141) ^ 2099071627 = (3 : ZMod 134340584141) ^ (1049535813 + 1049535813 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1049535813 * (3 : ZMod 134340584141) ^ 1049535813) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 44623691285 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 134340584141) ^ 4198143254 = 94129398591 := by
        calc
          (3 : ZMod 134340584141) ^ 4198143254 = (3 : ZMod 134340584141) ^ (2099071627 + 2099071627) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 2099071627 * (3 : ZMod 134340584141) ^ 2099071627 := by rw [pow_add]
          _ = 94129398591 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 134340584141) ^ 8396286508 = 24230988215 := by
        calc
          (3 : ZMod 134340584141) ^ 8396286508 = (3 : ZMod 134340584141) ^ (4198143254 + 4198143254) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 4198143254 * (3 : ZMod 134340584141) ^ 4198143254 := by rw [pow_add]
          _ = 24230988215 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 134340584141) ^ 16792573017 = 59540830819 := by
        calc
          (3 : ZMod 134340584141) ^ 16792573017 = (3 : ZMod 134340584141) ^ (8396286508 + 8396286508 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 8396286508 * (3 : ZMod 134340584141) ^ 8396286508) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 59540830819 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 134340584141) ^ 33585146035 = 61937688190 := by
        calc
          (3 : ZMod 134340584141) ^ 33585146035 = (3 : ZMod 134340584141) ^ (16792573017 + 16792573017 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 16792573017 * (3 : ZMod 134340584141) ^ 16792573017) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 61937688190 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 134340584141) ^ 67170292070 = 134340584140 := by
        calc
          (3 : ZMod 134340584141) ^ 67170292070 = (3 : ZMod 134340584141) ^ (33585146035 + 33585146035) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 33585146035 * (3 : ZMod 134340584141) ^ 33585146035 := by rw [pow_add]
          _ = 134340584140 := by rw [factor_0_34]; decide
      change (3 : ZMod 134340584141) ^ 67170292070 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (3 : ZMod 134340584141) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 134340584141) ^ 3 = 27 := by
        calc
          (3 : ZMod 134340584141) ^ 3 = (3 : ZMod 134340584141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1 * (3 : ZMod 134340584141) ^ 1) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 134340584141) ^ 6 = 729 := by
        calc
          (3 : ZMod 134340584141) ^ 6 = (3 : ZMod 134340584141) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 3 * (3 : ZMod 134340584141) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 134340584141) ^ 12 = 531441 := by
        calc
          (3 : ZMod 134340584141) ^ 12 = (3 : ZMod 134340584141) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 6 * (3 : ZMod 134340584141) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 134340584141) ^ 25 = 41245104597 := by
        calc
          (3 : ZMod 134340584141) ^ 25 = (3 : ZMod 134340584141) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 12 * (3 : ZMod 134340584141) ^ 12) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 41245104597 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 134340584141) ^ 50 = 10266802013 := by
        calc
          (3 : ZMod 134340584141) ^ 50 = (3 : ZMod 134340584141) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 25 * (3 : ZMod 134340584141) ^ 25 := by rw [pow_add]
          _ = 10266802013 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 134340584141) ^ 100 = 123413768523 := by
        calc
          (3 : ZMod 134340584141) ^ 100 = (3 : ZMod 134340584141) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 50 * (3 : ZMod 134340584141) ^ 50 := by rw [pow_add]
          _ = 123413768523 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 134340584141) ^ 200 = 71437005380 := by
        calc
          (3 : ZMod 134340584141) ^ 200 = (3 : ZMod 134340584141) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 100 * (3 : ZMod 134340584141) ^ 100 := by rw [pow_add]
          _ = 71437005380 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 134340584141) ^ 400 = 52051283591 := by
        calc
          (3 : ZMod 134340584141) ^ 400 = (3 : ZMod 134340584141) ^ (200 + 200) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 200 * (3 : ZMod 134340584141) ^ 200 := by rw [pow_add]
          _ = 52051283591 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 134340584141) ^ 800 = 112480228555 := by
        calc
          (3 : ZMod 134340584141) ^ 800 = (3 : ZMod 134340584141) ^ (400 + 400) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 400 * (3 : ZMod 134340584141) ^ 400 := by rw [pow_add]
          _ = 112480228555 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 134340584141) ^ 1601 = 119656052410 := by
        calc
          (3 : ZMod 134340584141) ^ 1601 = (3 : ZMod 134340584141) ^ (800 + 800 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 800 * (3 : ZMod 134340584141) ^ 800) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 119656052410 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 134340584141) ^ 3202 = 62544288161 := by
        calc
          (3 : ZMod 134340584141) ^ 3202 = (3 : ZMod 134340584141) ^ (1601 + 1601) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1601 * (3 : ZMod 134340584141) ^ 1601 := by rw [pow_add]
          _ = 62544288161 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 134340584141) ^ 6405 = 129971224090 := by
        calc
          (3 : ZMod 134340584141) ^ 6405 = (3 : ZMod 134340584141) ^ (3202 + 3202 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 3202 * (3 : ZMod 134340584141) ^ 3202) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 129971224090 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 134340584141) ^ 12811 = 110315712578 := by
        calc
          (3 : ZMod 134340584141) ^ 12811 = (3 : ZMod 134340584141) ^ (6405 + 6405 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 6405 * (3 : ZMod 134340584141) ^ 6405) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 110315712578 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 134340584141) ^ 25623 = 26512691458 := by
        calc
          (3 : ZMod 134340584141) ^ 25623 = (3 : ZMod 134340584141) ^ (12811 + 12811 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 12811 * (3 : ZMod 134340584141) ^ 12811) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 26512691458 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 134340584141) ^ 51246 = 100715544817 := by
        calc
          (3 : ZMod 134340584141) ^ 51246 = (3 : ZMod 134340584141) ^ (25623 + 25623) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 25623 * (3 : ZMod 134340584141) ^ 25623 := by rw [pow_add]
          _ = 100715544817 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 134340584141) ^ 102493 = 34668080069 := by
        calc
          (3 : ZMod 134340584141) ^ 102493 = (3 : ZMod 134340584141) ^ (51246 + 51246 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 51246 * (3 : ZMod 134340584141) ^ 51246) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 34668080069 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 134340584141) ^ 204987 = 69081319540 := by
        calc
          (3 : ZMod 134340584141) ^ 204987 = (3 : ZMod 134340584141) ^ (102493 + 102493 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 102493 * (3 : ZMod 134340584141) ^ 102493) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 69081319540 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 134340584141) ^ 409974 = 13624646365 := by
        calc
          (3 : ZMod 134340584141) ^ 409974 = (3 : ZMod 134340584141) ^ (204987 + 204987) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 204987 * (3 : ZMod 134340584141) ^ 204987 := by rw [pow_add]
          _ = 13624646365 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 134340584141) ^ 819949 = 99316971084 := by
        calc
          (3 : ZMod 134340584141) ^ 819949 = (3 : ZMod 134340584141) ^ (409974 + 409974 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 409974 * (3 : ZMod 134340584141) ^ 409974) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 99316971084 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 134340584141) ^ 1639899 = 105303273483 := by
        calc
          (3 : ZMod 134340584141) ^ 1639899 = (3 : ZMod 134340584141) ^ (819949 + 819949 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 819949 * (3 : ZMod 134340584141) ^ 819949) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 105303273483 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 134340584141) ^ 3279799 = 61559729275 := by
        calc
          (3 : ZMod 134340584141) ^ 3279799 = (3 : ZMod 134340584141) ^ (1639899 + 1639899 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1639899 * (3 : ZMod 134340584141) ^ 1639899) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 61559729275 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 134340584141) ^ 6559598 = 3362137041 := by
        calc
          (3 : ZMod 134340584141) ^ 6559598 = (3 : ZMod 134340584141) ^ (3279799 + 3279799) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 3279799 * (3 : ZMod 134340584141) ^ 3279799 := by rw [pow_add]
          _ = 3362137041 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 134340584141) ^ 13119197 = 123344007370 := by
        calc
          (3 : ZMod 134340584141) ^ 13119197 = (3 : ZMod 134340584141) ^ (6559598 + 6559598 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 6559598 * (3 : ZMod 134340584141) ^ 6559598) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 123344007370 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 134340584141) ^ 26238395 = 47905051653 := by
        calc
          (3 : ZMod 134340584141) ^ 26238395 = (3 : ZMod 134340584141) ^ (13119197 + 13119197 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 13119197 * (3 : ZMod 134340584141) ^ 13119197) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 47905051653 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 134340584141) ^ 52476790 = 113151524958 := by
        calc
          (3 : ZMod 134340584141) ^ 52476790 = (3 : ZMod 134340584141) ^ (26238395 + 26238395) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 26238395 * (3 : ZMod 134340584141) ^ 26238395 := by rw [pow_add]
          _ = 113151524958 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 134340584141) ^ 104953581 = 123679077345 := by
        calc
          (3 : ZMod 134340584141) ^ 104953581 = (3 : ZMod 134340584141) ^ (52476790 + 52476790 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 52476790 * (3 : ZMod 134340584141) ^ 52476790) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 123679077345 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 134340584141) ^ 209907162 = 66266939746 := by
        calc
          (3 : ZMod 134340584141) ^ 209907162 = (3 : ZMod 134340584141) ^ (104953581 + 104953581) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 104953581 * (3 : ZMod 134340584141) ^ 104953581 := by rw [pow_add]
          _ = 66266939746 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 134340584141) ^ 419814325 = 10074408740 := by
        calc
          (3 : ZMod 134340584141) ^ 419814325 = (3 : ZMod 134340584141) ^ (209907162 + 209907162 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 209907162 * (3 : ZMod 134340584141) ^ 209907162) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 10074408740 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 134340584141) ^ 839628650 = 107111661306 := by
        calc
          (3 : ZMod 134340584141) ^ 839628650 = (3 : ZMod 134340584141) ^ (419814325 + 419814325) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 419814325 * (3 : ZMod 134340584141) ^ 419814325 := by rw [pow_add]
          _ = 107111661306 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 134340584141) ^ 1679257301 = 78813989160 := by
        calc
          (3 : ZMod 134340584141) ^ 1679257301 = (3 : ZMod 134340584141) ^ (839628650 + 839628650 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 839628650 * (3 : ZMod 134340584141) ^ 839628650) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 78813989160 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 134340584141) ^ 3358514603 = 19685930126 := by
        calc
          (3 : ZMod 134340584141) ^ 3358514603 = (3 : ZMod 134340584141) ^ (1679257301 + 1679257301 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1679257301 * (3 : ZMod 134340584141) ^ 1679257301) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 19685930126 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 134340584141) ^ 6717029207 = 112572452488 := by
        calc
          (3 : ZMod 134340584141) ^ 6717029207 = (3 : ZMod 134340584141) ^ (3358514603 + 3358514603 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 3358514603 * (3 : ZMod 134340584141) ^ 3358514603) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 112572452488 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 134340584141) ^ 13434058414 = 38199563141 := by
        calc
          (3 : ZMod 134340584141) ^ 13434058414 = (3 : ZMod 134340584141) ^ (6717029207 + 6717029207) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 6717029207 * (3 : ZMod 134340584141) ^ 6717029207 := by rw [pow_add]
          _ = 38199563141 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 134340584141) ^ 26868116828 = 27925850382 := by
        calc
          (3 : ZMod 134340584141) ^ 26868116828 = (3 : ZMod 134340584141) ^ (13434058414 + 13434058414) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 13434058414 * (3 : ZMod 134340584141) ^ 13434058414 := by rw [pow_add]
          _ = 27925850382 := by rw [factor_1_33]; decide
      change (3 : ZMod 134340584141) ^ 26868116828 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (3 : ZMod 134340584141) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 134340584141) ^ 2 = 9 := by
        calc
          (3 : ZMod 134340584141) ^ 2 = (3 : ZMod 134340584141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1 * (3 : ZMod 134340584141) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 134340584141) ^ 4 = 81 := by
        calc
          (3 : ZMod 134340584141) ^ 4 = (3 : ZMod 134340584141) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 2 * (3 : ZMod 134340584141) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 134340584141) ^ 8 = 6561 := by
        calc
          (3 : ZMod 134340584141) ^ 8 = (3 : ZMod 134340584141) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 4 * (3 : ZMod 134340584141) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 134340584141) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 134340584141) ^ 17 = (3 : ZMod 134340584141) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 8 * (3 : ZMod 134340584141) ^ 8) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 134340584141) ^ 35 = 21731456064 := by
        calc
          (3 : ZMod 134340584141) ^ 35 = (3 : ZMod 134340584141) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 17 * (3 : ZMod 134340584141) ^ 17) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 21731456064 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 134340584141) ^ 71 = 55671976798 := by
        calc
          (3 : ZMod 134340584141) ^ 71 = (3 : ZMod 134340584141) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 35 * (3 : ZMod 134340584141) ^ 35) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 55671976798 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 134340584141) ^ 142 = 28574894638 := by
        calc
          (3 : ZMod 134340584141) ^ 142 = (3 : ZMod 134340584141) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 71 * (3 : ZMod 134340584141) ^ 71 := by rw [pow_add]
          _ = 28574894638 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 134340584141) ^ 285 = 113245765044 := by
        calc
          (3 : ZMod 134340584141) ^ 285 = (3 : ZMod 134340584141) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 142 * (3 : ZMod 134340584141) ^ 142) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 113245765044 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 134340584141) ^ 571 = 16345540603 := by
        calc
          (3 : ZMod 134340584141) ^ 571 = (3 : ZMod 134340584141) ^ (285 + 285 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 285 * (3 : ZMod 134340584141) ^ 285) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 16345540603 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 134340584141) ^ 1143 = 92146149935 := by
        calc
          (3 : ZMod 134340584141) ^ 1143 = (3 : ZMod 134340584141) ^ (571 + 571 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 571 * (3 : ZMod 134340584141) ^ 571) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 92146149935 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 134340584141) ^ 2287 = 106087406418 := by
        calc
          (3 : ZMod 134340584141) ^ 2287 = (3 : ZMod 134340584141) ^ (1143 + 1143 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1143 * (3 : ZMod 134340584141) ^ 1143) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 106087406418 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 134340584141) ^ 4575 = 18351087210 := by
        calc
          (3 : ZMod 134340584141) ^ 4575 = (3 : ZMod 134340584141) ^ (2287 + 2287 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2287 * (3 : ZMod 134340584141) ^ 2287) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 18351087210 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 134340584141) ^ 9151 = 36304370813 := by
        calc
          (3 : ZMod 134340584141) ^ 9151 = (3 : ZMod 134340584141) ^ (4575 + 4575 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 4575 * (3 : ZMod 134340584141) ^ 4575) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 36304370813 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 134340584141) ^ 18302 = 84310414994 := by
        calc
          (3 : ZMod 134340584141) ^ 18302 = (3 : ZMod 134340584141) ^ (9151 + 9151) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 9151 * (3 : ZMod 134340584141) ^ 9151 := by rw [pow_add]
          _ = 84310414994 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 134340584141) ^ 36604 = 924116554 := by
        calc
          (3 : ZMod 134340584141) ^ 36604 = (3 : ZMod 134340584141) ^ (18302 + 18302) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 18302 * (3 : ZMod 134340584141) ^ 18302 := by rw [pow_add]
          _ = 924116554 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 134340584141) ^ 73209 = 133210538690 := by
        calc
          (3 : ZMod 134340584141) ^ 73209 = (3 : ZMod 134340584141) ^ (36604 + 36604 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 36604 * (3 : ZMod 134340584141) ^ 36604) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 133210538690 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 134340584141) ^ 146419 = 127411960732 := by
        calc
          (3 : ZMod 134340584141) ^ 146419 = (3 : ZMod 134340584141) ^ (73209 + 73209 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 73209 * (3 : ZMod 134340584141) ^ 73209) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 127411960732 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 134340584141) ^ 292839 = 2374542842 := by
        calc
          (3 : ZMod 134340584141) ^ 292839 = (3 : ZMod 134340584141) ^ (146419 + 146419 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 146419 * (3 : ZMod 134340584141) ^ 146419) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 2374542842 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 134340584141) ^ 585678 = 47415838729 := by
        calc
          (3 : ZMod 134340584141) ^ 585678 = (3 : ZMod 134340584141) ^ (292839 + 292839) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 292839 * (3 : ZMod 134340584141) ^ 292839 := by rw [pow_add]
          _ = 47415838729 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 134340584141) ^ 1171356 = 20473027264 := by
        calc
          (3 : ZMod 134340584141) ^ 1171356 = (3 : ZMod 134340584141) ^ (585678 + 585678) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 585678 * (3 : ZMod 134340584141) ^ 585678 := by rw [pow_add]
          _ = 20473027264 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 134340584141) ^ 2342713 = 99786386130 := by
        calc
          (3 : ZMod 134340584141) ^ 2342713 = (3 : ZMod 134340584141) ^ (1171356 + 1171356 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1171356 * (3 : ZMod 134340584141) ^ 1171356) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 99786386130 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 134340584141) ^ 4685427 = 13999906003 := by
        calc
          (3 : ZMod 134340584141) ^ 4685427 = (3 : ZMod 134340584141) ^ (2342713 + 2342713 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2342713 * (3 : ZMod 134340584141) ^ 2342713) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 13999906003 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 134340584141) ^ 9370855 = 66731221096 := by
        calc
          (3 : ZMod 134340584141) ^ 9370855 = (3 : ZMod 134340584141) ^ (4685427 + 4685427 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 4685427 * (3 : ZMod 134340584141) ^ 4685427) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 66731221096 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 134340584141) ^ 18741710 = 115581621962 := by
        calc
          (3 : ZMod 134340584141) ^ 18741710 = (3 : ZMod 134340584141) ^ (9370855 + 9370855) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 9370855 * (3 : ZMod 134340584141) ^ 9370855 := by rw [pow_add]
          _ = 115581621962 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 134340584141) ^ 37483421 = 58254652915 := by
        calc
          (3 : ZMod 134340584141) ^ 37483421 = (3 : ZMod 134340584141) ^ (18741710 + 18741710 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 18741710 * (3 : ZMod 134340584141) ^ 18741710) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 58254652915 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 134340584141) ^ 74966843 = 104169052315 := by
        calc
          (3 : ZMod 134340584141) ^ 74966843 = (3 : ZMod 134340584141) ^ (37483421 + 37483421 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 37483421 * (3 : ZMod 134340584141) ^ 37483421) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 104169052315 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 134340584141) ^ 149933687 = 103177406983 := by
        calc
          (3 : ZMod 134340584141) ^ 149933687 = (3 : ZMod 134340584141) ^ (74966843 + 74966843 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 74966843 * (3 : ZMod 134340584141) ^ 74966843) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 103177406983 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 134340584141) ^ 299867375 = 70950032562 := by
        calc
          (3 : ZMod 134340584141) ^ 299867375 = (3 : ZMod 134340584141) ^ (149933687 + 149933687 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 149933687 * (3 : ZMod 134340584141) ^ 149933687) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 70950032562 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 134340584141) ^ 599734750 = 13633938381 := by
        calc
          (3 : ZMod 134340584141) ^ 599734750 = (3 : ZMod 134340584141) ^ (299867375 + 299867375) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 299867375 * (3 : ZMod 134340584141) ^ 299867375 := by rw [pow_add]
          _ = 13633938381 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 134340584141) ^ 1199469501 = 70850934039 := by
        calc
          (3 : ZMod 134340584141) ^ 1199469501 = (3 : ZMod 134340584141) ^ (599734750 + 599734750 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 599734750 * (3 : ZMod 134340584141) ^ 599734750) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 70850934039 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 134340584141) ^ 2398939002 = 40340225294 := by
        calc
          (3 : ZMod 134340584141) ^ 2398939002 = (3 : ZMod 134340584141) ^ (1199469501 + 1199469501) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1199469501 * (3 : ZMod 134340584141) ^ 1199469501 := by rw [pow_add]
          _ = 40340225294 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 134340584141) ^ 4797878005 = 71341531286 := by
        calc
          (3 : ZMod 134340584141) ^ 4797878005 = (3 : ZMod 134340584141) ^ (2398939002 + 2398939002 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2398939002 * (3 : ZMod 134340584141) ^ 2398939002) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 71341531286 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 134340584141) ^ 9595756010 = 2734764863 := by
        calc
          (3 : ZMod 134340584141) ^ 9595756010 = (3 : ZMod 134340584141) ^ (4797878005 + 4797878005) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 4797878005 * (3 : ZMod 134340584141) ^ 4797878005 := by rw [pow_add]
          _ = 2734764863 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 134340584141) ^ 19191512020 = 115727162512 := by
        calc
          (3 : ZMod 134340584141) ^ 19191512020 = (3 : ZMod 134340584141) ^ (9595756010 + 9595756010) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 9595756010 * (3 : ZMod 134340584141) ^ 9595756010 := by rw [pow_add]
          _ = 115727162512 := by rw [factor_2_33]; decide
      change (3 : ZMod 134340584141) ^ 19191512020 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (3 : ZMod 134340584141) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 134340584141) ^ 3 = 27 := by
        calc
          (3 : ZMod 134340584141) ^ 3 = (3 : ZMod 134340584141) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1 * (3 : ZMod 134340584141) ^ 1) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 134340584141) ^ 6 = 729 := by
        calc
          (3 : ZMod 134340584141) ^ 6 = (3 : ZMod 134340584141) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 3 * (3 : ZMod 134340584141) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 134340584141) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 134340584141) ^ 13 = (3 : ZMod 134340584141) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 6 * (3 : ZMod 134340584141) ^ 6) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 134340584141) ^ 26 = 123735313791 := by
        calc
          (3 : ZMod 134340584141) ^ 26 = (3 : ZMod 134340584141) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 13 * (3 : ZMod 134340584141) ^ 13 := by rw [pow_add]
          _ = 123735313791 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 134340584141) ^ 52 = 92401218117 := by
        calc
          (3 : ZMod 134340584141) ^ 52 = (3 : ZMod 134340584141) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 26 * (3 : ZMod 134340584141) ^ 26 := by rw [pow_add]
          _ = 92401218117 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 134340584141) ^ 105 = 31595487646 := by
        calc
          (3 : ZMod 134340584141) ^ 105 = (3 : ZMod 134340584141) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 52 * (3 : ZMod 134340584141) ^ 52) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 31595487646 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 134340584141) ^ 210 = 123729240361 := by
        calc
          (3 : ZMod 134340584141) ^ 210 = (3 : ZMod 134340584141) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 105 * (3 : ZMod 134340584141) ^ 105 := by rw [pow_add]
          _ = 123729240361 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 134340584141) ^ 421 = 48169576091 := by
        calc
          (3 : ZMod 134340584141) ^ 421 = (3 : ZMod 134340584141) ^ (210 + 210 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 210 * (3 : ZMod 134340584141) ^ 210) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 48169576091 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 134340584141) ^ 842 = 133819080690 := by
        calc
          (3 : ZMod 134340584141) ^ 842 = (3 : ZMod 134340584141) ^ (421 + 421) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 421 * (3 : ZMod 134340584141) ^ 421 := by rw [pow_add]
          _ = 133819080690 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 134340584141) ^ 1685 = 27181401712 := by
        calc
          (3 : ZMod 134340584141) ^ 1685 = (3 : ZMod 134340584141) ^ (842 + 842 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 842 * (3 : ZMod 134340584141) ^ 842) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 27181401712 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 134340584141) ^ 3371 = 1039340735 := by
        calc
          (3 : ZMod 134340584141) ^ 3371 = (3 : ZMod 134340584141) ^ (1685 + 1685 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 1685 * (3 : ZMod 134340584141) ^ 1685) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 1039340735 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 134340584141) ^ 6743 = 57623240673 := by
        calc
          (3 : ZMod 134340584141) ^ 6743 = (3 : ZMod 134340584141) ^ (3371 + 3371 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 3371 * (3 : ZMod 134340584141) ^ 3371) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 57623240673 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 134340584141) ^ 13486 = 24533730112 := by
        calc
          (3 : ZMod 134340584141) ^ 13486 = (3 : ZMod 134340584141) ^ (6743 + 6743) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 6743 * (3 : ZMod 134340584141) ^ 6743 := by rw [pow_add]
          _ = 24533730112 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 134340584141) ^ 26972 = 133801420530 := by
        calc
          (3 : ZMod 134340584141) ^ 26972 = (3 : ZMod 134340584141) ^ (13486 + 13486) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 13486 * (3 : ZMod 134340584141) ^ 13486 := by rw [pow_add]
          _ = 133801420530 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 134340584141) ^ 53944 = 93193779818 := by
        calc
          (3 : ZMod 134340584141) ^ 53944 = (3 : ZMod 134340584141) ^ (26972 + 26972) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 26972 * (3 : ZMod 134340584141) ^ 26972 := by rw [pow_add]
          _ = 93193779818 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 134340584141) ^ 107888 = 90936749198 := by
        calc
          (3 : ZMod 134340584141) ^ 107888 = (3 : ZMod 134340584141) ^ (53944 + 53944) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 53944 * (3 : ZMod 134340584141) ^ 53944 := by rw [pow_add]
          _ = 90936749198 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 134340584141) ^ 215776 = 56555384098 := by
        calc
          (3 : ZMod 134340584141) ^ 215776 = (3 : ZMod 134340584141) ^ (107888 + 107888) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 107888 * (3 : ZMod 134340584141) ^ 107888 := by rw [pow_add]
          _ = 56555384098 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 134340584141) ^ 431552 = 82009800398 := by
        calc
          (3 : ZMod 134340584141) ^ 431552 = (3 : ZMod 134340584141) ^ (215776 + 215776) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 215776 * (3 : ZMod 134340584141) ^ 215776 := by rw [pow_add]
          _ = 82009800398 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 134340584141) ^ 863105 = 91948413849 := by
        calc
          (3 : ZMod 134340584141) ^ 863105 = (3 : ZMod 134340584141) ^ (431552 + 431552 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 431552 * (3 : ZMod 134340584141) ^ 431552) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 91948413849 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 134340584141) ^ 1726210 = 119200617458 := by
        calc
          (3 : ZMod 134340584141) ^ 1726210 = (3 : ZMod 134340584141) ^ (863105 + 863105) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 863105 * (3 : ZMod 134340584141) ^ 863105 := by rw [pow_add]
          _ = 119200617458 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 134340584141) ^ 3452420 = 101421956637 := by
        calc
          (3 : ZMod 134340584141) ^ 3452420 = (3 : ZMod 134340584141) ^ (1726210 + 1726210) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1726210 * (3 : ZMod 134340584141) ^ 1726210 := by rw [pow_add]
          _ = 101421956637 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 134340584141) ^ 6904840 = 130210168083 := by
        calc
          (3 : ZMod 134340584141) ^ 6904840 = (3 : ZMod 134340584141) ^ (3452420 + 3452420) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 3452420 * (3 : ZMod 134340584141) ^ 3452420 := by rw [pow_add]
          _ = 130210168083 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 134340584141) ^ 13809681 = 114379074759 := by
        calc
          (3 : ZMod 134340584141) ^ 13809681 = (3 : ZMod 134340584141) ^ (6904840 + 6904840 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 6904840 * (3 : ZMod 134340584141) ^ 6904840) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 114379074759 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 134340584141) ^ 27619363 = 26506054313 := by
        calc
          (3 : ZMod 134340584141) ^ 27619363 = (3 : ZMod 134340584141) ^ (13809681 + 13809681 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 13809681 * (3 : ZMod 134340584141) ^ 13809681) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 26506054313 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 134340584141) ^ 55238727 = 66119589355 := by
        calc
          (3 : ZMod 134340584141) ^ 55238727 = (3 : ZMod 134340584141) ^ (27619363 + 27619363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 27619363 * (3 : ZMod 134340584141) ^ 27619363) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 66119589355 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 134340584141) ^ 110477454 = 36514482424 := by
        calc
          (3 : ZMod 134340584141) ^ 110477454 = (3 : ZMod 134340584141) ^ (55238727 + 55238727) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 55238727 * (3 : ZMod 134340584141) ^ 55238727 := by rw [pow_add]
          _ = 36514482424 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 134340584141) ^ 220954908 = 40267584462 := by
        calc
          (3 : ZMod 134340584141) ^ 220954908 = (3 : ZMod 134340584141) ^ (110477454 + 110477454) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 110477454 * (3 : ZMod 134340584141) ^ 110477454 := by rw [pow_add]
          _ = 40267584462 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 134340584141) ^ 441909816 = 19012516893 := by
        calc
          (3 : ZMod 134340584141) ^ 441909816 = (3 : ZMod 134340584141) ^ (220954908 + 220954908) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 220954908 * (3 : ZMod 134340584141) ^ 220954908 := by rw [pow_add]
          _ = 19012516893 := by rw [factor_3_27]; decide
      have factor_3_29 : (3 : ZMod 134340584141) ^ 883819632 = 21440239567 := by
        calc
          (3 : ZMod 134340584141) ^ 883819632 = (3 : ZMod 134340584141) ^ (441909816 + 441909816) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 441909816 * (3 : ZMod 134340584141) ^ 441909816 := by rw [pow_add]
          _ = 21440239567 := by rw [factor_3_28]; decide
      have factor_3_30 : (3 : ZMod 134340584141) ^ 1767639265 = 19393528053 := by
        calc
          (3 : ZMod 134340584141) ^ 1767639265 = (3 : ZMod 134340584141) ^ (883819632 + 883819632 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 883819632 * (3 : ZMod 134340584141) ^ 883819632) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 19393528053 := by rw [factor_3_29]; decide
      have factor_3_31 : (3 : ZMod 134340584141) ^ 3535278530 = 69926076225 := by
        calc
          (3 : ZMod 134340584141) ^ 3535278530 = (3 : ZMod 134340584141) ^ (1767639265 + 1767639265) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1767639265 * (3 : ZMod 134340584141) ^ 1767639265 := by rw [pow_add]
          _ = 69926076225 := by rw [factor_3_30]; decide
      have factor_3_32 : (3 : ZMod 134340584141) ^ 7070557060 = 104180215272 := by
        calc
          (3 : ZMod 134340584141) ^ 7070557060 = (3 : ZMod 134340584141) ^ (3535278530 + 3535278530) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 3535278530 * (3 : ZMod 134340584141) ^ 3535278530 := by rw [pow_add]
          _ = 104180215272 := by rw [factor_3_31]; decide
      change (3 : ZMod 134340584141) ^ 7070557060 ≠ 1
      rw [factor_3_32]
      decide
    ·
      have factor_4_0 : (3 : ZMod 134340584141) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 134340584141) ^ 2 = 9 := by
        calc
          (3 : ZMod 134340584141) ^ 2 = (3 : ZMod 134340584141) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1 * (3 : ZMod 134340584141) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 134340584141) ^ 5 = 243 := by
        calc
          (3 : ZMod 134340584141) ^ 5 = (3 : ZMod 134340584141) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 2 * (3 : ZMod 134340584141) ^ 2) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 134340584141) ^ 10 = 59049 := by
        calc
          (3 : ZMod 134340584141) ^ 10 = (3 : ZMod 134340584141) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 5 * (3 : ZMod 134340584141) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 134340584141) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 134340584141) ^ 20 = (3 : ZMod 134340584141) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 10 * (3 : ZMod 134340584141) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 134340584141) ^ 41 = 124383126159 := by
        calc
          (3 : ZMod 134340584141) ^ 41 = (3 : ZMod 134340584141) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 20 * (3 : ZMod 134340584141) ^ 20) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 124383126159 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 134340584141) ^ 83 = 6813796924 := by
        calc
          (3 : ZMod 134340584141) ^ 83 = (3 : ZMod 134340584141) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 41 * (3 : ZMod 134340584141) ^ 41) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 6813796924 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 134340584141) ^ 166 = 55688512941 := by
        calc
          (3 : ZMod 134340584141) ^ 166 = (3 : ZMod 134340584141) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 83 * (3 : ZMod 134340584141) ^ 83 := by rw [pow_add]
          _ = 55688512941 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 134340584141) ^ 332 = 126039194520 := by
        calc
          (3 : ZMod 134340584141) ^ 332 = (3 : ZMod 134340584141) ^ (166 + 166) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 166 * (3 : ZMod 134340584141) ^ 166 := by rw [pow_add]
          _ = 126039194520 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 134340584141) ^ 665 = 26953903833 := by
        calc
          (3 : ZMod 134340584141) ^ 665 = (3 : ZMod 134340584141) ^ (332 + 332 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = ((3 : ZMod 134340584141) ^ 332 * (3 : ZMod 134340584141) ^ 332) * (3 : ZMod 134340584141) := by rw [pow_succ, pow_add]
          _ = 26953903833 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 134340584141) ^ 1330 = 39542870080 := by
        calc
          (3 : ZMod 134340584141) ^ 1330 = (3 : ZMod 134340584141) ^ (665 + 665) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 665 * (3 : ZMod 134340584141) ^ 665 := by rw [pow_add]
          _ = 39542870080 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 134340584141) ^ 2660 = 125465862224 := by
        calc
          (3 : ZMod 134340584141) ^ 2660 = (3 : ZMod 134340584141) ^ (1330 + 1330) :=
            congrArg (fun n : ℕ => (3 : ZMod 134340584141) ^ n) (by norm_num)
          _ = (3 : ZMod 134340584141) ^ 1330 * (3 : ZMod 134340584141) ^ 1330 := by rw [pow_add]
          _ = 125465862224 := by rw [factor_4_10]; decide
      change (3 : ZMod 134340584141) ^ 2660 ≠ 1
      rw [factor_4_11]
      decide

#print axioms prime_lucas_134340584141

end TotientTailPeriodKiller
end Erdos249257
