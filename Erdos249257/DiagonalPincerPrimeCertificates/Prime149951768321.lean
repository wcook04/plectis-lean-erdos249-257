import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_149951768321 : Nat.Prime 149951768321 := by
  apply lucas_primality 149951768321 (3 : ZMod 149951768321)
  ·
      have fermat_0 : (3 : ZMod 149951768321) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 149951768321) ^ 2 = 9 := by
        calc
          (3 : ZMod 149951768321) ^ 2 = (3 : ZMod 149951768321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1 * (3 : ZMod 149951768321) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 149951768321) ^ 4 = 81 := by
        calc
          (3 : ZMod 149951768321) ^ 4 = (3 : ZMod 149951768321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2 * (3 : ZMod 149951768321) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 149951768321) ^ 8 = 6561 := by
        calc
          (3 : ZMod 149951768321) ^ 8 = (3 : ZMod 149951768321) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 4 * (3 : ZMod 149951768321) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 149951768321) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 149951768321) ^ 17 = (3 : ZMod 149951768321) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 8 * (3 : ZMod 149951768321) ^ 8) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 149951768321) ^ 34 = 145834078233 := by
        calc
          (3 : ZMod 149951768321) ^ 34 = (3 : ZMod 149951768321) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 17 * (3 : ZMod 149951768321) ^ 17 := by rw [pow_add]
          _ = 145834078233 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 149951768321) ^ 69 = 64069236806 := by
        calc
          (3 : ZMod 149951768321) ^ 69 = (3 : ZMod 149951768321) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 34 * (3 : ZMod 149951768321) ^ 34) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 64069236806 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 149951768321) ^ 139 = 137725011889 := by
        calc
          (3 : ZMod 149951768321) ^ 139 = (3 : ZMod 149951768321) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 69 * (3 : ZMod 149951768321) ^ 69) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 137725011889 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 149951768321) ^ 279 = 146407617290 := by
        calc
          (3 : ZMod 149951768321) ^ 279 = (3 : ZMod 149951768321) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 139 * (3 : ZMod 149951768321) ^ 139) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 146407617290 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 149951768321) ^ 558 = 52532059023 := by
        calc
          (3 : ZMod 149951768321) ^ 558 = (3 : ZMod 149951768321) ^ (279 + 279) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 279 * (3 : ZMod 149951768321) ^ 279 := by rw [pow_add]
          _ = 52532059023 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 149951768321) ^ 1117 = 64315860019 := by
        calc
          (3 : ZMod 149951768321) ^ 1117 = (3 : ZMod 149951768321) ^ (558 + 558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 558 * (3 : ZMod 149951768321) ^ 558) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 64315860019 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 149951768321) ^ 2234 = 133249774093 := by
        calc
          (3 : ZMod 149951768321) ^ 2234 = (3 : ZMod 149951768321) ^ (1117 + 1117) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1117 * (3 : ZMod 149951768321) ^ 1117 := by rw [pow_add]
          _ = 133249774093 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 149951768321) ^ 4468 = 64477970911 := by
        calc
          (3 : ZMod 149951768321) ^ 4468 = (3 : ZMod 149951768321) ^ (2234 + 2234) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2234 * (3 : ZMod 149951768321) ^ 2234 := by rw [pow_add]
          _ = 64477970911 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 149951768321) ^ 8937 = 147927520268 := by
        calc
          (3 : ZMod 149951768321) ^ 8937 = (3 : ZMod 149951768321) ^ (4468 + 4468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 4468 * (3 : ZMod 149951768321) ^ 4468) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 147927520268 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 149951768321) ^ 17875 = 25019362304 := by
        calc
          (3 : ZMod 149951768321) ^ 17875 = (3 : ZMod 149951768321) ^ (8937 + 8937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 8937 * (3 : ZMod 149951768321) ^ 8937) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 25019362304 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 149951768321) ^ 35751 = 92744638697 := by
        calc
          (3 : ZMod 149951768321) ^ 35751 = (3 : ZMod 149951768321) ^ (17875 + 17875 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 17875 * (3 : ZMod 149951768321) ^ 17875) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 92744638697 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 149951768321) ^ 71502 = 10237834584 := by
        calc
          (3 : ZMod 149951768321) ^ 71502 = (3 : ZMod 149951768321) ^ (35751 + 35751) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 35751 * (3 : ZMod 149951768321) ^ 35751 := by rw [pow_add]
          _ = 10237834584 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 149951768321) ^ 143005 = 115966148410 := by
        calc
          (3 : ZMod 149951768321) ^ 143005 = (3 : ZMod 149951768321) ^ (71502 + 71502 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 71502 * (3 : ZMod 149951768321) ^ 71502) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 115966148410 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 149951768321) ^ 286010 = 110388219553 := by
        calc
          (3 : ZMod 149951768321) ^ 286010 = (3 : ZMod 149951768321) ^ (143005 + 143005) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 143005 * (3 : ZMod 149951768321) ^ 143005 := by rw [pow_add]
          _ = 110388219553 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 149951768321) ^ 572020 = 18258692848 := by
        calc
          (3 : ZMod 149951768321) ^ 572020 = (3 : ZMod 149951768321) ^ (286010 + 286010) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 286010 * (3 : ZMod 149951768321) ^ 286010 := by rw [pow_add]
          _ = 18258692848 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 149951768321) ^ 1144041 = 53586788523 := by
        calc
          (3 : ZMod 149951768321) ^ 1144041 = (3 : ZMod 149951768321) ^ (572020 + 572020 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 572020 * (3 : ZMod 149951768321) ^ 572020) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 53586788523 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 149951768321) ^ 2288082 = 21152358473 := by
        calc
          (3 : ZMod 149951768321) ^ 2288082 = (3 : ZMod 149951768321) ^ (1144041 + 1144041) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1144041 * (3 : ZMod 149951768321) ^ 1144041 := by rw [pow_add]
          _ = 21152358473 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 149951768321) ^ 4576164 = 126213007747 := by
        calc
          (3 : ZMod 149951768321) ^ 4576164 = (3 : ZMod 149951768321) ^ (2288082 + 2288082) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2288082 * (3 : ZMod 149951768321) ^ 2288082 := by rw [pow_add]
          _ = 126213007747 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 149951768321) ^ 9152329 = 25517282919 := by
        calc
          (3 : ZMod 149951768321) ^ 9152329 = (3 : ZMod 149951768321) ^ (4576164 + 4576164 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 4576164 * (3 : ZMod 149951768321) ^ 4576164) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 25517282919 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 149951768321) ^ 18304659 = 12492376828 := by
        calc
          (3 : ZMod 149951768321) ^ 18304659 = (3 : ZMod 149951768321) ^ (9152329 + 9152329 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 9152329 * (3 : ZMod 149951768321) ^ 9152329) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 12492376828 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 149951768321) ^ 36609318 = 124275149298 := by
        calc
          (3 : ZMod 149951768321) ^ 36609318 = (3 : ZMod 149951768321) ^ (18304659 + 18304659) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 18304659 * (3 : ZMod 149951768321) ^ 18304659 := by rw [pow_add]
          _ = 124275149298 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 149951768321) ^ 73218636 = 82333672774 := by
        calc
          (3 : ZMod 149951768321) ^ 73218636 = (3 : ZMod 149951768321) ^ (36609318 + 36609318) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 36609318 * (3 : ZMod 149951768321) ^ 36609318 := by rw [pow_add]
          _ = 82333672774 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 149951768321) ^ 146437273 = 47086889260 := by
        calc
          (3 : ZMod 149951768321) ^ 146437273 = (3 : ZMod 149951768321) ^ (73218636 + 73218636 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 73218636 * (3 : ZMod 149951768321) ^ 73218636) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 47086889260 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 149951768321) ^ 292874547 = 71732821000 := by
        calc
          (3 : ZMod 149951768321) ^ 292874547 = (3 : ZMod 149951768321) ^ (146437273 + 146437273 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 146437273 * (3 : ZMod 149951768321) ^ 146437273) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 71732821000 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 149951768321) ^ 585749095 = 133513677610 := by
        calc
          (3 : ZMod 149951768321) ^ 585749095 = (3 : ZMod 149951768321) ^ (292874547 + 292874547 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 292874547 * (3 : ZMod 149951768321) ^ 292874547) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 133513677610 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 149951768321) ^ 1171498190 = 81578156275 := by
        calc
          (3 : ZMod 149951768321) ^ 1171498190 = (3 : ZMod 149951768321) ^ (585749095 + 585749095) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 585749095 * (3 : ZMod 149951768321) ^ 585749095 := by rw [pow_add]
          _ = 81578156275 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 149951768321) ^ 2342996380 = 19632393259 := by
        calc
          (3 : ZMod 149951768321) ^ 2342996380 = (3 : ZMod 149951768321) ^ (1171498190 + 1171498190) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1171498190 * (3 : ZMod 149951768321) ^ 1171498190 := by rw [pow_add]
          _ = 19632393259 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 149951768321) ^ 4685992760 = 73933471654 := by
        calc
          (3 : ZMod 149951768321) ^ 4685992760 = (3 : ZMod 149951768321) ^ (2342996380 + 2342996380) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2342996380 * (3 : ZMod 149951768321) ^ 2342996380 := by rw [pow_add]
          _ = 73933471654 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 149951768321) ^ 9371985520 = 106502763814 := by
        calc
          (3 : ZMod 149951768321) ^ 9371985520 = (3 : ZMod 149951768321) ^ (4685992760 + 4685992760) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 4685992760 * (3 : ZMod 149951768321) ^ 4685992760 := by rw [pow_add]
          _ = 106502763814 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 149951768321) ^ 18743971040 = 144791847098 := by
        calc
          (3 : ZMod 149951768321) ^ 18743971040 = (3 : ZMod 149951768321) ^ (9371985520 + 9371985520) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 9371985520 * (3 : ZMod 149951768321) ^ 9371985520 := by rw [pow_add]
          _ = 144791847098 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 149951768321) ^ 37487942080 = 35742349017 := by
        calc
          (3 : ZMod 149951768321) ^ 37487942080 = (3 : ZMod 149951768321) ^ (18743971040 + 18743971040) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 18743971040 * (3 : ZMod 149951768321) ^ 18743971040 := by rw [pow_add]
          _ = 35742349017 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 149951768321) ^ 74975884160 = 149951768320 := by
        calc
          (3 : ZMod 149951768321) ^ 74975884160 = (3 : ZMod 149951768321) ^ (37487942080 + 37487942080) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 37487942080 * (3 : ZMod 149951768321) ^ 37487942080 := by rw [pow_add]
          _ = 149951768320 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 149951768321) ^ 149951768320 = 1 := by
        calc
          (3 : ZMod 149951768321) ^ 149951768320 = (3 : ZMod 149951768321) ^ (74975884160 + 74975884160) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 74975884160 * (3 : ZMod 149951768321) ^ 74975884160 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (5, 1), (6121, 1), (19139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (5, 1), (6121, 1), (19139, 1)] : List FactorBlock).map factorBlockValue).prod = 149951768321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 149951768321) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 149951768321) ^ 2 = 9 := by
        calc
          (3 : ZMod 149951768321) ^ 2 = (3 : ZMod 149951768321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1 * (3 : ZMod 149951768321) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 149951768321) ^ 4 = 81 := by
        calc
          (3 : ZMod 149951768321) ^ 4 = (3 : ZMod 149951768321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2 * (3 : ZMod 149951768321) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 149951768321) ^ 8 = 6561 := by
        calc
          (3 : ZMod 149951768321) ^ 8 = (3 : ZMod 149951768321) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 4 * (3 : ZMod 149951768321) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 149951768321) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 149951768321) ^ 17 = (3 : ZMod 149951768321) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 8 * (3 : ZMod 149951768321) ^ 8) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 149951768321) ^ 34 = 145834078233 := by
        calc
          (3 : ZMod 149951768321) ^ 34 = (3 : ZMod 149951768321) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 17 * (3 : ZMod 149951768321) ^ 17 := by rw [pow_add]
          _ = 145834078233 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 149951768321) ^ 69 = 64069236806 := by
        calc
          (3 : ZMod 149951768321) ^ 69 = (3 : ZMod 149951768321) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 34 * (3 : ZMod 149951768321) ^ 34) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 64069236806 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 149951768321) ^ 139 = 137725011889 := by
        calc
          (3 : ZMod 149951768321) ^ 139 = (3 : ZMod 149951768321) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 69 * (3 : ZMod 149951768321) ^ 69) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 137725011889 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 149951768321) ^ 279 = 146407617290 := by
        calc
          (3 : ZMod 149951768321) ^ 279 = (3 : ZMod 149951768321) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 139 * (3 : ZMod 149951768321) ^ 139) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 146407617290 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 149951768321) ^ 558 = 52532059023 := by
        calc
          (3 : ZMod 149951768321) ^ 558 = (3 : ZMod 149951768321) ^ (279 + 279) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 279 * (3 : ZMod 149951768321) ^ 279 := by rw [pow_add]
          _ = 52532059023 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 149951768321) ^ 1117 = 64315860019 := by
        calc
          (3 : ZMod 149951768321) ^ 1117 = (3 : ZMod 149951768321) ^ (558 + 558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 558 * (3 : ZMod 149951768321) ^ 558) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 64315860019 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 149951768321) ^ 2234 = 133249774093 := by
        calc
          (3 : ZMod 149951768321) ^ 2234 = (3 : ZMod 149951768321) ^ (1117 + 1117) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1117 * (3 : ZMod 149951768321) ^ 1117 := by rw [pow_add]
          _ = 133249774093 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 149951768321) ^ 4468 = 64477970911 := by
        calc
          (3 : ZMod 149951768321) ^ 4468 = (3 : ZMod 149951768321) ^ (2234 + 2234) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2234 * (3 : ZMod 149951768321) ^ 2234 := by rw [pow_add]
          _ = 64477970911 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 149951768321) ^ 8937 = 147927520268 := by
        calc
          (3 : ZMod 149951768321) ^ 8937 = (3 : ZMod 149951768321) ^ (4468 + 4468 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 4468 * (3 : ZMod 149951768321) ^ 4468) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 147927520268 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 149951768321) ^ 17875 = 25019362304 := by
        calc
          (3 : ZMod 149951768321) ^ 17875 = (3 : ZMod 149951768321) ^ (8937 + 8937 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 8937 * (3 : ZMod 149951768321) ^ 8937) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 25019362304 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 149951768321) ^ 35751 = 92744638697 := by
        calc
          (3 : ZMod 149951768321) ^ 35751 = (3 : ZMod 149951768321) ^ (17875 + 17875 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 17875 * (3 : ZMod 149951768321) ^ 17875) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 92744638697 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 149951768321) ^ 71502 = 10237834584 := by
        calc
          (3 : ZMod 149951768321) ^ 71502 = (3 : ZMod 149951768321) ^ (35751 + 35751) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 35751 * (3 : ZMod 149951768321) ^ 35751 := by rw [pow_add]
          _ = 10237834584 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 149951768321) ^ 143005 = 115966148410 := by
        calc
          (3 : ZMod 149951768321) ^ 143005 = (3 : ZMod 149951768321) ^ (71502 + 71502 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 71502 * (3 : ZMod 149951768321) ^ 71502) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 115966148410 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 149951768321) ^ 286010 = 110388219553 := by
        calc
          (3 : ZMod 149951768321) ^ 286010 = (3 : ZMod 149951768321) ^ (143005 + 143005) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 143005 * (3 : ZMod 149951768321) ^ 143005 := by rw [pow_add]
          _ = 110388219553 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 149951768321) ^ 572020 = 18258692848 := by
        calc
          (3 : ZMod 149951768321) ^ 572020 = (3 : ZMod 149951768321) ^ (286010 + 286010) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 286010 * (3 : ZMod 149951768321) ^ 286010 := by rw [pow_add]
          _ = 18258692848 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 149951768321) ^ 1144041 = 53586788523 := by
        calc
          (3 : ZMod 149951768321) ^ 1144041 = (3 : ZMod 149951768321) ^ (572020 + 572020 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 572020 * (3 : ZMod 149951768321) ^ 572020) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 53586788523 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 149951768321) ^ 2288082 = 21152358473 := by
        calc
          (3 : ZMod 149951768321) ^ 2288082 = (3 : ZMod 149951768321) ^ (1144041 + 1144041) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1144041 * (3 : ZMod 149951768321) ^ 1144041 := by rw [pow_add]
          _ = 21152358473 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 149951768321) ^ 4576164 = 126213007747 := by
        calc
          (3 : ZMod 149951768321) ^ 4576164 = (3 : ZMod 149951768321) ^ (2288082 + 2288082) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2288082 * (3 : ZMod 149951768321) ^ 2288082 := by rw [pow_add]
          _ = 126213007747 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 149951768321) ^ 9152329 = 25517282919 := by
        calc
          (3 : ZMod 149951768321) ^ 9152329 = (3 : ZMod 149951768321) ^ (4576164 + 4576164 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 4576164 * (3 : ZMod 149951768321) ^ 4576164) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 25517282919 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 149951768321) ^ 18304659 = 12492376828 := by
        calc
          (3 : ZMod 149951768321) ^ 18304659 = (3 : ZMod 149951768321) ^ (9152329 + 9152329 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 9152329 * (3 : ZMod 149951768321) ^ 9152329) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 12492376828 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 149951768321) ^ 36609318 = 124275149298 := by
        calc
          (3 : ZMod 149951768321) ^ 36609318 = (3 : ZMod 149951768321) ^ (18304659 + 18304659) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 18304659 * (3 : ZMod 149951768321) ^ 18304659 := by rw [pow_add]
          _ = 124275149298 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 149951768321) ^ 73218636 = 82333672774 := by
        calc
          (3 : ZMod 149951768321) ^ 73218636 = (3 : ZMod 149951768321) ^ (36609318 + 36609318) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 36609318 * (3 : ZMod 149951768321) ^ 36609318 := by rw [pow_add]
          _ = 82333672774 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 149951768321) ^ 146437273 = 47086889260 := by
        calc
          (3 : ZMod 149951768321) ^ 146437273 = (3 : ZMod 149951768321) ^ (73218636 + 73218636 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 73218636 * (3 : ZMod 149951768321) ^ 73218636) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 47086889260 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 149951768321) ^ 292874547 = 71732821000 := by
        calc
          (3 : ZMod 149951768321) ^ 292874547 = (3 : ZMod 149951768321) ^ (146437273 + 146437273 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 146437273 * (3 : ZMod 149951768321) ^ 146437273) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 71732821000 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 149951768321) ^ 585749095 = 133513677610 := by
        calc
          (3 : ZMod 149951768321) ^ 585749095 = (3 : ZMod 149951768321) ^ (292874547 + 292874547 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 292874547 * (3 : ZMod 149951768321) ^ 292874547) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 133513677610 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 149951768321) ^ 1171498190 = 81578156275 := by
        calc
          (3 : ZMod 149951768321) ^ 1171498190 = (3 : ZMod 149951768321) ^ (585749095 + 585749095) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 585749095 * (3 : ZMod 149951768321) ^ 585749095 := by rw [pow_add]
          _ = 81578156275 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 149951768321) ^ 2342996380 = 19632393259 := by
        calc
          (3 : ZMod 149951768321) ^ 2342996380 = (3 : ZMod 149951768321) ^ (1171498190 + 1171498190) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1171498190 * (3 : ZMod 149951768321) ^ 1171498190 := by rw [pow_add]
          _ = 19632393259 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 149951768321) ^ 4685992760 = 73933471654 := by
        calc
          (3 : ZMod 149951768321) ^ 4685992760 = (3 : ZMod 149951768321) ^ (2342996380 + 2342996380) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2342996380 * (3 : ZMod 149951768321) ^ 2342996380 := by rw [pow_add]
          _ = 73933471654 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 149951768321) ^ 9371985520 = 106502763814 := by
        calc
          (3 : ZMod 149951768321) ^ 9371985520 = (3 : ZMod 149951768321) ^ (4685992760 + 4685992760) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 4685992760 * (3 : ZMod 149951768321) ^ 4685992760 := by rw [pow_add]
          _ = 106502763814 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 149951768321) ^ 18743971040 = 144791847098 := by
        calc
          (3 : ZMod 149951768321) ^ 18743971040 = (3 : ZMod 149951768321) ^ (9371985520 + 9371985520) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 9371985520 * (3 : ZMod 149951768321) ^ 9371985520 := by rw [pow_add]
          _ = 144791847098 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 149951768321) ^ 37487942080 = 35742349017 := by
        calc
          (3 : ZMod 149951768321) ^ 37487942080 = (3 : ZMod 149951768321) ^ (18743971040 + 18743971040) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 18743971040 * (3 : ZMod 149951768321) ^ 18743971040 := by rw [pow_add]
          _ = 35742349017 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 149951768321) ^ 74975884160 = 149951768320 := by
        calc
          (3 : ZMod 149951768321) ^ 74975884160 = (3 : ZMod 149951768321) ^ (37487942080 + 37487942080) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 37487942080 * (3 : ZMod 149951768321) ^ 37487942080 := by rw [pow_add]
          _ = 149951768320 := by rw [factor_0_35]; decide
      change (3 : ZMod 149951768321) ^ 74975884160 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (3 : ZMod 149951768321) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 149951768321) ^ 3 = 27 := by
        calc
          (3 : ZMod 149951768321) ^ 3 = (3 : ZMod 149951768321) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 1 * (3 : ZMod 149951768321) ^ 1) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 149951768321) ^ 6 = 729 := by
        calc
          (3 : ZMod 149951768321) ^ 6 = (3 : ZMod 149951768321) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 3 * (3 : ZMod 149951768321) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 149951768321) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 149951768321) ^ 13 = (3 : ZMod 149951768321) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 6 * (3 : ZMod 149951768321) ^ 6) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 149951768321) ^ 27 = 128009068937 := by
        calc
          (3 : ZMod 149951768321) ^ 27 = (3 : ZMod 149951768321) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 13 * (3 : ZMod 149951768321) ^ 13) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 128009068937 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 149951768321) ^ 55 = 69992014609 := by
        calc
          (3 : ZMod 149951768321) ^ 55 = (3 : ZMod 149951768321) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 27 * (3 : ZMod 149951768321) ^ 27) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 69992014609 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 149951768321) ^ 111 = 54198251995 := by
        calc
          (3 : ZMod 149951768321) ^ 111 = (3 : ZMod 149951768321) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 55 * (3 : ZMod 149951768321) ^ 55) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 54198251995 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 149951768321) ^ 223 = 10943649990 := by
        calc
          (3 : ZMod 149951768321) ^ 223 = (3 : ZMod 149951768321) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 111 * (3 : ZMod 149951768321) ^ 111) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 10943649990 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 149951768321) ^ 446 = 79949623162 := by
        calc
          (3 : ZMod 149951768321) ^ 446 = (3 : ZMod 149951768321) ^ (223 + 223) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 223 * (3 : ZMod 149951768321) ^ 223 := by rw [pow_add]
          _ = 79949623162 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 149951768321) ^ 893 = 60490862115 := by
        calc
          (3 : ZMod 149951768321) ^ 893 = (3 : ZMod 149951768321) ^ (446 + 446 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 446 * (3 : ZMod 149951768321) ^ 446) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 60490862115 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 149951768321) ^ 1787 = 41126164081 := by
        calc
          (3 : ZMod 149951768321) ^ 1787 = (3 : ZMod 149951768321) ^ (893 + 893 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 893 * (3 : ZMod 149951768321) ^ 893) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 41126164081 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 149951768321) ^ 3575 = 110107424425 := by
        calc
          (3 : ZMod 149951768321) ^ 3575 = (3 : ZMod 149951768321) ^ (1787 + 1787 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 1787 * (3 : ZMod 149951768321) ^ 1787) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 110107424425 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 149951768321) ^ 7150 = 99768614472 := by
        calc
          (3 : ZMod 149951768321) ^ 7150 = (3 : ZMod 149951768321) ^ (3575 + 3575) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 3575 * (3 : ZMod 149951768321) ^ 3575 := by rw [pow_add]
          _ = 99768614472 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 149951768321) ^ 14300 = 55206373628 := by
        calc
          (3 : ZMod 149951768321) ^ 14300 = (3 : ZMod 149951768321) ^ (7150 + 7150) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 7150 * (3 : ZMod 149951768321) ^ 7150 := by rw [pow_add]
          _ = 55206373628 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 149951768321) ^ 28601 = 49569609599 := by
        calc
          (3 : ZMod 149951768321) ^ 28601 = (3 : ZMod 149951768321) ^ (14300 + 14300 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 14300 * (3 : ZMod 149951768321) ^ 14300) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 49569609599 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 149951768321) ^ 57202 = 85951202856 := by
        calc
          (3 : ZMod 149951768321) ^ 57202 = (3 : ZMod 149951768321) ^ (28601 + 28601) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 28601 * (3 : ZMod 149951768321) ^ 28601 := by rw [pow_add]
          _ = 85951202856 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 149951768321) ^ 114404 = 77049321898 := by
        calc
          (3 : ZMod 149951768321) ^ 114404 = (3 : ZMod 149951768321) ^ (57202 + 57202) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 57202 * (3 : ZMod 149951768321) ^ 57202 := by rw [pow_add]
          _ = 77049321898 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 149951768321) ^ 228808 = 124623345688 := by
        calc
          (3 : ZMod 149951768321) ^ 228808 = (3 : ZMod 149951768321) ^ (114404 + 114404) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 114404 * (3 : ZMod 149951768321) ^ 114404 := by rw [pow_add]
          _ = 124623345688 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 149951768321) ^ 457616 = 11867530052 := by
        calc
          (3 : ZMod 149951768321) ^ 457616 = (3 : ZMod 149951768321) ^ (228808 + 228808) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 228808 * (3 : ZMod 149951768321) ^ 228808 := by rw [pow_add]
          _ = 11867530052 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 149951768321) ^ 915232 = 25905651225 := by
        calc
          (3 : ZMod 149951768321) ^ 915232 = (3 : ZMod 149951768321) ^ (457616 + 457616) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 457616 * (3 : ZMod 149951768321) ^ 457616 := by rw [pow_add]
          _ = 25905651225 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 149951768321) ^ 1830465 = 61814722511 := by
        calc
          (3 : ZMod 149951768321) ^ 1830465 = (3 : ZMod 149951768321) ^ (915232 + 915232 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 915232 * (3 : ZMod 149951768321) ^ 915232) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 61814722511 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 149951768321) ^ 3660931 = 14439470979 := by
        calc
          (3 : ZMod 149951768321) ^ 3660931 = (3 : ZMod 149951768321) ^ (1830465 + 1830465 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 1830465 * (3 : ZMod 149951768321) ^ 1830465) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 14439470979 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 149951768321) ^ 7321863 = 34339210339 := by
        calc
          (3 : ZMod 149951768321) ^ 7321863 = (3 : ZMod 149951768321) ^ (3660931 + 3660931 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 3660931 * (3 : ZMod 149951768321) ^ 3660931) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 34339210339 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 149951768321) ^ 14643727 = 78912612924 := by
        calc
          (3 : ZMod 149951768321) ^ 14643727 = (3 : ZMod 149951768321) ^ (7321863 + 7321863 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 7321863 * (3 : ZMod 149951768321) ^ 7321863) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 78912612924 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 149951768321) ^ 29287454 = 16204338011 := by
        calc
          (3 : ZMod 149951768321) ^ 29287454 = (3 : ZMod 149951768321) ^ (14643727 + 14643727) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 14643727 * (3 : ZMod 149951768321) ^ 14643727 := by rw [pow_add]
          _ = 16204338011 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 149951768321) ^ 58574909 = 81338687146 := by
        calc
          (3 : ZMod 149951768321) ^ 58574909 = (3 : ZMod 149951768321) ^ (29287454 + 29287454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 29287454 * (3 : ZMod 149951768321) ^ 29287454) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 81338687146 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 149951768321) ^ 117149819 = 138836931715 := by
        calc
          (3 : ZMod 149951768321) ^ 117149819 = (3 : ZMod 149951768321) ^ (58574909 + 58574909 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 58574909 * (3 : ZMod 149951768321) ^ 58574909) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 138836931715 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 149951768321) ^ 234299638 = 84910611283 := by
        calc
          (3 : ZMod 149951768321) ^ 234299638 = (3 : ZMod 149951768321) ^ (117149819 + 117149819) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 117149819 * (3 : ZMod 149951768321) ^ 117149819 := by rw [pow_add]
          _ = 84910611283 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 149951768321) ^ 468599276 = 78743164745 := by
        calc
          (3 : ZMod 149951768321) ^ 468599276 = (3 : ZMod 149951768321) ^ (234299638 + 234299638) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 234299638 * (3 : ZMod 149951768321) ^ 234299638 := by rw [pow_add]
          _ = 78743164745 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 149951768321) ^ 937198552 = 122154072468 := by
        calc
          (3 : ZMod 149951768321) ^ 937198552 = (3 : ZMod 149951768321) ^ (468599276 + 468599276) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 468599276 * (3 : ZMod 149951768321) ^ 468599276 := by rw [pow_add]
          _ = 122154072468 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 149951768321) ^ 1874397104 = 133354768997 := by
        calc
          (3 : ZMod 149951768321) ^ 1874397104 = (3 : ZMod 149951768321) ^ (937198552 + 937198552) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 937198552 * (3 : ZMod 149951768321) ^ 937198552 := by rw [pow_add]
          _ = 133354768997 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 149951768321) ^ 3748794208 = 29712087084 := by
        calc
          (3 : ZMod 149951768321) ^ 3748794208 = (3 : ZMod 149951768321) ^ (1874397104 + 1874397104) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1874397104 * (3 : ZMod 149951768321) ^ 1874397104 := by rw [pow_add]
          _ = 29712087084 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 149951768321) ^ 7497588416 = 9590412334 := by
        calc
          (3 : ZMod 149951768321) ^ 7497588416 = (3 : ZMod 149951768321) ^ (3748794208 + 3748794208) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 3748794208 * (3 : ZMod 149951768321) ^ 3748794208 := by rw [pow_add]
          _ = 9590412334 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 149951768321) ^ 14995176832 = 80846503499 := by
        calc
          (3 : ZMod 149951768321) ^ 14995176832 = (3 : ZMod 149951768321) ^ (7497588416 + 7497588416) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 7497588416 * (3 : ZMod 149951768321) ^ 7497588416 := by rw [pow_add]
          _ = 80846503499 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 149951768321) ^ 29990353664 = 110147394378 := by
        calc
          (3 : ZMod 149951768321) ^ 29990353664 = (3 : ZMod 149951768321) ^ (14995176832 + 14995176832) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 14995176832 * (3 : ZMod 149951768321) ^ 14995176832 := by rw [pow_add]
          _ = 110147394378 := by rw [factor_1_33]; decide
      change (3 : ZMod 149951768321) ^ 29990353664 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (3 : ZMod 149951768321) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 149951768321) ^ 2 = 9 := by
        calc
          (3 : ZMod 149951768321) ^ 2 = (3 : ZMod 149951768321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1 * (3 : ZMod 149951768321) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 149951768321) ^ 5 = 243 := by
        calc
          (3 : ZMod 149951768321) ^ 5 = (3 : ZMod 149951768321) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 2 * (3 : ZMod 149951768321) ^ 2) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 149951768321) ^ 11 = 177147 := by
        calc
          (3 : ZMod 149951768321) ^ 11 = (3 : ZMod 149951768321) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 5 * (3 : ZMod 149951768321) ^ 5) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 149951768321) ^ 23 = 94143178827 := by
        calc
          (3 : ZMod 149951768321) ^ 23 = (3 : ZMod 149951768321) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 11 * (3 : ZMod 149951768321) ^ 11) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 94143178827 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 149951768321) ^ 46 = 86768819866 := by
        calc
          (3 : ZMod 149951768321) ^ 46 = (3 : ZMod 149951768321) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 23 * (3 : ZMod 149951768321) ^ 23 := by rw [pow_add]
          _ = 86768819866 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 149951768321) ^ 93 = 56934839687 := by
        calc
          (3 : ZMod 149951768321) ^ 93 = (3 : ZMod 149951768321) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 46 * (3 : ZMod 149951768321) ^ 46) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 56934839687 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 149951768321) ^ 186 = 2577194766 := by
        calc
          (3 : ZMod 149951768321) ^ 186 = (3 : ZMod 149951768321) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 93 * (3 : ZMod 149951768321) ^ 93 := by rw [pow_add]
          _ = 2577194766 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 149951768321) ^ 373 = 77951548004 := by
        calc
          (3 : ZMod 149951768321) ^ 373 = (3 : ZMod 149951768321) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 186 * (3 : ZMod 149951768321) ^ 186) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 77951548004 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 149951768321) ^ 747 = 84023205650 := by
        calc
          (3 : ZMod 149951768321) ^ 747 = (3 : ZMod 149951768321) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 373 * (3 : ZMod 149951768321) ^ 373) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 84023205650 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 149951768321) ^ 1495 = 79893515305 := by
        calc
          (3 : ZMod 149951768321) ^ 1495 = (3 : ZMod 149951768321) ^ (747 + 747 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 747 * (3 : ZMod 149951768321) ^ 747) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 79893515305 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 149951768321) ^ 2990 = 79127038584 := by
        calc
          (3 : ZMod 149951768321) ^ 2990 = (3 : ZMod 149951768321) ^ (1495 + 1495) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1495 * (3 : ZMod 149951768321) ^ 1495 := by rw [pow_add]
          _ = 79127038584 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 149951768321) ^ 5980 = 74420084488 := by
        calc
          (3 : ZMod 149951768321) ^ 5980 = (3 : ZMod 149951768321) ^ (2990 + 2990) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 2990 * (3 : ZMod 149951768321) ^ 2990 := by rw [pow_add]
          _ = 74420084488 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 149951768321) ^ 11961 = 149271866957 := by
        calc
          (3 : ZMod 149951768321) ^ 11961 = (3 : ZMod 149951768321) ^ (5980 + 5980 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 5980 * (3 : ZMod 149951768321) ^ 5980) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 149271866957 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 149951768321) ^ 23923 = 4909992077 := by
        calc
          (3 : ZMod 149951768321) ^ 23923 = (3 : ZMod 149951768321) ^ (11961 + 11961 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 11961 * (3 : ZMod 149951768321) ^ 11961) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 4909992077 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 149951768321) ^ 47847 = 126379764978 := by
        calc
          (3 : ZMod 149951768321) ^ 47847 = (3 : ZMod 149951768321) ^ (23923 + 23923 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 23923 * (3 : ZMod 149951768321) ^ 23923) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 126379764978 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 149951768321) ^ 95695 = 24040553870 := by
        calc
          (3 : ZMod 149951768321) ^ 95695 = (3 : ZMod 149951768321) ^ (47847 + 47847 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 47847 * (3 : ZMod 149951768321) ^ 47847) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 24040553870 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 149951768321) ^ 191390 = 40330802832 := by
        calc
          (3 : ZMod 149951768321) ^ 191390 = (3 : ZMod 149951768321) ^ (95695 + 95695) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 95695 * (3 : ZMod 149951768321) ^ 95695 := by rw [pow_add]
          _ = 40330802832 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 149951768321) ^ 382780 = 57271548270 := by
        calc
          (3 : ZMod 149951768321) ^ 382780 = (3 : ZMod 149951768321) ^ (191390 + 191390) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 191390 * (3 : ZMod 149951768321) ^ 191390 := by rw [pow_add]
          _ = 57271548270 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 149951768321) ^ 765560 = 48597800632 := by
        calc
          (3 : ZMod 149951768321) ^ 765560 = (3 : ZMod 149951768321) ^ (382780 + 382780) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 382780 * (3 : ZMod 149951768321) ^ 382780 := by rw [pow_add]
          _ = 48597800632 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 149951768321) ^ 1531120 = 101586782644 := by
        calc
          (3 : ZMod 149951768321) ^ 1531120 = (3 : ZMod 149951768321) ^ (765560 + 765560) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 765560 * (3 : ZMod 149951768321) ^ 765560 := by rw [pow_add]
          _ = 101586782644 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 149951768321) ^ 3062240 = 65161281627 := by
        calc
          (3 : ZMod 149951768321) ^ 3062240 = (3 : ZMod 149951768321) ^ (1531120 + 1531120) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1531120 * (3 : ZMod 149951768321) ^ 1531120 := by rw [pow_add]
          _ = 65161281627 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 149951768321) ^ 6124480 = 149567619916 := by
        calc
          (3 : ZMod 149951768321) ^ 6124480 = (3 : ZMod 149951768321) ^ (3062240 + 3062240) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 3062240 * (3 : ZMod 149951768321) ^ 3062240 := by rw [pow_add]
          _ = 149567619916 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 149951768321) ^ 12248960 = 62631054789 := by
        calc
          (3 : ZMod 149951768321) ^ 12248960 = (3 : ZMod 149951768321) ^ (6124480 + 6124480) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 6124480 * (3 : ZMod 149951768321) ^ 6124480 := by rw [pow_add]
          _ = 62631054789 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 149951768321) ^ 24497920 = 102977051695 := by
        calc
          (3 : ZMod 149951768321) ^ 24497920 = (3 : ZMod 149951768321) ^ (12248960 + 12248960) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 12248960 * (3 : ZMod 149951768321) ^ 12248960 := by rw [pow_add]
          _ = 102977051695 := by rw [factor_2_23]; decide
      change (3 : ZMod 149951768321) ^ 24497920 ≠ 1
      rw [factor_2_24]
      decide
    ·
      have factor_3_0 : (3 : ZMod 149951768321) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 149951768321) ^ 3 = 27 := by
        calc
          (3 : ZMod 149951768321) ^ 3 = (3 : ZMod 149951768321) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 1 * (3 : ZMod 149951768321) ^ 1) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 149951768321) ^ 7 = 2187 := by
        calc
          (3 : ZMod 149951768321) ^ 7 = (3 : ZMod 149951768321) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 3 * (3 : ZMod 149951768321) ^ 3) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 149951768321) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 149951768321) ^ 14 = (3 : ZMod 149951768321) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 7 * (3 : ZMod 149951768321) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 149951768321) ^ 29 = 102419242186 := by
        calc
          (3 : ZMod 149951768321) ^ 29 = (3 : ZMod 149951768321) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 14 * (3 : ZMod 149951768321) ^ 14) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 102419242186 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 149951768321) ^ 59 = 121137755452 := by
        calc
          (3 : ZMod 149951768321) ^ 59 = (3 : ZMod 149951768321) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 29 * (3 : ZMod 149951768321) ^ 29) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 121137755452 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 149951768321) ^ 119 = 59088650104 := by
        calc
          (3 : ZMod 149951768321) ^ 119 = (3 : ZMod 149951768321) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 59 * (3 : ZMod 149951768321) ^ 59) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 59088650104 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 149951768321) ^ 239 = 72387465832 := by
        calc
          (3 : ZMod 149951768321) ^ 239 = (3 : ZMod 149951768321) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 119 * (3 : ZMod 149951768321) ^ 119) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 72387465832 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 149951768321) ^ 478 = 67935902123 := by
        calc
          (3 : ZMod 149951768321) ^ 478 = (3 : ZMod 149951768321) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 239 * (3 : ZMod 149951768321) ^ 239 := by rw [pow_add]
          _ = 67935902123 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 149951768321) ^ 956 = 106518472471 := by
        calc
          (3 : ZMod 149951768321) ^ 956 = (3 : ZMod 149951768321) ^ (478 + 478) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 478 * (3 : ZMod 149951768321) ^ 478 := by rw [pow_add]
          _ = 106518472471 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 149951768321) ^ 1912 = 52650304890 := by
        calc
          (3 : ZMod 149951768321) ^ 1912 = (3 : ZMod 149951768321) ^ (956 + 956) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 956 * (3 : ZMod 149951768321) ^ 956 := by rw [pow_add]
          _ = 52650304890 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 149951768321) ^ 3825 = 129493151527 := by
        calc
          (3 : ZMod 149951768321) ^ 3825 = (3 : ZMod 149951768321) ^ (1912 + 1912 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 1912 * (3 : ZMod 149951768321) ^ 1912) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 129493151527 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 149951768321) ^ 7651 = 96417108659 := by
        calc
          (3 : ZMod 149951768321) ^ 7651 = (3 : ZMod 149951768321) ^ (3825 + 3825 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 3825 * (3 : ZMod 149951768321) ^ 3825) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 96417108659 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 149951768321) ^ 15302 = 68122729823 := by
        calc
          (3 : ZMod 149951768321) ^ 15302 = (3 : ZMod 149951768321) ^ (7651 + 7651) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 7651 * (3 : ZMod 149951768321) ^ 7651 := by rw [pow_add]
          _ = 68122729823 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 149951768321) ^ 30605 = 45279112063 := by
        calc
          (3 : ZMod 149951768321) ^ 30605 = (3 : ZMod 149951768321) ^ (15302 + 15302 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = ((3 : ZMod 149951768321) ^ 15302 * (3 : ZMod 149951768321) ^ 15302) * (3 : ZMod 149951768321) := by rw [pow_succ, pow_add]
          _ = 45279112063 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 149951768321) ^ 61210 = 95655981415 := by
        calc
          (3 : ZMod 149951768321) ^ 61210 = (3 : ZMod 149951768321) ^ (30605 + 30605) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 30605 * (3 : ZMod 149951768321) ^ 30605 := by rw [pow_add]
          _ = 95655981415 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 149951768321) ^ 122420 = 46474329634 := by
        calc
          (3 : ZMod 149951768321) ^ 122420 = (3 : ZMod 149951768321) ^ (61210 + 61210) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 61210 * (3 : ZMod 149951768321) ^ 61210 := by rw [pow_add]
          _ = 46474329634 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 149951768321) ^ 244840 = 88927484793 := by
        calc
          (3 : ZMod 149951768321) ^ 244840 = (3 : ZMod 149951768321) ^ (122420 + 122420) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 122420 * (3 : ZMod 149951768321) ^ 122420 := by rw [pow_add]
          _ = 88927484793 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 149951768321) ^ 489680 = 31475394456 := by
        calc
          (3 : ZMod 149951768321) ^ 489680 = (3 : ZMod 149951768321) ^ (244840 + 244840) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 244840 * (3 : ZMod 149951768321) ^ 244840 := by rw [pow_add]
          _ = 31475394456 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 149951768321) ^ 979360 = 32370586330 := by
        calc
          (3 : ZMod 149951768321) ^ 979360 = (3 : ZMod 149951768321) ^ (489680 + 489680) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 489680 * (3 : ZMod 149951768321) ^ 489680 := by rw [pow_add]
          _ = 32370586330 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 149951768321) ^ 1958720 = 16227739542 := by
        calc
          (3 : ZMod 149951768321) ^ 1958720 = (3 : ZMod 149951768321) ^ (979360 + 979360) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 979360 * (3 : ZMod 149951768321) ^ 979360 := by rw [pow_add]
          _ = 16227739542 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 149951768321) ^ 3917440 = 13383270609 := by
        calc
          (3 : ZMod 149951768321) ^ 3917440 = (3 : ZMod 149951768321) ^ (1958720 + 1958720) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 1958720 * (3 : ZMod 149951768321) ^ 1958720 := by rw [pow_add]
          _ = 13383270609 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 149951768321) ^ 7834880 = 29668480540 := by
        calc
          (3 : ZMod 149951768321) ^ 7834880 = (3 : ZMod 149951768321) ^ (3917440 + 3917440) :=
            congrArg (fun n : ℕ => (3 : ZMod 149951768321) ^ n) (by norm_num)
          _ = (3 : ZMod 149951768321) ^ 3917440 * (3 : ZMod 149951768321) ^ 3917440 := by rw [pow_add]
          _ = 29668480540 := by rw [factor_3_21]; decide
      change (3 : ZMod 149951768321) ^ 7834880 ≠ 1
      rw [factor_3_22]
      decide

#print axioms prime_lucas_149951768321

end TotientTailPeriodKiller
end Erdos249257
