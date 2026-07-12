import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_153581058871 : Nat.Prime 153581058871 := by
  apply lucas_primality 153581058871 (3 : ZMod 153581058871)
  ·
      have fermat_0 : (3 : ZMod 153581058871) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 153581058871) ^ 2 = 9 := by
        calc
          (3 : ZMod 153581058871) ^ 2 = (3 : ZMod 153581058871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1 * (3 : ZMod 153581058871) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 153581058871) ^ 4 = 81 := by
        calc
          (3 : ZMod 153581058871) ^ 4 = (3 : ZMod 153581058871) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 2 * (3 : ZMod 153581058871) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 153581058871) ^ 8 = 6561 := by
        calc
          (3 : ZMod 153581058871) ^ 8 = (3 : ZMod 153581058871) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 4 * (3 : ZMod 153581058871) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 153581058871) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 153581058871) ^ 17 = (3 : ZMod 153581058871) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 8 * (3 : ZMod 153581058871) ^ 8) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 153581058871) ^ 35 = 57874829521 := by
        calc
          (3 : ZMod 153581058871) ^ 35 = (3 : ZMod 153581058871) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 17 * (3 : ZMod 153581058871) ^ 17) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 57874829521 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 153581058871) ^ 71 = 85716841392 := by
        calc
          (3 : ZMod 153581058871) ^ 71 = (3 : ZMod 153581058871) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 35 * (3 : ZMod 153581058871) ^ 35) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 85716841392 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 153581058871) ^ 143 = 1994392079 := by
        calc
          (3 : ZMod 153581058871) ^ 143 = (3 : ZMod 153581058871) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 71 * (3 : ZMod 153581058871) ^ 71) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 1994392079 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 153581058871) ^ 286 = 81551441466 := by
        calc
          (3 : ZMod 153581058871) ^ 286 = (3 : ZMod 153581058871) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 143 * (3 : ZMod 153581058871) ^ 143 := by rw [pow_add]
          _ = 81551441466 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 153581058871) ^ 572 = 97081649740 := by
        calc
          (3 : ZMod 153581058871) ^ 572 = (3 : ZMod 153581058871) ^ (286 + 286) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 286 * (3 : ZMod 153581058871) ^ 286 := by rw [pow_add]
          _ = 97081649740 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 153581058871) ^ 1144 = 35484183838 := by
        calc
          (3 : ZMod 153581058871) ^ 1144 = (3 : ZMod 153581058871) ^ (572 + 572) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 572 * (3 : ZMod 153581058871) ^ 572 := by rw [pow_add]
          _ = 35484183838 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 153581058871) ^ 2288 = 13127429458 := by
        calc
          (3 : ZMod 153581058871) ^ 2288 = (3 : ZMod 153581058871) ^ (1144 + 1144) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1144 * (3 : ZMod 153581058871) ^ 1144 := by rw [pow_add]
          _ = 13127429458 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 153581058871) ^ 4577 = 148739427783 := by
        calc
          (3 : ZMod 153581058871) ^ 4577 = (3 : ZMod 153581058871) ^ (2288 + 2288 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2288 * (3 : ZMod 153581058871) ^ 2288) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 148739427783 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 153581058871) ^ 9154 = 42798765936 := by
        calc
          (3 : ZMod 153581058871) ^ 9154 = (3 : ZMod 153581058871) ^ (4577 + 4577) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 4577 * (3 : ZMod 153581058871) ^ 4577 := by rw [pow_add]
          _ = 42798765936 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 153581058871) ^ 18308 = 17622336751 := by
        calc
          (3 : ZMod 153581058871) ^ 18308 = (3 : ZMod 153581058871) ^ (9154 + 9154) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 9154 * (3 : ZMod 153581058871) ^ 9154 := by rw [pow_add]
          _ = 17622336751 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 153581058871) ^ 36616 = 90140250901 := by
        calc
          (3 : ZMod 153581058871) ^ 36616 = (3 : ZMod 153581058871) ^ (18308 + 18308) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 18308 * (3 : ZMod 153581058871) ^ 18308 := by rw [pow_add]
          _ = 90140250901 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 153581058871) ^ 73233 = 149677130539 := by
        calc
          (3 : ZMod 153581058871) ^ 73233 = (3 : ZMod 153581058871) ^ (36616 + 36616 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 36616 * (3 : ZMod 153581058871) ^ 36616) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 149677130539 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 153581058871) ^ 146466 = 113253310764 := by
        calc
          (3 : ZMod 153581058871) ^ 146466 = (3 : ZMod 153581058871) ^ (73233 + 73233) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 73233 * (3 : ZMod 153581058871) ^ 73233 := by rw [pow_add]
          _ = 113253310764 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 153581058871) ^ 292932 = 134456036708 := by
        calc
          (3 : ZMod 153581058871) ^ 292932 = (3 : ZMod 153581058871) ^ (146466 + 146466) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 146466 * (3 : ZMod 153581058871) ^ 146466 := by rw [pow_add]
          _ = 134456036708 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 153581058871) ^ 585865 = 125893402724 := by
        calc
          (3 : ZMod 153581058871) ^ 585865 = (3 : ZMod 153581058871) ^ (292932 + 292932 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 292932 * (3 : ZMod 153581058871) ^ 292932) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 125893402724 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 153581058871) ^ 1171730 = 73477922158 := by
        calc
          (3 : ZMod 153581058871) ^ 1171730 = (3 : ZMod 153581058871) ^ (585865 + 585865) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 585865 * (3 : ZMod 153581058871) ^ 585865 := by rw [pow_add]
          _ = 73477922158 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 153581058871) ^ 2343460 = 49846158982 := by
        calc
          (3 : ZMod 153581058871) ^ 2343460 = (3 : ZMod 153581058871) ^ (1171730 + 1171730) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1171730 * (3 : ZMod 153581058871) ^ 1171730 := by rw [pow_add]
          _ = 49846158982 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 153581058871) ^ 4686921 = 46975953118 := by
        calc
          (3 : ZMod 153581058871) ^ 4686921 = (3 : ZMod 153581058871) ^ (2343460 + 2343460 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2343460 * (3 : ZMod 153581058871) ^ 2343460) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 46975953118 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 153581058871) ^ 9373843 = 108959671916 := by
        calc
          (3 : ZMod 153581058871) ^ 9373843 = (3 : ZMod 153581058871) ^ (4686921 + 4686921 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 4686921 * (3 : ZMod 153581058871) ^ 4686921) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 108959671916 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 153581058871) ^ 18747687 = 109370458129 := by
        calc
          (3 : ZMod 153581058871) ^ 18747687 = (3 : ZMod 153581058871) ^ (9373843 + 9373843 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 9373843 * (3 : ZMod 153581058871) ^ 9373843) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 109370458129 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 153581058871) ^ 37495375 = 147070271226 := by
        calc
          (3 : ZMod 153581058871) ^ 37495375 = (3 : ZMod 153581058871) ^ (18747687 + 18747687 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 18747687 * (3 : ZMod 153581058871) ^ 18747687) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 147070271226 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 153581058871) ^ 74990751 = 31539981180 := by
        calc
          (3 : ZMod 153581058871) ^ 74990751 = (3 : ZMod 153581058871) ^ (37495375 + 37495375 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 37495375 * (3 : ZMod 153581058871) ^ 37495375) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 31539981180 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 153581058871) ^ 149981502 = 146437306316 := by
        calc
          (3 : ZMod 153581058871) ^ 149981502 = (3 : ZMod 153581058871) ^ (74990751 + 74990751) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 74990751 * (3 : ZMod 153581058871) ^ 74990751 := by rw [pow_add]
          _ = 146437306316 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 153581058871) ^ 299963005 = 98554251329 := by
        calc
          (3 : ZMod 153581058871) ^ 299963005 = (3 : ZMod 153581058871) ^ (149981502 + 149981502 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 149981502 * (3 : ZMod 153581058871) ^ 149981502) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 98554251329 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 153581058871) ^ 599926011 = 67257117605 := by
        calc
          (3 : ZMod 153581058871) ^ 599926011 = (3 : ZMod 153581058871) ^ (299963005 + 299963005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 299963005 * (3 : ZMod 153581058871) ^ 299963005) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 67257117605 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 153581058871) ^ 1199852022 = 12230089857 := by
        calc
          (3 : ZMod 153581058871) ^ 1199852022 = (3 : ZMod 153581058871) ^ (599926011 + 599926011) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 599926011 * (3 : ZMod 153581058871) ^ 599926011 := by rw [pow_add]
          _ = 12230089857 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 153581058871) ^ 2399704044 = 75919312181 := by
        calc
          (3 : ZMod 153581058871) ^ 2399704044 = (3 : ZMod 153581058871) ^ (1199852022 + 1199852022) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1199852022 * (3 : ZMod 153581058871) ^ 1199852022 := by rw [pow_add]
          _ = 75919312181 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 153581058871) ^ 4799408089 = 117286704676 := by
        calc
          (3 : ZMod 153581058871) ^ 4799408089 = (3 : ZMod 153581058871) ^ (2399704044 + 2399704044 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2399704044 * (3 : ZMod 153581058871) ^ 2399704044) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 117286704676 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 153581058871) ^ 9598816179 = 24540656949 := by
        calc
          (3 : ZMod 153581058871) ^ 9598816179 = (3 : ZMod 153581058871) ^ (4799408089 + 4799408089 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 4799408089 * (3 : ZMod 153581058871) ^ 4799408089) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 24540656949 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 153581058871) ^ 19197632358 = 141148169507 := by
        calc
          (3 : ZMod 153581058871) ^ 19197632358 = (3 : ZMod 153581058871) ^ (9598816179 + 9598816179) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 9598816179 * (3 : ZMod 153581058871) ^ 9598816179 := by rw [pow_add]
          _ = 141148169507 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 153581058871) ^ 38395264717 = 22240882383 := by
        calc
          (3 : ZMod 153581058871) ^ 38395264717 = (3 : ZMod 153581058871) ^ (19197632358 + 19197632358 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 19197632358 * (3 : ZMod 153581058871) ^ 19197632358) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 22240882383 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 153581058871) ^ 76790529435 = 153581058870 := by
        calc
          (3 : ZMod 153581058871) ^ 76790529435 = (3 : ZMod 153581058871) ^ (38395264717 + 38395264717 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 38395264717 * (3 : ZMod 153581058871) ^ 38395264717) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 153581058870 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 153581058871) ^ 153581058870 = 1 := by
        calc
          (3 : ZMod 153581058871) ^ 153581058870 = (3 : ZMod 153581058871) ^ (76790529435 + 76790529435) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 76790529435 * (3 : ZMod 153581058871) ^ 76790529435 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (67, 1), (1567, 1), (48761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (67, 1), (1567, 1), (48761, 1)] : List FactorBlock).map factorBlockValue).prod = 153581058871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 153581058871) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 153581058871) ^ 2 = 9 := by
        calc
          (3 : ZMod 153581058871) ^ 2 = (3 : ZMod 153581058871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1 * (3 : ZMod 153581058871) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 153581058871) ^ 4 = 81 := by
        calc
          (3 : ZMod 153581058871) ^ 4 = (3 : ZMod 153581058871) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 2 * (3 : ZMod 153581058871) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 153581058871) ^ 8 = 6561 := by
        calc
          (3 : ZMod 153581058871) ^ 8 = (3 : ZMod 153581058871) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 4 * (3 : ZMod 153581058871) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 153581058871) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 153581058871) ^ 17 = (3 : ZMod 153581058871) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 8 * (3 : ZMod 153581058871) ^ 8) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 153581058871) ^ 35 = 57874829521 := by
        calc
          (3 : ZMod 153581058871) ^ 35 = (3 : ZMod 153581058871) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 17 * (3 : ZMod 153581058871) ^ 17) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 57874829521 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 153581058871) ^ 71 = 85716841392 := by
        calc
          (3 : ZMod 153581058871) ^ 71 = (3 : ZMod 153581058871) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 35 * (3 : ZMod 153581058871) ^ 35) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 85716841392 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 153581058871) ^ 143 = 1994392079 := by
        calc
          (3 : ZMod 153581058871) ^ 143 = (3 : ZMod 153581058871) ^ (71 + 71 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 71 * (3 : ZMod 153581058871) ^ 71) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 1994392079 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 153581058871) ^ 286 = 81551441466 := by
        calc
          (3 : ZMod 153581058871) ^ 286 = (3 : ZMod 153581058871) ^ (143 + 143) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 143 * (3 : ZMod 153581058871) ^ 143 := by rw [pow_add]
          _ = 81551441466 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 153581058871) ^ 572 = 97081649740 := by
        calc
          (3 : ZMod 153581058871) ^ 572 = (3 : ZMod 153581058871) ^ (286 + 286) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 286 * (3 : ZMod 153581058871) ^ 286 := by rw [pow_add]
          _ = 97081649740 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 153581058871) ^ 1144 = 35484183838 := by
        calc
          (3 : ZMod 153581058871) ^ 1144 = (3 : ZMod 153581058871) ^ (572 + 572) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 572 * (3 : ZMod 153581058871) ^ 572 := by rw [pow_add]
          _ = 35484183838 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 153581058871) ^ 2288 = 13127429458 := by
        calc
          (3 : ZMod 153581058871) ^ 2288 = (3 : ZMod 153581058871) ^ (1144 + 1144) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1144 * (3 : ZMod 153581058871) ^ 1144 := by rw [pow_add]
          _ = 13127429458 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 153581058871) ^ 4577 = 148739427783 := by
        calc
          (3 : ZMod 153581058871) ^ 4577 = (3 : ZMod 153581058871) ^ (2288 + 2288 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2288 * (3 : ZMod 153581058871) ^ 2288) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 148739427783 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 153581058871) ^ 9154 = 42798765936 := by
        calc
          (3 : ZMod 153581058871) ^ 9154 = (3 : ZMod 153581058871) ^ (4577 + 4577) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 4577 * (3 : ZMod 153581058871) ^ 4577 := by rw [pow_add]
          _ = 42798765936 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 153581058871) ^ 18308 = 17622336751 := by
        calc
          (3 : ZMod 153581058871) ^ 18308 = (3 : ZMod 153581058871) ^ (9154 + 9154) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 9154 * (3 : ZMod 153581058871) ^ 9154 := by rw [pow_add]
          _ = 17622336751 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 153581058871) ^ 36616 = 90140250901 := by
        calc
          (3 : ZMod 153581058871) ^ 36616 = (3 : ZMod 153581058871) ^ (18308 + 18308) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 18308 * (3 : ZMod 153581058871) ^ 18308 := by rw [pow_add]
          _ = 90140250901 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 153581058871) ^ 73233 = 149677130539 := by
        calc
          (3 : ZMod 153581058871) ^ 73233 = (3 : ZMod 153581058871) ^ (36616 + 36616 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 36616 * (3 : ZMod 153581058871) ^ 36616) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 149677130539 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 153581058871) ^ 146466 = 113253310764 := by
        calc
          (3 : ZMod 153581058871) ^ 146466 = (3 : ZMod 153581058871) ^ (73233 + 73233) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 73233 * (3 : ZMod 153581058871) ^ 73233 := by rw [pow_add]
          _ = 113253310764 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 153581058871) ^ 292932 = 134456036708 := by
        calc
          (3 : ZMod 153581058871) ^ 292932 = (3 : ZMod 153581058871) ^ (146466 + 146466) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 146466 * (3 : ZMod 153581058871) ^ 146466 := by rw [pow_add]
          _ = 134456036708 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 153581058871) ^ 585865 = 125893402724 := by
        calc
          (3 : ZMod 153581058871) ^ 585865 = (3 : ZMod 153581058871) ^ (292932 + 292932 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 292932 * (3 : ZMod 153581058871) ^ 292932) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 125893402724 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 153581058871) ^ 1171730 = 73477922158 := by
        calc
          (3 : ZMod 153581058871) ^ 1171730 = (3 : ZMod 153581058871) ^ (585865 + 585865) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 585865 * (3 : ZMod 153581058871) ^ 585865 := by rw [pow_add]
          _ = 73477922158 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 153581058871) ^ 2343460 = 49846158982 := by
        calc
          (3 : ZMod 153581058871) ^ 2343460 = (3 : ZMod 153581058871) ^ (1171730 + 1171730) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1171730 * (3 : ZMod 153581058871) ^ 1171730 := by rw [pow_add]
          _ = 49846158982 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 153581058871) ^ 4686921 = 46975953118 := by
        calc
          (3 : ZMod 153581058871) ^ 4686921 = (3 : ZMod 153581058871) ^ (2343460 + 2343460 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2343460 * (3 : ZMod 153581058871) ^ 2343460) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 46975953118 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 153581058871) ^ 9373843 = 108959671916 := by
        calc
          (3 : ZMod 153581058871) ^ 9373843 = (3 : ZMod 153581058871) ^ (4686921 + 4686921 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 4686921 * (3 : ZMod 153581058871) ^ 4686921) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 108959671916 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 153581058871) ^ 18747687 = 109370458129 := by
        calc
          (3 : ZMod 153581058871) ^ 18747687 = (3 : ZMod 153581058871) ^ (9373843 + 9373843 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 9373843 * (3 : ZMod 153581058871) ^ 9373843) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 109370458129 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 153581058871) ^ 37495375 = 147070271226 := by
        calc
          (3 : ZMod 153581058871) ^ 37495375 = (3 : ZMod 153581058871) ^ (18747687 + 18747687 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 18747687 * (3 : ZMod 153581058871) ^ 18747687) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 147070271226 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 153581058871) ^ 74990751 = 31539981180 := by
        calc
          (3 : ZMod 153581058871) ^ 74990751 = (3 : ZMod 153581058871) ^ (37495375 + 37495375 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 37495375 * (3 : ZMod 153581058871) ^ 37495375) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 31539981180 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 153581058871) ^ 149981502 = 146437306316 := by
        calc
          (3 : ZMod 153581058871) ^ 149981502 = (3 : ZMod 153581058871) ^ (74990751 + 74990751) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 74990751 * (3 : ZMod 153581058871) ^ 74990751 := by rw [pow_add]
          _ = 146437306316 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 153581058871) ^ 299963005 = 98554251329 := by
        calc
          (3 : ZMod 153581058871) ^ 299963005 = (3 : ZMod 153581058871) ^ (149981502 + 149981502 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 149981502 * (3 : ZMod 153581058871) ^ 149981502) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 98554251329 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 153581058871) ^ 599926011 = 67257117605 := by
        calc
          (3 : ZMod 153581058871) ^ 599926011 = (3 : ZMod 153581058871) ^ (299963005 + 299963005 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 299963005 * (3 : ZMod 153581058871) ^ 299963005) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 67257117605 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 153581058871) ^ 1199852022 = 12230089857 := by
        calc
          (3 : ZMod 153581058871) ^ 1199852022 = (3 : ZMod 153581058871) ^ (599926011 + 599926011) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 599926011 * (3 : ZMod 153581058871) ^ 599926011 := by rw [pow_add]
          _ = 12230089857 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 153581058871) ^ 2399704044 = 75919312181 := by
        calc
          (3 : ZMod 153581058871) ^ 2399704044 = (3 : ZMod 153581058871) ^ (1199852022 + 1199852022) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1199852022 * (3 : ZMod 153581058871) ^ 1199852022 := by rw [pow_add]
          _ = 75919312181 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 153581058871) ^ 4799408089 = 117286704676 := by
        calc
          (3 : ZMod 153581058871) ^ 4799408089 = (3 : ZMod 153581058871) ^ (2399704044 + 2399704044 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2399704044 * (3 : ZMod 153581058871) ^ 2399704044) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 117286704676 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 153581058871) ^ 9598816179 = 24540656949 := by
        calc
          (3 : ZMod 153581058871) ^ 9598816179 = (3 : ZMod 153581058871) ^ (4799408089 + 4799408089 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 4799408089 * (3 : ZMod 153581058871) ^ 4799408089) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 24540656949 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 153581058871) ^ 19197632358 = 141148169507 := by
        calc
          (3 : ZMod 153581058871) ^ 19197632358 = (3 : ZMod 153581058871) ^ (9598816179 + 9598816179) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 9598816179 * (3 : ZMod 153581058871) ^ 9598816179 := by rw [pow_add]
          _ = 141148169507 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 153581058871) ^ 38395264717 = 22240882383 := by
        calc
          (3 : ZMod 153581058871) ^ 38395264717 = (3 : ZMod 153581058871) ^ (19197632358 + 19197632358 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 19197632358 * (3 : ZMod 153581058871) ^ 19197632358) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 22240882383 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 153581058871) ^ 76790529435 = 153581058870 := by
        calc
          (3 : ZMod 153581058871) ^ 76790529435 = (3 : ZMod 153581058871) ^ (38395264717 + 38395264717 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 38395264717 * (3 : ZMod 153581058871) ^ 38395264717) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 153581058870 := by rw [factor_0_35]; decide
      change (3 : ZMod 153581058871) ^ 76790529435 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (3 : ZMod 153581058871) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 153581058871) ^ 2 = 9 := by
        calc
          (3 : ZMod 153581058871) ^ 2 = (3 : ZMod 153581058871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1 * (3 : ZMod 153581058871) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 153581058871) ^ 5 = 243 := by
        calc
          (3 : ZMod 153581058871) ^ 5 = (3 : ZMod 153581058871) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2 * (3 : ZMod 153581058871) ^ 2) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 153581058871) ^ 11 = 177147 := by
        calc
          (3 : ZMod 153581058871) ^ 11 = (3 : ZMod 153581058871) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 5 * (3 : ZMod 153581058871) ^ 5) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 153581058871) ^ 23 = 94143178827 := by
        calc
          (3 : ZMod 153581058871) ^ 23 = (3 : ZMod 153581058871) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 11 * (3 : ZMod 153581058871) ^ 11) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 94143178827 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 153581058871) ^ 47 = 146520668946 := by
        calc
          (3 : ZMod 153581058871) ^ 47 = (3 : ZMod 153581058871) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 23 * (3 : ZMod 153581058871) ^ 23) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 146520668946 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 153581058871) ^ 95 = 47421311700 := by
        calc
          (3 : ZMod 153581058871) ^ 95 = (3 : ZMod 153581058871) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 47 * (3 : ZMod 153581058871) ^ 47) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 47421311700 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 153581058871) ^ 190 = 73190028528 := by
        calc
          (3 : ZMod 153581058871) ^ 190 = (3 : ZMod 153581058871) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 95 * (3 : ZMod 153581058871) ^ 95 := by rw [pow_add]
          _ = 73190028528 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 153581058871) ^ 381 = 49771357510 := by
        calc
          (3 : ZMod 153581058871) ^ 381 = (3 : ZMod 153581058871) ^ (190 + 190 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 190 * (3 : ZMod 153581058871) ^ 190) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 49771357510 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 153581058871) ^ 762 = 135331235899 := by
        calc
          (3 : ZMod 153581058871) ^ 762 = (3 : ZMod 153581058871) ^ (381 + 381) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 381 * (3 : ZMod 153581058871) ^ 381 := by rw [pow_add]
          _ = 135331235899 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 153581058871) ^ 1525 = 138915618900 := by
        calc
          (3 : ZMod 153581058871) ^ 1525 = (3 : ZMod 153581058871) ^ (762 + 762 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 762 * (3 : ZMod 153581058871) ^ 762) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 138915618900 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 153581058871) ^ 3051 = 134788396420 := by
        calc
          (3 : ZMod 153581058871) ^ 3051 = (3 : ZMod 153581058871) ^ (1525 + 1525 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1525 * (3 : ZMod 153581058871) ^ 1525) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 134788396420 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 153581058871) ^ 6102 = 150838372420 := by
        calc
          (3 : ZMod 153581058871) ^ 6102 = (3 : ZMod 153581058871) ^ (3051 + 3051) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 3051 * (3 : ZMod 153581058871) ^ 3051 := by rw [pow_add]
          _ = 150838372420 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 153581058871) ^ 12205 = 53407193506 := by
        calc
          (3 : ZMod 153581058871) ^ 12205 = (3 : ZMod 153581058871) ^ (6102 + 6102 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 6102 * (3 : ZMod 153581058871) ^ 6102) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 53407193506 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 153581058871) ^ 24411 = 78670695685 := by
        calc
          (3 : ZMod 153581058871) ^ 24411 = (3 : ZMod 153581058871) ^ (12205 + 12205 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 12205 * (3 : ZMod 153581058871) ^ 12205) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 78670695685 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 153581058871) ^ 48822 = 18276220893 := by
        calc
          (3 : ZMod 153581058871) ^ 48822 = (3 : ZMod 153581058871) ^ (24411 + 24411) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 24411 * (3 : ZMod 153581058871) ^ 24411 := by rw [pow_add]
          _ = 18276220893 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 153581058871) ^ 97644 = 137959510862 := by
        calc
          (3 : ZMod 153581058871) ^ 97644 = (3 : ZMod 153581058871) ^ (48822 + 48822) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 48822 * (3 : ZMod 153581058871) ^ 48822 := by rw [pow_add]
          _ = 137959510862 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 153581058871) ^ 195288 = 20720253568 := by
        calc
          (3 : ZMod 153581058871) ^ 195288 = (3 : ZMod 153581058871) ^ (97644 + 97644) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 97644 * (3 : ZMod 153581058871) ^ 97644 := by rw [pow_add]
          _ = 20720253568 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 153581058871) ^ 390576 = 19359317566 := by
        calc
          (3 : ZMod 153581058871) ^ 390576 = (3 : ZMod 153581058871) ^ (195288 + 195288) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 195288 * (3 : ZMod 153581058871) ^ 195288 := by rw [pow_add]
          _ = 19359317566 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 153581058871) ^ 781153 = 138898166078 := by
        calc
          (3 : ZMod 153581058871) ^ 781153 = (3 : ZMod 153581058871) ^ (390576 + 390576 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 390576 * (3 : ZMod 153581058871) ^ 390576) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 138898166078 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 153581058871) ^ 1562307 = 34783427884 := by
        calc
          (3 : ZMod 153581058871) ^ 1562307 = (3 : ZMod 153581058871) ^ (781153 + 781153 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 781153 * (3 : ZMod 153581058871) ^ 781153) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 34783427884 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 153581058871) ^ 3124614 = 126168948456 := by
        calc
          (3 : ZMod 153581058871) ^ 3124614 = (3 : ZMod 153581058871) ^ (1562307 + 1562307) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1562307 * (3 : ZMod 153581058871) ^ 1562307 := by rw [pow_add]
          _ = 126168948456 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 153581058871) ^ 6249229 = 42593990673 := by
        calc
          (3 : ZMod 153581058871) ^ 6249229 = (3 : ZMod 153581058871) ^ (3124614 + 3124614 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 3124614 * (3 : ZMod 153581058871) ^ 3124614) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 42593990673 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 153581058871) ^ 12498458 = 58169305271 := by
        calc
          (3 : ZMod 153581058871) ^ 12498458 = (3 : ZMod 153581058871) ^ (6249229 + 6249229) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 6249229 * (3 : ZMod 153581058871) ^ 6249229 := by rw [pow_add]
          _ = 58169305271 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 153581058871) ^ 24996917 = 74517501367 := by
        calc
          (3 : ZMod 153581058871) ^ 24996917 = (3 : ZMod 153581058871) ^ (12498458 + 12498458 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 12498458 * (3 : ZMod 153581058871) ^ 12498458) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 74517501367 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 153581058871) ^ 49993834 = 145555959725 := by
        calc
          (3 : ZMod 153581058871) ^ 49993834 = (3 : ZMod 153581058871) ^ (24996917 + 24996917) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 24996917 * (3 : ZMod 153581058871) ^ 24996917 := by rw [pow_add]
          _ = 145555959725 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 153581058871) ^ 99987668 = 119611050704 := by
        calc
          (3 : ZMod 153581058871) ^ 99987668 = (3 : ZMod 153581058871) ^ (49993834 + 49993834) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 49993834 * (3 : ZMod 153581058871) ^ 49993834 := by rw [pow_add]
          _ = 119611050704 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 153581058871) ^ 199975337 = 108980271786 := by
        calc
          (3 : ZMod 153581058871) ^ 199975337 = (3 : ZMod 153581058871) ^ (99987668 + 99987668 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 99987668 * (3 : ZMod 153581058871) ^ 99987668) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 108980271786 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 153581058871) ^ 399950674 = 148530328202 := by
        calc
          (3 : ZMod 153581058871) ^ 399950674 = (3 : ZMod 153581058871) ^ (199975337 + 199975337) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 199975337 * (3 : ZMod 153581058871) ^ 199975337 := by rw [pow_add]
          _ = 148530328202 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 153581058871) ^ 799901348 = 65286655289 := by
        calc
          (3 : ZMod 153581058871) ^ 799901348 = (3 : ZMod 153581058871) ^ (399950674 + 399950674) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 399950674 * (3 : ZMod 153581058871) ^ 399950674 := by rw [pow_add]
          _ = 65286655289 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 153581058871) ^ 1599802696 = 14414892726 := by
        calc
          (3 : ZMod 153581058871) ^ 1599802696 = (3 : ZMod 153581058871) ^ (799901348 + 799901348) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 799901348 * (3 : ZMod 153581058871) ^ 799901348 := by rw [pow_add]
          _ = 14414892726 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 153581058871) ^ 3199605393 = 131591381389 := by
        calc
          (3 : ZMod 153581058871) ^ 3199605393 = (3 : ZMod 153581058871) ^ (1599802696 + 1599802696 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1599802696 * (3 : ZMod 153581058871) ^ 1599802696) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 131591381389 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 153581058871) ^ 6399210786 = 150165141013 := by
        calc
          (3 : ZMod 153581058871) ^ 6399210786 = (3 : ZMod 153581058871) ^ (3199605393 + 3199605393) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 3199605393 * (3 : ZMod 153581058871) ^ 3199605393 := by rw [pow_add]
          _ = 150165141013 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 153581058871) ^ 12798421572 = 11120441192 := by
        calc
          (3 : ZMod 153581058871) ^ 12798421572 = (3 : ZMod 153581058871) ^ (6399210786 + 6399210786) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 6399210786 * (3 : ZMod 153581058871) ^ 6399210786 := by rw [pow_add]
          _ = 11120441192 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 153581058871) ^ 25596843145 = 33361323575 := by
        calc
          (3 : ZMod 153581058871) ^ 25596843145 = (3 : ZMod 153581058871) ^ (12798421572 + 12798421572 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 12798421572 * (3 : ZMod 153581058871) ^ 12798421572) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 33361323575 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 153581058871) ^ 51193686290 = 33361323574 := by
        calc
          (3 : ZMod 153581058871) ^ 51193686290 = (3 : ZMod 153581058871) ^ (25596843145 + 25596843145) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 25596843145 * (3 : ZMod 153581058871) ^ 25596843145 := by rw [pow_add]
          _ = 33361323574 := by rw [factor_1_34]; decide
      change (3 : ZMod 153581058871) ^ 51193686290 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (3 : ZMod 153581058871) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 153581058871) ^ 3 = 27 := by
        calc
          (3 : ZMod 153581058871) ^ 3 = (3 : ZMod 153581058871) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1 * (3 : ZMod 153581058871) ^ 1) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 153581058871) ^ 7 = 2187 := by
        calc
          (3 : ZMod 153581058871) ^ 7 = (3 : ZMod 153581058871) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 3 * (3 : ZMod 153581058871) ^ 3) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 153581058871) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 153581058871) ^ 14 = (3 : ZMod 153581058871) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 7 * (3 : ZMod 153581058871) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 153581058871) ^ 28 = 146795742053 := by
        calc
          (3 : ZMod 153581058871) ^ 28 = (3 : ZMod 153581058871) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 14 * (3 : ZMod 153581058871) ^ 14 := by rw [pow_add]
          _ = 146795742053 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 153581058871) ^ 57 = 63610153440 := by
        calc
          (3 : ZMod 153581058871) ^ 57 = (3 : ZMod 153581058871) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 28 * (3 : ZMod 153581058871) ^ 28) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 63610153440 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 153581058871) ^ 114 = 43004509960 := by
        calc
          (3 : ZMod 153581058871) ^ 114 = (3 : ZMod 153581058871) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 57 * (3 : ZMod 153581058871) ^ 57 := by rw [pow_add]
          _ = 43004509960 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 153581058871) ^ 228 = 80940209807 := by
        calc
          (3 : ZMod 153581058871) ^ 228 = (3 : ZMod 153581058871) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 114 * (3 : ZMod 153581058871) ^ 114 := by rw [pow_add]
          _ = 80940209807 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 153581058871) ^ 457 = 3563642170 := by
        calc
          (3 : ZMod 153581058871) ^ 457 = (3 : ZMod 153581058871) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 228 * (3 : ZMod 153581058871) ^ 228) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 3563642170 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 153581058871) ^ 915 = 129733082552 := by
        calc
          (3 : ZMod 153581058871) ^ 915 = (3 : ZMod 153581058871) ^ (457 + 457 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 457 * (3 : ZMod 153581058871) ^ 457) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 129733082552 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 153581058871) ^ 1830 = 98472821222 := by
        calc
          (3 : ZMod 153581058871) ^ 1830 = (3 : ZMod 153581058871) ^ (915 + 915) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 915 * (3 : ZMod 153581058871) ^ 915 := by rw [pow_add]
          _ = 98472821222 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 153581058871) ^ 3661 = 129947932178 := by
        calc
          (3 : ZMod 153581058871) ^ 3661 = (3 : ZMod 153581058871) ^ (1830 + 1830 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1830 * (3 : ZMod 153581058871) ^ 1830) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 129947932178 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 153581058871) ^ 7323 = 118274608248 := by
        calc
          (3 : ZMod 153581058871) ^ 7323 = (3 : ZMod 153581058871) ^ (3661 + 3661 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 3661 * (3 : ZMod 153581058871) ^ 3661) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 118274608248 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 153581058871) ^ 14646 = 153153048413 := by
        calc
          (3 : ZMod 153581058871) ^ 14646 = (3 : ZMod 153581058871) ^ (7323 + 7323) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 7323 * (3 : ZMod 153581058871) ^ 7323 := by rw [pow_add]
          _ = 153153048413 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 153581058871) ^ 29293 = 95138474504 := by
        calc
          (3 : ZMod 153581058871) ^ 29293 = (3 : ZMod 153581058871) ^ (14646 + 14646 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 14646 * (3 : ZMod 153581058871) ^ 14646) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 95138474504 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 153581058871) ^ 58586 = 138873653503 := by
        calc
          (3 : ZMod 153581058871) ^ 58586 = (3 : ZMod 153581058871) ^ (29293 + 29293) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 29293 * (3 : ZMod 153581058871) ^ 29293 := by rw [pow_add]
          _ = 138873653503 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 153581058871) ^ 117173 = 138872896039 := by
        calc
          (3 : ZMod 153581058871) ^ 117173 = (3 : ZMod 153581058871) ^ (58586 + 58586 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 58586 * (3 : ZMod 153581058871) ^ 58586) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 138872896039 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 153581058871) ^ 234346 = 149770495789 := by
        calc
          (3 : ZMod 153581058871) ^ 234346 = (3 : ZMod 153581058871) ^ (117173 + 117173) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 117173 * (3 : ZMod 153581058871) ^ 117173 := by rw [pow_add]
          _ = 149770495789 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 153581058871) ^ 468692 = 65141916290 := by
        calc
          (3 : ZMod 153581058871) ^ 468692 = (3 : ZMod 153581058871) ^ (234346 + 234346) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 234346 * (3 : ZMod 153581058871) ^ 234346 := by rw [pow_add]
          _ = 65141916290 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 153581058871) ^ 937384 = 99303171836 := by
        calc
          (3 : ZMod 153581058871) ^ 937384 = (3 : ZMod 153581058871) ^ (468692 + 468692) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 468692 * (3 : ZMod 153581058871) ^ 468692 := by rw [pow_add]
          _ = 99303171836 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 153581058871) ^ 1874768 = 25356474852 := by
        calc
          (3 : ZMod 153581058871) ^ 1874768 = (3 : ZMod 153581058871) ^ (937384 + 937384) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 937384 * (3 : ZMod 153581058871) ^ 937384 := by rw [pow_add]
          _ = 25356474852 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 153581058871) ^ 3749537 = 151516220329 := by
        calc
          (3 : ZMod 153581058871) ^ 3749537 = (3 : ZMod 153581058871) ^ (1874768 + 1874768 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1874768 * (3 : ZMod 153581058871) ^ 1874768) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 151516220329 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 153581058871) ^ 7499075 = 27967981231 := by
        calc
          (3 : ZMod 153581058871) ^ 7499075 = (3 : ZMod 153581058871) ^ (3749537 + 3749537 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 3749537 * (3 : ZMod 153581058871) ^ 3749537) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 27967981231 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 153581058871) ^ 14998150 = 133108380913 := by
        calc
          (3 : ZMod 153581058871) ^ 14998150 = (3 : ZMod 153581058871) ^ (7499075 + 7499075) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 7499075 * (3 : ZMod 153581058871) ^ 7499075 := by rw [pow_add]
          _ = 133108380913 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 153581058871) ^ 29996300 = 18274452151 := by
        calc
          (3 : ZMod 153581058871) ^ 29996300 = (3 : ZMod 153581058871) ^ (14998150 + 14998150) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 14998150 * (3 : ZMod 153581058871) ^ 14998150 := by rw [pow_add]
          _ = 18274452151 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 153581058871) ^ 59992601 = 129342672346 := by
        calc
          (3 : ZMod 153581058871) ^ 59992601 = (3 : ZMod 153581058871) ^ (29996300 + 29996300 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 29996300 * (3 : ZMod 153581058871) ^ 29996300) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 129342672346 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 153581058871) ^ 119985202 = 3654555061 := by
        calc
          (3 : ZMod 153581058871) ^ 119985202 = (3 : ZMod 153581058871) ^ (59992601 + 59992601) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 59992601 * (3 : ZMod 153581058871) ^ 59992601 := by rw [pow_add]
          _ = 3654555061 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 153581058871) ^ 239970404 = 134511147193 := by
        calc
          (3 : ZMod 153581058871) ^ 239970404 = (3 : ZMod 153581058871) ^ (119985202 + 119985202) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 119985202 * (3 : ZMod 153581058871) ^ 119985202 := by rw [pow_add]
          _ = 134511147193 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 153581058871) ^ 479940808 = 58543056165 := by
        calc
          (3 : ZMod 153581058871) ^ 479940808 = (3 : ZMod 153581058871) ^ (239970404 + 239970404) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 239970404 * (3 : ZMod 153581058871) ^ 239970404 := by rw [pow_add]
          _ = 58543056165 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 153581058871) ^ 959881617 = 152661035314 := by
        calc
          (3 : ZMod 153581058871) ^ 959881617 = (3 : ZMod 153581058871) ^ (479940808 + 479940808 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 479940808 * (3 : ZMod 153581058871) ^ 479940808) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 152661035314 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 153581058871) ^ 1919763235 = 75488735162 := by
        calc
          (3 : ZMod 153581058871) ^ 1919763235 = (3 : ZMod 153581058871) ^ (959881617 + 959881617 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 959881617 * (3 : ZMod 153581058871) ^ 959881617) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 75488735162 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 153581058871) ^ 3839526471 = 103513961977 := by
        calc
          (3 : ZMod 153581058871) ^ 3839526471 = (3 : ZMod 153581058871) ^ (1919763235 + 1919763235 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1919763235 * (3 : ZMod 153581058871) ^ 1919763235) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 103513961977 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 153581058871) ^ 7679052943 = 7086350589 := by
        calc
          (3 : ZMod 153581058871) ^ 7679052943 = (3 : ZMod 153581058871) ^ (3839526471 + 3839526471 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 3839526471 * (3 : ZMod 153581058871) ^ 3839526471) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 7086350589 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 153581058871) ^ 15358105887 = 145656656591 := by
        calc
          (3 : ZMod 153581058871) ^ 15358105887 = (3 : ZMod 153581058871) ^ (7679052943 + 7679052943 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 7679052943 * (3 : ZMod 153581058871) ^ 7679052943) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 145656656591 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 153581058871) ^ 30716211774 = 20030270028 := by
        calc
          (3 : ZMod 153581058871) ^ 30716211774 = (3 : ZMod 153581058871) ^ (15358105887 + 15358105887) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 15358105887 * (3 : ZMod 153581058871) ^ 15358105887 := by rw [pow_add]
          _ = 20030270028 := by rw [factor_2_33]; decide
      change (3 : ZMod 153581058871) ^ 30716211774 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (3 : ZMod 153581058871) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 153581058871) ^ 2 = 9 := by
        calc
          (3 : ZMod 153581058871) ^ 2 = (3 : ZMod 153581058871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1 * (3 : ZMod 153581058871) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 153581058871) ^ 4 = 81 := by
        calc
          (3 : ZMod 153581058871) ^ 4 = (3 : ZMod 153581058871) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 2 * (3 : ZMod 153581058871) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 153581058871) ^ 8 = 6561 := by
        calc
          (3 : ZMod 153581058871) ^ 8 = (3 : ZMod 153581058871) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 4 * (3 : ZMod 153581058871) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 153581058871) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 153581058871) ^ 17 = (3 : ZMod 153581058871) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 8 * (3 : ZMod 153581058871) ^ 8) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 153581058871) ^ 34 = 121678982421 := by
        calc
          (3 : ZMod 153581058871) ^ 34 = (3 : ZMod 153581058871) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 17 * (3 : ZMod 153581058871) ^ 17 := by rw [pow_add]
          _ = 121678982421 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 153581058871) ^ 68 = 105562070410 := by
        calc
          (3 : ZMod 153581058871) ^ 68 = (3 : ZMod 153581058871) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 34 * (3 : ZMod 153581058871) ^ 34 := by rw [pow_add]
          _ = 105562070410 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 153581058871) ^ 136 = 35042955084 := by
        calc
          (3 : ZMod 153581058871) ^ 136 = (3 : ZMod 153581058871) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 68 * (3 : ZMod 153581058871) ^ 68 := by rw [pow_add]
          _ = 35042955084 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 153581058871) ^ 273 = 18326053976 := by
        calc
          (3 : ZMod 153581058871) ^ 273 = (3 : ZMod 153581058871) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 136 * (3 : ZMod 153581058871) ^ 136) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 18326053976 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 153581058871) ^ 546 = 122462241457 := by
        calc
          (3 : ZMod 153581058871) ^ 546 = (3 : ZMod 153581058871) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 273 * (3 : ZMod 153581058871) ^ 273 := by rw [pow_add]
          _ = 122462241457 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 153581058871) ^ 1093 = 69083518960 := by
        calc
          (3 : ZMod 153581058871) ^ 1093 = (3 : ZMod 153581058871) ^ (546 + 546 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 546 * (3 : ZMod 153581058871) ^ 546) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 69083518960 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 153581058871) ^ 2186 = 145188349899 := by
        calc
          (3 : ZMod 153581058871) ^ 2186 = (3 : ZMod 153581058871) ^ (1093 + 1093) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1093 * (3 : ZMod 153581058871) ^ 1093 := by rw [pow_add]
          _ = 145188349899 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 153581058871) ^ 4372 = 37294826318 := by
        calc
          (3 : ZMod 153581058871) ^ 4372 = (3 : ZMod 153581058871) ^ (2186 + 2186) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 2186 * (3 : ZMod 153581058871) ^ 2186 := by rw [pow_add]
          _ = 37294826318 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 153581058871) ^ 8744 = 70927269968 := by
        calc
          (3 : ZMod 153581058871) ^ 8744 = (3 : ZMod 153581058871) ^ (4372 + 4372) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 4372 * (3 : ZMod 153581058871) ^ 4372 := by rw [pow_add]
          _ = 70927269968 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 153581058871) ^ 17488 = 103971879194 := by
        calc
          (3 : ZMod 153581058871) ^ 17488 = (3 : ZMod 153581058871) ^ (8744 + 8744) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 8744 * (3 : ZMod 153581058871) ^ 8744 := by rw [pow_add]
          _ = 103971879194 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 153581058871) ^ 34977 = 3903450714 := by
        calc
          (3 : ZMod 153581058871) ^ 34977 = (3 : ZMod 153581058871) ^ (17488 + 17488 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 17488 * (3 : ZMod 153581058871) ^ 17488) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 3903450714 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 153581058871) ^ 69954 = 116597506216 := by
        calc
          (3 : ZMod 153581058871) ^ 69954 = (3 : ZMod 153581058871) ^ (34977 + 34977) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 34977 * (3 : ZMod 153581058871) ^ 34977 := by rw [pow_add]
          _ = 116597506216 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 153581058871) ^ 139908 = 15987384136 := by
        calc
          (3 : ZMod 153581058871) ^ 139908 = (3 : ZMod 153581058871) ^ (69954 + 69954) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 69954 * (3 : ZMod 153581058871) ^ 69954 := by rw [pow_add]
          _ = 15987384136 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 153581058871) ^ 279816 = 91316265863 := by
        calc
          (3 : ZMod 153581058871) ^ 279816 = (3 : ZMod 153581058871) ^ (139908 + 139908) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 139908 * (3 : ZMod 153581058871) ^ 139908 := by rw [pow_add]
          _ = 91316265863 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 153581058871) ^ 559632 = 57531652541 := by
        calc
          (3 : ZMod 153581058871) ^ 559632 = (3 : ZMod 153581058871) ^ (279816 + 279816) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 279816 * (3 : ZMod 153581058871) ^ 279816 := by rw [pow_add]
          _ = 57531652541 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 153581058871) ^ 1119264 = 138923878377 := by
        calc
          (3 : ZMod 153581058871) ^ 1119264 = (3 : ZMod 153581058871) ^ (559632 + 559632) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 559632 * (3 : ZMod 153581058871) ^ 559632 := by rw [pow_add]
          _ = 138923878377 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 153581058871) ^ 2238529 = 98473899742 := by
        calc
          (3 : ZMod 153581058871) ^ 2238529 = (3 : ZMod 153581058871) ^ (1119264 + 1119264 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1119264 * (3 : ZMod 153581058871) ^ 1119264) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 98473899742 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 153581058871) ^ 4477059 = 61880778174 := by
        calc
          (3 : ZMod 153581058871) ^ 4477059 = (3 : ZMod 153581058871) ^ (2238529 + 2238529 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2238529 * (3 : ZMod 153581058871) ^ 2238529) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 61880778174 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 153581058871) ^ 8954119 = 21951555536 := by
        calc
          (3 : ZMod 153581058871) ^ 8954119 = (3 : ZMod 153581058871) ^ (4477059 + 4477059 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 4477059 * (3 : ZMod 153581058871) ^ 4477059) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 21951555536 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 153581058871) ^ 17908239 = 101219649159 := by
        calc
          (3 : ZMod 153581058871) ^ 17908239 = (3 : ZMod 153581058871) ^ (8954119 + 8954119 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 8954119 * (3 : ZMod 153581058871) ^ 8954119) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 101219649159 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 153581058871) ^ 35816478 = 94299934301 := by
        calc
          (3 : ZMod 153581058871) ^ 35816478 = (3 : ZMod 153581058871) ^ (17908239 + 17908239) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 17908239 * (3 : ZMod 153581058871) ^ 17908239 := by rw [pow_add]
          _ = 94299934301 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 153581058871) ^ 71632956 = 49276023941 := by
        calc
          (3 : ZMod 153581058871) ^ 71632956 = (3 : ZMod 153581058871) ^ (35816478 + 35816478) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 35816478 * (3 : ZMod 153581058871) ^ 35816478 := by rw [pow_add]
          _ = 49276023941 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 153581058871) ^ 143265913 = 113200011371 := by
        calc
          (3 : ZMod 153581058871) ^ 143265913 = (3 : ZMod 153581058871) ^ (71632956 + 71632956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 71632956 * (3 : ZMod 153581058871) ^ 71632956) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 113200011371 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 153581058871) ^ 286531826 = 52974457791 := by
        calc
          (3 : ZMod 153581058871) ^ 286531826 = (3 : ZMod 153581058871) ^ (143265913 + 143265913) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 143265913 * (3 : ZMod 153581058871) ^ 143265913 := by rw [pow_add]
          _ = 52974457791 := by rw [factor_3_27]; decide
      have factor_3_29 : (3 : ZMod 153581058871) ^ 573063652 = 92810267709 := by
        calc
          (3 : ZMod 153581058871) ^ 573063652 = (3 : ZMod 153581058871) ^ (286531826 + 286531826) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 286531826 * (3 : ZMod 153581058871) ^ 286531826 := by rw [pow_add]
          _ = 92810267709 := by rw [factor_3_28]; decide
      have factor_3_30 : (3 : ZMod 153581058871) ^ 1146127305 = 106048282618 := by
        calc
          (3 : ZMod 153581058871) ^ 1146127305 = (3 : ZMod 153581058871) ^ (573063652 + 573063652 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 573063652 * (3 : ZMod 153581058871) ^ 573063652) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 106048282618 := by rw [factor_3_29]; decide
      have factor_3_31 : (3 : ZMod 153581058871) ^ 2292254610 = 21781959671 := by
        calc
          (3 : ZMod 153581058871) ^ 2292254610 = (3 : ZMod 153581058871) ^ (1146127305 + 1146127305) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1146127305 * (3 : ZMod 153581058871) ^ 1146127305 := by rw [pow_add]
          _ = 21781959671 := by rw [factor_3_30]; decide
      change (3 : ZMod 153581058871) ^ 2292254610 ≠ 1
      rw [factor_3_31]
      decide
    ·
      have factor_4_0 : (3 : ZMod 153581058871) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 153581058871) ^ 2 = 9 := by
        calc
          (3 : ZMod 153581058871) ^ 2 = (3 : ZMod 153581058871) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1 * (3 : ZMod 153581058871) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 153581058871) ^ 5 = 243 := by
        calc
          (3 : ZMod 153581058871) ^ 5 = (3 : ZMod 153581058871) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 2 * (3 : ZMod 153581058871) ^ 2) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 153581058871) ^ 11 = 177147 := by
        calc
          (3 : ZMod 153581058871) ^ 11 = (3 : ZMod 153581058871) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 5 * (3 : ZMod 153581058871) ^ 5) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 153581058871) ^ 23 = 94143178827 := by
        calc
          (3 : ZMod 153581058871) ^ 23 = (3 : ZMod 153581058871) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 11 * (3 : ZMod 153581058871) ^ 11) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 94143178827 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 153581058871) ^ 46 = 48840222982 := by
        calc
          (3 : ZMod 153581058871) ^ 46 = (3 : ZMod 153581058871) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 23 * (3 : ZMod 153581058871) ^ 23 := by rw [pow_add]
          _ = 48840222982 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 153581058871) ^ 93 = 107656407214 := by
        calc
          (3 : ZMod 153581058871) ^ 93 = (3 : ZMod 153581058871) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 46 * (3 : ZMod 153581058871) ^ 46) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 107656407214 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 153581058871) ^ 186 = 86226391083 := by
        calc
          (3 : ZMod 153581058871) ^ 186 = (3 : ZMod 153581058871) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 93 * (3 : ZMod 153581058871) ^ 93 := by rw [pow_add]
          _ = 86226391083 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 153581058871) ^ 373 = 30602075187 := by
        calc
          (3 : ZMod 153581058871) ^ 373 = (3 : ZMod 153581058871) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 186 * (3 : ZMod 153581058871) ^ 186) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 30602075187 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 153581058871) ^ 747 = 151875535790 := by
        calc
          (3 : ZMod 153581058871) ^ 747 = (3 : ZMod 153581058871) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 373 * (3 : ZMod 153581058871) ^ 373) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 151875535790 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 153581058871) ^ 1495 = 13197698661 := by
        calc
          (3 : ZMod 153581058871) ^ 1495 = (3 : ZMod 153581058871) ^ (747 + 747 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 747 * (3 : ZMod 153581058871) ^ 747) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 13197698661 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 153581058871) ^ 2991 = 12547641407 := by
        calc
          (3 : ZMod 153581058871) ^ 2991 = (3 : ZMod 153581058871) ^ (1495 + 1495 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1495 * (3 : ZMod 153581058871) ^ 1495) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 12547641407 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 153581058871) ^ 5982 = 136266093748 := by
        calc
          (3 : ZMod 153581058871) ^ 5982 = (3 : ZMod 153581058871) ^ (2991 + 2991) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 2991 * (3 : ZMod 153581058871) ^ 2991 := by rw [pow_add]
          _ = 136266093748 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 153581058871) ^ 11964 = 78979023973 := by
        calc
          (3 : ZMod 153581058871) ^ 11964 = (3 : ZMod 153581058871) ^ (5982 + 5982) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 5982 * (3 : ZMod 153581058871) ^ 5982 := by rw [pow_add]
          _ = 78979023973 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 153581058871) ^ 23928 = 124398678284 := by
        calc
          (3 : ZMod 153581058871) ^ 23928 = (3 : ZMod 153581058871) ^ (11964 + 11964) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 11964 * (3 : ZMod 153581058871) ^ 11964 := by rw [pow_add]
          _ = 124398678284 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 153581058871) ^ 47856 = 50383174136 := by
        calc
          (3 : ZMod 153581058871) ^ 47856 = (3 : ZMod 153581058871) ^ (23928 + 23928) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 23928 * (3 : ZMod 153581058871) ^ 23928 := by rw [pow_add]
          _ = 50383174136 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 153581058871) ^ 95712 = 112714173171 := by
        calc
          (3 : ZMod 153581058871) ^ 95712 = (3 : ZMod 153581058871) ^ (47856 + 47856) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 47856 * (3 : ZMod 153581058871) ^ 47856 := by rw [pow_add]
          _ = 112714173171 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 153581058871) ^ 191425 = 99854060020 := by
        calc
          (3 : ZMod 153581058871) ^ 191425 = (3 : ZMod 153581058871) ^ (95712 + 95712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 95712 * (3 : ZMod 153581058871) ^ 95712) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 99854060020 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 153581058871) ^ 382850 = 54750509749 := by
        calc
          (3 : ZMod 153581058871) ^ 382850 = (3 : ZMod 153581058871) ^ (191425 + 191425) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 191425 * (3 : ZMod 153581058871) ^ 191425 := by rw [pow_add]
          _ = 54750509749 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 153581058871) ^ 765700 = 25738868771 := by
        calc
          (3 : ZMod 153581058871) ^ 765700 = (3 : ZMod 153581058871) ^ (382850 + 382850) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 382850 * (3 : ZMod 153581058871) ^ 382850 := by rw [pow_add]
          _ = 25738868771 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 153581058871) ^ 1531400 = 14645621772 := by
        calc
          (3 : ZMod 153581058871) ^ 1531400 = (3 : ZMod 153581058871) ^ (765700 + 765700) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 765700 * (3 : ZMod 153581058871) ^ 765700 := by rw [pow_add]
          _ = 14645621772 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 153581058871) ^ 3062800 = 96219620175 := by
        calc
          (3 : ZMod 153581058871) ^ 3062800 = (3 : ZMod 153581058871) ^ (1531400 + 1531400) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1531400 * (3 : ZMod 153581058871) ^ 1531400 := by rw [pow_add]
          _ = 96219620175 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 153581058871) ^ 6125600 = 109895839563 := by
        calc
          (3 : ZMod 153581058871) ^ 6125600 = (3 : ZMod 153581058871) ^ (3062800 + 3062800) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 3062800 * (3 : ZMod 153581058871) ^ 3062800 := by rw [pow_add]
          _ = 109895839563 := by rw [factor_4_21]; decide
      have factor_4_23 : (3 : ZMod 153581058871) ^ 12251201 = 139540329563 := by
        calc
          (3 : ZMod 153581058871) ^ 12251201 = (3 : ZMod 153581058871) ^ (6125600 + 6125600 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 6125600 * (3 : ZMod 153581058871) ^ 6125600) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 139540329563 := by rw [factor_4_22]; decide
      have factor_4_24 : (3 : ZMod 153581058871) ^ 24502402 = 18081232723 := by
        calc
          (3 : ZMod 153581058871) ^ 24502402 = (3 : ZMod 153581058871) ^ (12251201 + 12251201) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 12251201 * (3 : ZMod 153581058871) ^ 12251201 := by rw [pow_add]
          _ = 18081232723 := by rw [factor_4_23]; decide
      have factor_4_25 : (3 : ZMod 153581058871) ^ 49004805 = 15934712150 := by
        calc
          (3 : ZMod 153581058871) ^ 49004805 = (3 : ZMod 153581058871) ^ (24502402 + 24502402 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 24502402 * (3 : ZMod 153581058871) ^ 24502402) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 15934712150 := by rw [factor_4_24]; decide
      have factor_4_26 : (3 : ZMod 153581058871) ^ 98009610 = 93413128253 := by
        calc
          (3 : ZMod 153581058871) ^ 98009610 = (3 : ZMod 153581058871) ^ (49004805 + 49004805) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 49004805 * (3 : ZMod 153581058871) ^ 49004805 := by rw [pow_add]
          _ = 93413128253 := by rw [factor_4_25]; decide
      change (3 : ZMod 153581058871) ^ 98009610 ≠ 1
      rw [factor_4_26]
      decide
    ·
      have factor_5_0 : (3 : ZMod 153581058871) ^ 1 = 3 := by norm_num
      have factor_5_1 : (3 : ZMod 153581058871) ^ 3 = 27 := by
        calc
          (3 : ZMod 153581058871) ^ 3 = (3 : ZMod 153581058871) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1 * (3 : ZMod 153581058871) ^ 1) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_5_0]; decide
      have factor_5_2 : (3 : ZMod 153581058871) ^ 6 = 729 := by
        calc
          (3 : ZMod 153581058871) ^ 6 = (3 : ZMod 153581058871) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 3 * (3 : ZMod 153581058871) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_5_1]; decide
      have factor_5_3 : (3 : ZMod 153581058871) ^ 12 = 531441 := by
        calc
          (3 : ZMod 153581058871) ^ 12 = (3 : ZMod 153581058871) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 6 * (3 : ZMod 153581058871) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_5_2]; decide
      have factor_5_4 : (3 : ZMod 153581058871) ^ 24 = 128848477610 := by
        calc
          (3 : ZMod 153581058871) ^ 24 = (3 : ZMod 153581058871) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 12 * (3 : ZMod 153581058871) ^ 12 := by rw [pow_add]
          _ = 128848477610 := by rw [factor_5_3]; decide
      have factor_5_5 : (3 : ZMod 153581058871) ^ 48 = 132399889096 := by
        calc
          (3 : ZMod 153581058871) ^ 48 = (3 : ZMod 153581058871) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 24 * (3 : ZMod 153581058871) ^ 24 := by rw [pow_add]
          _ = 132399889096 := by rw [factor_5_4]; decide
      have factor_5_6 : (3 : ZMod 153581058871) ^ 96 = 142263935100 := by
        calc
          (3 : ZMod 153581058871) ^ 96 = (3 : ZMod 153581058871) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 48 * (3 : ZMod 153581058871) ^ 48 := by rw [pow_add]
          _ = 142263935100 := by rw [factor_5_5]; decide
      have factor_5_7 : (3 : ZMod 153581058871) ^ 192 = 44386021268 := by
        calc
          (3 : ZMod 153581058871) ^ 192 = (3 : ZMod 153581058871) ^ (96 + 96) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 96 * (3 : ZMod 153581058871) ^ 96 := by rw [pow_add]
          _ = 44386021268 := by rw [factor_5_6]; decide
      have factor_5_8 : (3 : ZMod 153581058871) ^ 384 = 115178181802 := by
        calc
          (3 : ZMod 153581058871) ^ 384 = (3 : ZMod 153581058871) ^ (192 + 192) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 192 * (3 : ZMod 153581058871) ^ 192 := by rw [pow_add]
          _ = 115178181802 := by rw [factor_5_7]; decide
      have factor_5_9 : (3 : ZMod 153581058871) ^ 768 = 57431175189 := by
        calc
          (3 : ZMod 153581058871) ^ 768 = (3 : ZMod 153581058871) ^ (384 + 384) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 384 * (3 : ZMod 153581058871) ^ 384 := by rw [pow_add]
          _ = 57431175189 := by rw [factor_5_8]; decide
      have factor_5_10 : (3 : ZMod 153581058871) ^ 1537 = 115491957297 := by
        calc
          (3 : ZMod 153581058871) ^ 1537 = (3 : ZMod 153581058871) ^ (768 + 768 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 768 * (3 : ZMod 153581058871) ^ 768) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 115491957297 := by rw [factor_5_9]; decide
      have factor_5_11 : (3 : ZMod 153581058871) ^ 3075 = 30661532111 := by
        calc
          (3 : ZMod 153581058871) ^ 3075 = (3 : ZMod 153581058871) ^ (1537 + 1537 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 1537 * (3 : ZMod 153581058871) ^ 1537) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 30661532111 := by rw [factor_5_10]; decide
      have factor_5_12 : (3 : ZMod 153581058871) ^ 6151 = 106556873322 := by
        calc
          (3 : ZMod 153581058871) ^ 6151 = (3 : ZMod 153581058871) ^ (3075 + 3075 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 3075 * (3 : ZMod 153581058871) ^ 3075) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 106556873322 := by rw [factor_5_11]; decide
      have factor_5_13 : (3 : ZMod 153581058871) ^ 12303 = 33158720096 := by
        calc
          (3 : ZMod 153581058871) ^ 12303 = (3 : ZMod 153581058871) ^ (6151 + 6151 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 6151 * (3 : ZMod 153581058871) ^ 6151) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 33158720096 := by rw [factor_5_12]; decide
      have factor_5_14 : (3 : ZMod 153581058871) ^ 24606 = 124668241454 := by
        calc
          (3 : ZMod 153581058871) ^ 24606 = (3 : ZMod 153581058871) ^ (12303 + 12303) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 12303 * (3 : ZMod 153581058871) ^ 12303 := by rw [pow_add]
          _ = 124668241454 := by rw [factor_5_13]; decide
      have factor_5_15 : (3 : ZMod 153581058871) ^ 49213 = 89463319157 := by
        calc
          (3 : ZMod 153581058871) ^ 49213 = (3 : ZMod 153581058871) ^ (24606 + 24606 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 24606 * (3 : ZMod 153581058871) ^ 24606) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 89463319157 := by rw [factor_5_14]; decide
      have factor_5_16 : (3 : ZMod 153581058871) ^ 98427 = 24895824815 := by
        calc
          (3 : ZMod 153581058871) ^ 98427 = (3 : ZMod 153581058871) ^ (49213 + 49213 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 49213 * (3 : ZMod 153581058871) ^ 49213) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 24895824815 := by rw [factor_5_15]; decide
      have factor_5_17 : (3 : ZMod 153581058871) ^ 196854 = 96132390111 := by
        calc
          (3 : ZMod 153581058871) ^ 196854 = (3 : ZMod 153581058871) ^ (98427 + 98427) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 98427 * (3 : ZMod 153581058871) ^ 98427 := by rw [pow_add]
          _ = 96132390111 := by rw [factor_5_16]; decide
      have factor_5_18 : (3 : ZMod 153581058871) ^ 393708 = 61592667419 := by
        calc
          (3 : ZMod 153581058871) ^ 393708 = (3 : ZMod 153581058871) ^ (196854 + 196854) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 196854 * (3 : ZMod 153581058871) ^ 196854 := by rw [pow_add]
          _ = 61592667419 := by rw [factor_5_17]; decide
      have factor_5_19 : (3 : ZMod 153581058871) ^ 787417 = 111480830969 := by
        calc
          (3 : ZMod 153581058871) ^ 787417 = (3 : ZMod 153581058871) ^ (393708 + 393708 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 393708 * (3 : ZMod 153581058871) ^ 393708) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 111480830969 := by rw [factor_5_18]; decide
      have factor_5_20 : (3 : ZMod 153581058871) ^ 1574835 = 52017976844 := by
        calc
          (3 : ZMod 153581058871) ^ 1574835 = (3 : ZMod 153581058871) ^ (787417 + 787417 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = ((3 : ZMod 153581058871) ^ 787417 * (3 : ZMod 153581058871) ^ 787417) * (3 : ZMod 153581058871) := by rw [pow_succ, pow_add]
          _ = 52017976844 := by rw [factor_5_19]; decide
      have factor_5_21 : (3 : ZMod 153581058871) ^ 3149670 = 111256896684 := by
        calc
          (3 : ZMod 153581058871) ^ 3149670 = (3 : ZMod 153581058871) ^ (1574835 + 1574835) :=
            congrArg (fun n : ℕ => (3 : ZMod 153581058871) ^ n) (by norm_num)
          _ = (3 : ZMod 153581058871) ^ 1574835 * (3 : ZMod 153581058871) ^ 1574835 := by rw [pow_add]
          _ = 111256896684 := by rw [factor_5_20]; decide
      change (3 : ZMod 153581058871) ^ 3149670 ≠ 1
      rw [factor_5_21]
      decide

#print axioms prime_lucas_153581058871

end TotientTailPeriodKiller
end Erdos249257
