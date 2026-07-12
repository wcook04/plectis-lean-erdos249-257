import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_13127560417 : Nat.Prime 13127560417 := by
  apply lucas_primality 13127560417 (5 : ZMod 13127560417)
  ·
      have fermat_0 : (5 : ZMod 13127560417) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 13127560417) ^ 3 = 125 := by
        calc
          (5 : ZMod 13127560417) ^ 3 = (5 : ZMod 13127560417) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 1 * (5 : ZMod 13127560417) ^ 1) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 13127560417) ^ 6 = 15625 := by
        calc
          (5 : ZMod 13127560417) ^ 6 = (5 : ZMod 13127560417) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 3 * (5 : ZMod 13127560417) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 13127560417) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 13127560417) ^ 12 = (5 : ZMod 13127560417) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 6 * (5 : ZMod 13127560417) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 13127560417) ^ 24 = 6906835485 := by
        calc
          (5 : ZMod 13127560417) ^ 24 = (5 : ZMod 13127560417) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 12 * (5 : ZMod 13127560417) ^ 12 := by rw [pow_add]
          _ = 6906835485 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 13127560417) ^ 48 = 7514369307 := by
        calc
          (5 : ZMod 13127560417) ^ 48 = (5 : ZMod 13127560417) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 24 * (5 : ZMod 13127560417) ^ 24 := by rw [pow_add]
          _ = 7514369307 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 13127560417) ^ 97 = 7975287937 := by
        calc
          (5 : ZMod 13127560417) ^ 97 = (5 : ZMod 13127560417) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 48 * (5 : ZMod 13127560417) ^ 48) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7975287937 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 13127560417) ^ 195 = 8991914627 := by
        calc
          (5 : ZMod 13127560417) ^ 195 = (5 : ZMod 13127560417) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 97 * (5 : ZMod 13127560417) ^ 97) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8991914627 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 13127560417) ^ 391 = 9305429364 := by
        calc
          (5 : ZMod 13127560417) ^ 391 = (5 : ZMod 13127560417) ^ (195 + 195 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 195 * (5 : ZMod 13127560417) ^ 195) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 9305429364 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 13127560417) ^ 782 = 3002878180 := by
        calc
          (5 : ZMod 13127560417) ^ 782 = (5 : ZMod 13127560417) ^ (391 + 391) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 391 * (5 : ZMod 13127560417) ^ 391 := by rw [pow_add]
          _ = 3002878180 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 13127560417) ^ 1564 = 12044846848 := by
        calc
          (5 : ZMod 13127560417) ^ 1564 = (5 : ZMod 13127560417) ^ (782 + 782) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 782 * (5 : ZMod 13127560417) ^ 782 := by rw [pow_add]
          _ = 12044846848 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 13127560417) ^ 3129 = 8210258325 := by
        calc
          (5 : ZMod 13127560417) ^ 3129 = (5 : ZMod 13127560417) ^ (1564 + 1564 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 1564 * (5 : ZMod 13127560417) ^ 1564) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8210258325 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 13127560417) ^ 6259 = 3985891541 := by
        calc
          (5 : ZMod 13127560417) ^ 6259 = (5 : ZMod 13127560417) ^ (3129 + 3129 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 3129 * (5 : ZMod 13127560417) ^ 3129) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 3985891541 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 13127560417) ^ 12519 = 12172232151 := by
        calc
          (5 : ZMod 13127560417) ^ 12519 = (5 : ZMod 13127560417) ^ (6259 + 6259 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 6259 * (5 : ZMod 13127560417) ^ 6259) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 12172232151 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 13127560417) ^ 25038 = 6555361561 := by
        calc
          (5 : ZMod 13127560417) ^ 25038 = (5 : ZMod 13127560417) ^ (12519 + 12519) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 12519 * (5 : ZMod 13127560417) ^ 12519 := by rw [pow_add]
          _ = 6555361561 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 13127560417) ^ 50077 = 12608420096 := by
        calc
          (5 : ZMod 13127560417) ^ 50077 = (5 : ZMod 13127560417) ^ (25038 + 25038 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 25038 * (5 : ZMod 13127560417) ^ 25038) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 12608420096 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 13127560417) ^ 100155 = 12851725894 := by
        calc
          (5 : ZMod 13127560417) ^ 100155 = (5 : ZMod 13127560417) ^ (50077 + 50077 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 50077 * (5 : ZMod 13127560417) ^ 50077) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 12851725894 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 13127560417) ^ 200310 = 8796470180 := by
        calc
          (5 : ZMod 13127560417) ^ 200310 = (5 : ZMod 13127560417) ^ (100155 + 100155) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 100155 * (5 : ZMod 13127560417) ^ 100155 := by rw [pow_add]
          _ = 8796470180 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 13127560417) ^ 400621 = 6704427422 := by
        calc
          (5 : ZMod 13127560417) ^ 400621 = (5 : ZMod 13127560417) ^ (200310 + 200310 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 200310 * (5 : ZMod 13127560417) ^ 200310) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 6704427422 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 13127560417) ^ 801242 = 3397376352 := by
        calc
          (5 : ZMod 13127560417) ^ 801242 = (5 : ZMod 13127560417) ^ (400621 + 400621) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 400621 * (5 : ZMod 13127560417) ^ 400621 := by rw [pow_add]
          _ = 3397376352 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 13127560417) ^ 1602485 = 7843353504 := by
        calc
          (5 : ZMod 13127560417) ^ 1602485 = (5 : ZMod 13127560417) ^ (801242 + 801242 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 801242 * (5 : ZMod 13127560417) ^ 801242) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7843353504 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 13127560417) ^ 3204970 = 3187017989 := by
        calc
          (5 : ZMod 13127560417) ^ 3204970 = (5 : ZMod 13127560417) ^ (1602485 + 1602485) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1602485 * (5 : ZMod 13127560417) ^ 1602485 := by rw [pow_add]
          _ = 3187017989 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 13127560417) ^ 6409941 = 6161354599 := by
        calc
          (5 : ZMod 13127560417) ^ 6409941 = (5 : ZMod 13127560417) ^ (3204970 + 3204970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 3204970 * (5 : ZMod 13127560417) ^ 3204970) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 6161354599 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 13127560417) ^ 12819883 = 7689702573 := by
        calc
          (5 : ZMod 13127560417) ^ 12819883 = (5 : ZMod 13127560417) ^ (6409941 + 6409941 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 6409941 * (5 : ZMod 13127560417) ^ 6409941) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7689702573 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 13127560417) ^ 25639766 = 2838039367 := by
        calc
          (5 : ZMod 13127560417) ^ 25639766 = (5 : ZMod 13127560417) ^ (12819883 + 12819883) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 12819883 * (5 : ZMod 13127560417) ^ 12819883 := by rw [pow_add]
          _ = 2838039367 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 13127560417) ^ 51279532 = 8253655183 := by
        calc
          (5 : ZMod 13127560417) ^ 51279532 = (5 : ZMod 13127560417) ^ (25639766 + 25639766) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 25639766 * (5 : ZMod 13127560417) ^ 25639766 := by rw [pow_add]
          _ = 8253655183 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 13127560417) ^ 102559065 = 9387670669 := by
        calc
          (5 : ZMod 13127560417) ^ 102559065 = (5 : ZMod 13127560417) ^ (51279532 + 51279532 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 51279532 * (5 : ZMod 13127560417) ^ 51279532) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 9387670669 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 13127560417) ^ 205118131 = 11334273812 := by
        calc
          (5 : ZMod 13127560417) ^ 205118131 = (5 : ZMod 13127560417) ^ (102559065 + 102559065 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 102559065 * (5 : ZMod 13127560417) ^ 102559065) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 11334273812 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 13127560417) ^ 410236263 = 8059442376 := by
        calc
          (5 : ZMod 13127560417) ^ 410236263 = (5 : ZMod 13127560417) ^ (205118131 + 205118131 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 205118131 * (5 : ZMod 13127560417) ^ 205118131) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8059442376 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 13127560417) ^ 820472526 = 9366995783 := by
        calc
          (5 : ZMod 13127560417) ^ 820472526 = (5 : ZMod 13127560417) ^ (410236263 + 410236263) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 410236263 * (5 : ZMod 13127560417) ^ 410236263 := by rw [pow_add]
          _ = 9366995783 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 13127560417) ^ 1640945052 = 11801166004 := by
        calc
          (5 : ZMod 13127560417) ^ 1640945052 = (5 : ZMod 13127560417) ^ (820472526 + 820472526) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 820472526 * (5 : ZMod 13127560417) ^ 820472526 := by rw [pow_add]
          _ = 11801166004 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 13127560417) ^ 3281890104 = 6413019170 := by
        calc
          (5 : ZMod 13127560417) ^ 3281890104 = (5 : ZMod 13127560417) ^ (1640945052 + 1640945052) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1640945052 * (5 : ZMod 13127560417) ^ 1640945052 := by rw [pow_add]
          _ = 6413019170 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 13127560417) ^ 6563780208 = 13127560416 := by
        calc
          (5 : ZMod 13127560417) ^ 6563780208 = (5 : ZMod 13127560417) ^ (3281890104 + 3281890104) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 3281890104 * (5 : ZMod 13127560417) ^ 3281890104 := by rw [pow_add]
          _ = 13127560416 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 13127560417) ^ 13127560416 = 1 := by
        calc
          (5 : ZMod 13127560417) ^ 13127560416 = (5 : ZMod 13127560417) ^ (6563780208 + 6563780208) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 6563780208 * (5 : ZMod 13127560417) ^ 6563780208 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (59, 1), (772573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (59, 1), (772573, 1)] : List FactorBlock).map factorBlockValue).prod = 13127560417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 13127560417) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 13127560417) ^ 3 = 125 := by
        calc
          (5 : ZMod 13127560417) ^ 3 = (5 : ZMod 13127560417) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 1 * (5 : ZMod 13127560417) ^ 1) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 13127560417) ^ 6 = 15625 := by
        calc
          (5 : ZMod 13127560417) ^ 6 = (5 : ZMod 13127560417) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 3 * (5 : ZMod 13127560417) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 13127560417) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 13127560417) ^ 12 = (5 : ZMod 13127560417) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 6 * (5 : ZMod 13127560417) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 13127560417) ^ 24 = 6906835485 := by
        calc
          (5 : ZMod 13127560417) ^ 24 = (5 : ZMod 13127560417) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 12 * (5 : ZMod 13127560417) ^ 12 := by rw [pow_add]
          _ = 6906835485 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 13127560417) ^ 48 = 7514369307 := by
        calc
          (5 : ZMod 13127560417) ^ 48 = (5 : ZMod 13127560417) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 24 * (5 : ZMod 13127560417) ^ 24 := by rw [pow_add]
          _ = 7514369307 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 13127560417) ^ 97 = 7975287937 := by
        calc
          (5 : ZMod 13127560417) ^ 97 = (5 : ZMod 13127560417) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 48 * (5 : ZMod 13127560417) ^ 48) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7975287937 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 13127560417) ^ 195 = 8991914627 := by
        calc
          (5 : ZMod 13127560417) ^ 195 = (5 : ZMod 13127560417) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 97 * (5 : ZMod 13127560417) ^ 97) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8991914627 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 13127560417) ^ 391 = 9305429364 := by
        calc
          (5 : ZMod 13127560417) ^ 391 = (5 : ZMod 13127560417) ^ (195 + 195 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 195 * (5 : ZMod 13127560417) ^ 195) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 9305429364 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 13127560417) ^ 782 = 3002878180 := by
        calc
          (5 : ZMod 13127560417) ^ 782 = (5 : ZMod 13127560417) ^ (391 + 391) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 391 * (5 : ZMod 13127560417) ^ 391 := by rw [pow_add]
          _ = 3002878180 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 13127560417) ^ 1564 = 12044846848 := by
        calc
          (5 : ZMod 13127560417) ^ 1564 = (5 : ZMod 13127560417) ^ (782 + 782) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 782 * (5 : ZMod 13127560417) ^ 782 := by rw [pow_add]
          _ = 12044846848 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 13127560417) ^ 3129 = 8210258325 := by
        calc
          (5 : ZMod 13127560417) ^ 3129 = (5 : ZMod 13127560417) ^ (1564 + 1564 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 1564 * (5 : ZMod 13127560417) ^ 1564) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8210258325 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 13127560417) ^ 6259 = 3985891541 := by
        calc
          (5 : ZMod 13127560417) ^ 6259 = (5 : ZMod 13127560417) ^ (3129 + 3129 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 3129 * (5 : ZMod 13127560417) ^ 3129) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 3985891541 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 13127560417) ^ 12519 = 12172232151 := by
        calc
          (5 : ZMod 13127560417) ^ 12519 = (5 : ZMod 13127560417) ^ (6259 + 6259 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 6259 * (5 : ZMod 13127560417) ^ 6259) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 12172232151 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 13127560417) ^ 25038 = 6555361561 := by
        calc
          (5 : ZMod 13127560417) ^ 25038 = (5 : ZMod 13127560417) ^ (12519 + 12519) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 12519 * (5 : ZMod 13127560417) ^ 12519 := by rw [pow_add]
          _ = 6555361561 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 13127560417) ^ 50077 = 12608420096 := by
        calc
          (5 : ZMod 13127560417) ^ 50077 = (5 : ZMod 13127560417) ^ (25038 + 25038 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 25038 * (5 : ZMod 13127560417) ^ 25038) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 12608420096 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 13127560417) ^ 100155 = 12851725894 := by
        calc
          (5 : ZMod 13127560417) ^ 100155 = (5 : ZMod 13127560417) ^ (50077 + 50077 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 50077 * (5 : ZMod 13127560417) ^ 50077) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 12851725894 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 13127560417) ^ 200310 = 8796470180 := by
        calc
          (5 : ZMod 13127560417) ^ 200310 = (5 : ZMod 13127560417) ^ (100155 + 100155) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 100155 * (5 : ZMod 13127560417) ^ 100155 := by rw [pow_add]
          _ = 8796470180 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 13127560417) ^ 400621 = 6704427422 := by
        calc
          (5 : ZMod 13127560417) ^ 400621 = (5 : ZMod 13127560417) ^ (200310 + 200310 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 200310 * (5 : ZMod 13127560417) ^ 200310) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 6704427422 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 13127560417) ^ 801242 = 3397376352 := by
        calc
          (5 : ZMod 13127560417) ^ 801242 = (5 : ZMod 13127560417) ^ (400621 + 400621) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 400621 * (5 : ZMod 13127560417) ^ 400621 := by rw [pow_add]
          _ = 3397376352 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 13127560417) ^ 1602485 = 7843353504 := by
        calc
          (5 : ZMod 13127560417) ^ 1602485 = (5 : ZMod 13127560417) ^ (801242 + 801242 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 801242 * (5 : ZMod 13127560417) ^ 801242) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7843353504 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 13127560417) ^ 3204970 = 3187017989 := by
        calc
          (5 : ZMod 13127560417) ^ 3204970 = (5 : ZMod 13127560417) ^ (1602485 + 1602485) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1602485 * (5 : ZMod 13127560417) ^ 1602485 := by rw [pow_add]
          _ = 3187017989 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 13127560417) ^ 6409941 = 6161354599 := by
        calc
          (5 : ZMod 13127560417) ^ 6409941 = (5 : ZMod 13127560417) ^ (3204970 + 3204970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 3204970 * (5 : ZMod 13127560417) ^ 3204970) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 6161354599 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 13127560417) ^ 12819883 = 7689702573 := by
        calc
          (5 : ZMod 13127560417) ^ 12819883 = (5 : ZMod 13127560417) ^ (6409941 + 6409941 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 6409941 * (5 : ZMod 13127560417) ^ 6409941) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7689702573 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 13127560417) ^ 25639766 = 2838039367 := by
        calc
          (5 : ZMod 13127560417) ^ 25639766 = (5 : ZMod 13127560417) ^ (12819883 + 12819883) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 12819883 * (5 : ZMod 13127560417) ^ 12819883 := by rw [pow_add]
          _ = 2838039367 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 13127560417) ^ 51279532 = 8253655183 := by
        calc
          (5 : ZMod 13127560417) ^ 51279532 = (5 : ZMod 13127560417) ^ (25639766 + 25639766) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 25639766 * (5 : ZMod 13127560417) ^ 25639766 := by rw [pow_add]
          _ = 8253655183 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 13127560417) ^ 102559065 = 9387670669 := by
        calc
          (5 : ZMod 13127560417) ^ 102559065 = (5 : ZMod 13127560417) ^ (51279532 + 51279532 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 51279532 * (5 : ZMod 13127560417) ^ 51279532) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 9387670669 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 13127560417) ^ 205118131 = 11334273812 := by
        calc
          (5 : ZMod 13127560417) ^ 205118131 = (5 : ZMod 13127560417) ^ (102559065 + 102559065 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 102559065 * (5 : ZMod 13127560417) ^ 102559065) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 11334273812 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 13127560417) ^ 410236263 = 8059442376 := by
        calc
          (5 : ZMod 13127560417) ^ 410236263 = (5 : ZMod 13127560417) ^ (205118131 + 205118131 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 205118131 * (5 : ZMod 13127560417) ^ 205118131) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8059442376 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 13127560417) ^ 820472526 = 9366995783 := by
        calc
          (5 : ZMod 13127560417) ^ 820472526 = (5 : ZMod 13127560417) ^ (410236263 + 410236263) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 410236263 * (5 : ZMod 13127560417) ^ 410236263 := by rw [pow_add]
          _ = 9366995783 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 13127560417) ^ 1640945052 = 11801166004 := by
        calc
          (5 : ZMod 13127560417) ^ 1640945052 = (5 : ZMod 13127560417) ^ (820472526 + 820472526) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 820472526 * (5 : ZMod 13127560417) ^ 820472526 := by rw [pow_add]
          _ = 11801166004 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 13127560417) ^ 3281890104 = 6413019170 := by
        calc
          (5 : ZMod 13127560417) ^ 3281890104 = (5 : ZMod 13127560417) ^ (1640945052 + 1640945052) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1640945052 * (5 : ZMod 13127560417) ^ 1640945052 := by rw [pow_add]
          _ = 6413019170 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 13127560417) ^ 6563780208 = 13127560416 := by
        calc
          (5 : ZMod 13127560417) ^ 6563780208 = (5 : ZMod 13127560417) ^ (3281890104 + 3281890104) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 3281890104 * (5 : ZMod 13127560417) ^ 3281890104 := by rw [pow_add]
          _ = 13127560416 := by rw [factor_0_31]; decide
      change (5 : ZMod 13127560417) ^ 6563780208 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (5 : ZMod 13127560417) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 13127560417) ^ 2 = 25 := by
        calc
          (5 : ZMod 13127560417) ^ 2 = (5 : ZMod 13127560417) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1 * (5 : ZMod 13127560417) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 13127560417) ^ 4 = 625 := by
        calc
          (5 : ZMod 13127560417) ^ 4 = (5 : ZMod 13127560417) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 2 * (5 : ZMod 13127560417) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 13127560417) ^ 8 = 390625 := by
        calc
          (5 : ZMod 13127560417) ^ 8 = (5 : ZMod 13127560417) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 4 * (5 : ZMod 13127560417) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 13127560417) ^ 16 = 8184726038 := by
        calc
          (5 : ZMod 13127560417) ^ 16 = (5 : ZMod 13127560417) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 8 * (5 : ZMod 13127560417) ^ 8 := by rw [pow_add]
          _ = 8184726038 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 13127560417) ^ 32 = 6394426285 := by
        calc
          (5 : ZMod 13127560417) ^ 32 = (5 : ZMod 13127560417) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 16 * (5 : ZMod 13127560417) ^ 16 := by rw [pow_add]
          _ = 6394426285 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 13127560417) ^ 65 = 3457435784 := by
        calc
          (5 : ZMod 13127560417) ^ 65 = (5 : ZMod 13127560417) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 32 * (5 : ZMod 13127560417) ^ 32) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 3457435784 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 13127560417) ^ 130 = 6285090801 := by
        calc
          (5 : ZMod 13127560417) ^ 130 = (5 : ZMod 13127560417) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 65 * (5 : ZMod 13127560417) ^ 65 := by rw [pow_add]
          _ = 6285090801 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 13127560417) ^ 260 = 2267715905 := by
        calc
          (5 : ZMod 13127560417) ^ 260 = (5 : ZMod 13127560417) ^ (130 + 130) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 130 * (5 : ZMod 13127560417) ^ 130 := by rw [pow_add]
          _ = 2267715905 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 13127560417) ^ 521 = 8899735453 := by
        calc
          (5 : ZMod 13127560417) ^ 521 = (5 : ZMod 13127560417) ^ (260 + 260 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 260 * (5 : ZMod 13127560417) ^ 260) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8899735453 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 13127560417) ^ 1043 = 3073081321 := by
        calc
          (5 : ZMod 13127560417) ^ 1043 = (5 : ZMod 13127560417) ^ (521 + 521 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 521 * (5 : ZMod 13127560417) ^ 521) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 3073081321 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 13127560417) ^ 2086 = 9062693966 := by
        calc
          (5 : ZMod 13127560417) ^ 2086 = (5 : ZMod 13127560417) ^ (1043 + 1043) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1043 * (5 : ZMod 13127560417) ^ 1043 := by rw [pow_add]
          _ = 9062693966 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 13127560417) ^ 4173 = 2301930655 := by
        calc
          (5 : ZMod 13127560417) ^ 4173 = (5 : ZMod 13127560417) ^ (2086 + 2086 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 2086 * (5 : ZMod 13127560417) ^ 2086) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 2301930655 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 13127560417) ^ 8346 = 8839947089 := by
        calc
          (5 : ZMod 13127560417) ^ 8346 = (5 : ZMod 13127560417) ^ (4173 + 4173) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 4173 * (5 : ZMod 13127560417) ^ 4173 := by rw [pow_add]
          _ = 8839947089 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 13127560417) ^ 16692 = 2334188771 := by
        calc
          (5 : ZMod 13127560417) ^ 16692 = (5 : ZMod 13127560417) ^ (8346 + 8346) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 8346 * (5 : ZMod 13127560417) ^ 8346 := by rw [pow_add]
          _ = 2334188771 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 13127560417) ^ 33385 = 779855437 := by
        calc
          (5 : ZMod 13127560417) ^ 33385 = (5 : ZMod 13127560417) ^ (16692 + 16692 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 16692 * (5 : ZMod 13127560417) ^ 16692) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 779855437 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 13127560417) ^ 66770 = 4073137030 := by
        calc
          (5 : ZMod 13127560417) ^ 66770 = (5 : ZMod 13127560417) ^ (33385 + 33385) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 33385 * (5 : ZMod 13127560417) ^ 33385 := by rw [pow_add]
          _ = 4073137030 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 13127560417) ^ 133540 = 1199720938 := by
        calc
          (5 : ZMod 13127560417) ^ 133540 = (5 : ZMod 13127560417) ^ (66770 + 66770) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 66770 * (5 : ZMod 13127560417) ^ 66770 := by rw [pow_add]
          _ = 1199720938 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 13127560417) ^ 267080 = 3907498386 := by
        calc
          (5 : ZMod 13127560417) ^ 267080 = (5 : ZMod 13127560417) ^ (133540 + 133540) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 133540 * (5 : ZMod 13127560417) ^ 133540 := by rw [pow_add]
          _ = 3907498386 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 13127560417) ^ 534161 = 11764323788 := by
        calc
          (5 : ZMod 13127560417) ^ 534161 = (5 : ZMod 13127560417) ^ (267080 + 267080 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 267080 * (5 : ZMod 13127560417) ^ 267080) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 11764323788 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 13127560417) ^ 1068323 = 10957443890 := by
        calc
          (5 : ZMod 13127560417) ^ 1068323 = (5 : ZMod 13127560417) ^ (534161 + 534161 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 534161 * (5 : ZMod 13127560417) ^ 534161) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 10957443890 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 13127560417) ^ 2136647 = 966043007 := by
        calc
          (5 : ZMod 13127560417) ^ 2136647 = (5 : ZMod 13127560417) ^ (1068323 + 1068323 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 1068323 * (5 : ZMod 13127560417) ^ 1068323) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 966043007 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 13127560417) ^ 4273294 = 7420326195 := by
        calc
          (5 : ZMod 13127560417) ^ 4273294 = (5 : ZMod 13127560417) ^ (2136647 + 2136647) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 2136647 * (5 : ZMod 13127560417) ^ 2136647 := by rw [pow_add]
          _ = 7420326195 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 13127560417) ^ 8546588 = 1276617964 := by
        calc
          (5 : ZMod 13127560417) ^ 8546588 = (5 : ZMod 13127560417) ^ (4273294 + 4273294) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 4273294 * (5 : ZMod 13127560417) ^ 4273294 := by rw [pow_add]
          _ = 1276617964 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 13127560417) ^ 17093177 = 12313809862 := by
        calc
          (5 : ZMod 13127560417) ^ 17093177 = (5 : ZMod 13127560417) ^ (8546588 + 8546588 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 8546588 * (5 : ZMod 13127560417) ^ 8546588) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 12313809862 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 13127560417) ^ 34186355 = 5467431411 := by
        calc
          (5 : ZMod 13127560417) ^ 34186355 = (5 : ZMod 13127560417) ^ (17093177 + 17093177 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 17093177 * (5 : ZMod 13127560417) ^ 17093177) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 5467431411 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 13127560417) ^ 68372710 = 10324531196 := by
        calc
          (5 : ZMod 13127560417) ^ 68372710 = (5 : ZMod 13127560417) ^ (34186355 + 34186355) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 34186355 * (5 : ZMod 13127560417) ^ 34186355 := by rw [pow_add]
          _ = 10324531196 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 13127560417) ^ 136745421 = 11921120050 := by
        calc
          (5 : ZMod 13127560417) ^ 136745421 = (5 : ZMod 13127560417) ^ (68372710 + 68372710 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 68372710 * (5 : ZMod 13127560417) ^ 68372710) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 11921120050 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 13127560417) ^ 273490842 = 12401372278 := by
        calc
          (5 : ZMod 13127560417) ^ 273490842 = (5 : ZMod 13127560417) ^ (136745421 + 136745421) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 136745421 * (5 : ZMod 13127560417) ^ 136745421 := by rw [pow_add]
          _ = 12401372278 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 13127560417) ^ 546981684 = 1451353354 := by
        calc
          (5 : ZMod 13127560417) ^ 546981684 = (5 : ZMod 13127560417) ^ (273490842 + 273490842) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 273490842 * (5 : ZMod 13127560417) ^ 273490842 := by rw [pow_add]
          _ = 1451353354 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 13127560417) ^ 1093963368 = 5405521536 := by
        calc
          (5 : ZMod 13127560417) ^ 1093963368 = (5 : ZMod 13127560417) ^ (546981684 + 546981684) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 546981684 * (5 : ZMod 13127560417) ^ 546981684 := by rw [pow_add]
          _ = 5405521536 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 13127560417) ^ 2187926736 = 1988067769 := by
        calc
          (5 : ZMod 13127560417) ^ 2187926736 = (5 : ZMod 13127560417) ^ (1093963368 + 1093963368) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1093963368 * (5 : ZMod 13127560417) ^ 1093963368 := by rw [pow_add]
          _ = 1988067769 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 13127560417) ^ 4375853472 = 1988067768 := by
        calc
          (5 : ZMod 13127560417) ^ 4375853472 = (5 : ZMod 13127560417) ^ (2187926736 + 2187926736) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 2187926736 * (5 : ZMod 13127560417) ^ 2187926736 := by rw [pow_add]
          _ = 1988067768 := by rw [factor_1_31]; decide
      change (5 : ZMod 13127560417) ^ 4375853472 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (5 : ZMod 13127560417) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 13127560417) ^ 3 = 125 := by
        calc
          (5 : ZMod 13127560417) ^ 3 = (5 : ZMod 13127560417) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 1 * (5 : ZMod 13127560417) ^ 1) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 13127560417) ^ 6 = 15625 := by
        calc
          (5 : ZMod 13127560417) ^ 6 = (5 : ZMod 13127560417) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 3 * (5 : ZMod 13127560417) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 13127560417) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 13127560417) ^ 13 = (5 : ZMod 13127560417) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 6 * (5 : ZMod 13127560417) ^ 6) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 13127560417) ^ 26 = 2012601704 := by
        calc
          (5 : ZMod 13127560417) ^ 26 = (5 : ZMod 13127560417) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 13 * (5 : ZMod 13127560417) ^ 13 := by rw [pow_add]
          _ = 2012601704 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 13127560417) ^ 53 = 10326058779 := by
        calc
          (5 : ZMod 13127560417) ^ 53 = (5 : ZMod 13127560417) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 26 * (5 : ZMod 13127560417) ^ 26) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 10326058779 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 13127560417) ^ 106 = 4270634686 := by
        calc
          (5 : ZMod 13127560417) ^ 106 = (5 : ZMod 13127560417) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 53 * (5 : ZMod 13127560417) ^ 53 := by rw [pow_add]
          _ = 4270634686 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 13127560417) ^ 212 = 3488475994 := by
        calc
          (5 : ZMod 13127560417) ^ 212 = (5 : ZMod 13127560417) ^ (106 + 106) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 106 * (5 : ZMod 13127560417) ^ 106 := by rw [pow_add]
          _ = 3488475994 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 13127560417) ^ 424 = 3852538795 := by
        calc
          (5 : ZMod 13127560417) ^ 424 = (5 : ZMod 13127560417) ^ (212 + 212) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 212 * (5 : ZMod 13127560417) ^ 212 := by rw [pow_add]
          _ = 3852538795 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 13127560417) ^ 848 = 6999649044 := by
        calc
          (5 : ZMod 13127560417) ^ 848 = (5 : ZMod 13127560417) ^ (424 + 424) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 424 * (5 : ZMod 13127560417) ^ 424 := by rw [pow_add]
          _ = 6999649044 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 13127560417) ^ 1697 = 7899166083 := by
        calc
          (5 : ZMod 13127560417) ^ 1697 = (5 : ZMod 13127560417) ^ (848 + 848 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 848 * (5 : ZMod 13127560417) ^ 848) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7899166083 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 13127560417) ^ 3395 = 8126907679 := by
        calc
          (5 : ZMod 13127560417) ^ 3395 = (5 : ZMod 13127560417) ^ (1697 + 1697 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 1697 * (5 : ZMod 13127560417) ^ 1697) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8126907679 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 13127560417) ^ 6790 = 1201823675 := by
        calc
          (5 : ZMod 13127560417) ^ 6790 = (5 : ZMod 13127560417) ^ (3395 + 3395) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 3395 * (5 : ZMod 13127560417) ^ 3395 := by rw [pow_add]
          _ = 1201823675 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 13127560417) ^ 13580 = 2574115526 := by
        calc
          (5 : ZMod 13127560417) ^ 13580 = (5 : ZMod 13127560417) ^ (6790 + 6790) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 6790 * (5 : ZMod 13127560417) ^ 6790 := by rw [pow_add]
          _ = 2574115526 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 13127560417) ^ 27160 = 9091943753 := by
        calc
          (5 : ZMod 13127560417) ^ 27160 = (5 : ZMod 13127560417) ^ (13580 + 13580) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 13580 * (5 : ZMod 13127560417) ^ 13580 := by rw [pow_add]
          _ = 9091943753 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 13127560417) ^ 54321 = 1695396218 := by
        calc
          (5 : ZMod 13127560417) ^ 54321 = (5 : ZMod 13127560417) ^ (27160 + 27160 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 27160 * (5 : ZMod 13127560417) ^ 27160) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 1695396218 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 13127560417) ^ 108643 = 7382675073 := by
        calc
          (5 : ZMod 13127560417) ^ 108643 = (5 : ZMod 13127560417) ^ (54321 + 54321 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 54321 * (5 : ZMod 13127560417) ^ 54321) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 7382675073 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 13127560417) ^ 217286 = 7035334918 := by
        calc
          (5 : ZMod 13127560417) ^ 217286 = (5 : ZMod 13127560417) ^ (108643 + 108643) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 108643 * (5 : ZMod 13127560417) ^ 108643 := by rw [pow_add]
          _ = 7035334918 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 13127560417) ^ 434572 = 6879180552 := by
        calc
          (5 : ZMod 13127560417) ^ 434572 = (5 : ZMod 13127560417) ^ (217286 + 217286) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 217286 * (5 : ZMod 13127560417) ^ 217286 := by rw [pow_add]
          _ = 6879180552 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 13127560417) ^ 869144 = 2448106138 := by
        calc
          (5 : ZMod 13127560417) ^ 869144 = (5 : ZMod 13127560417) ^ (434572 + 434572) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 434572 * (5 : ZMod 13127560417) ^ 434572 := by rw [pow_add]
          _ = 2448106138 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 13127560417) ^ 1738289 = 8889600214 := by
        calc
          (5 : ZMod 13127560417) ^ 1738289 = (5 : ZMod 13127560417) ^ (869144 + 869144 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 869144 * (5 : ZMod 13127560417) ^ 869144) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 8889600214 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 13127560417) ^ 3476578 = 3020615818 := by
        calc
          (5 : ZMod 13127560417) ^ 3476578 = (5 : ZMod 13127560417) ^ (1738289 + 1738289) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1738289 * (5 : ZMod 13127560417) ^ 1738289 := by rw [pow_add]
          _ = 3020615818 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 13127560417) ^ 6953157 = 1793803196 := by
        calc
          (5 : ZMod 13127560417) ^ 6953157 = (5 : ZMod 13127560417) ^ (3476578 + 3476578 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 3476578 * (5 : ZMod 13127560417) ^ 3476578) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 1793803196 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 13127560417) ^ 13906314 = 4996958147 := by
        calc
          (5 : ZMod 13127560417) ^ 13906314 = (5 : ZMod 13127560417) ^ (6953157 + 6953157) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 6953157 * (5 : ZMod 13127560417) ^ 6953157 := by rw [pow_add]
          _ = 4996958147 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 13127560417) ^ 27812628 = 387715625 := by
        calc
          (5 : ZMod 13127560417) ^ 27812628 = (5 : ZMod 13127560417) ^ (13906314 + 13906314) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 13906314 * (5 : ZMod 13127560417) ^ 13906314 := by rw [pow_add]
          _ = 387715625 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 13127560417) ^ 55625256 = 340402799 := by
        calc
          (5 : ZMod 13127560417) ^ 55625256 = (5 : ZMod 13127560417) ^ (27812628 + 27812628) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 27812628 * (5 : ZMod 13127560417) ^ 27812628 := by rw [pow_add]
          _ = 340402799 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 13127560417) ^ 111250512 = 4084587975 := by
        calc
          (5 : ZMod 13127560417) ^ 111250512 = (5 : ZMod 13127560417) ^ (55625256 + 55625256) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 55625256 * (5 : ZMod 13127560417) ^ 55625256 := by rw [pow_add]
          _ = 4084587975 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 13127560417) ^ 222501024 = 2656714132 := by
        calc
          (5 : ZMod 13127560417) ^ 222501024 = (5 : ZMod 13127560417) ^ (111250512 + 111250512) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 111250512 * (5 : ZMod 13127560417) ^ 111250512 := by rw [pow_add]
          _ = 2656714132 := by rw [factor_2_26]; decide
      change (5 : ZMod 13127560417) ^ 222501024 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (5 : ZMod 13127560417) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 13127560417) ^ 2 = 25 := by
        calc
          (5 : ZMod 13127560417) ^ 2 = (5 : ZMod 13127560417) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1 * (5 : ZMod 13127560417) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 13127560417) ^ 4 = 625 := by
        calc
          (5 : ZMod 13127560417) ^ 4 = (5 : ZMod 13127560417) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 2 * (5 : ZMod 13127560417) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 13127560417) ^ 8 = 390625 := by
        calc
          (5 : ZMod 13127560417) ^ 8 = (5 : ZMod 13127560417) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 4 * (5 : ZMod 13127560417) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 13127560417) ^ 16 = 8184726038 := by
        calc
          (5 : ZMod 13127560417) ^ 16 = (5 : ZMod 13127560417) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 8 * (5 : ZMod 13127560417) ^ 8 := by rw [pow_add]
          _ = 8184726038 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 13127560417) ^ 33 = 5717010591 := by
        calc
          (5 : ZMod 13127560417) ^ 33 = (5 : ZMod 13127560417) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 16 * (5 : ZMod 13127560417) ^ 16) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 5717010591 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 13127560417) ^ 66 = 4159618503 := by
        calc
          (5 : ZMod 13127560417) ^ 66 = (5 : ZMod 13127560417) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 33 * (5 : ZMod 13127560417) ^ 33 := by rw [pow_add]
          _ = 4159618503 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 13127560417) ^ 132 = 12724105438 := by
        calc
          (5 : ZMod 13127560417) ^ 132 = (5 : ZMod 13127560417) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 66 * (5 : ZMod 13127560417) ^ 66 := by rw [pow_add]
          _ = 12724105438 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 13127560417) ^ 265 = 10857138362 := by
        calc
          (5 : ZMod 13127560417) ^ 265 = (5 : ZMod 13127560417) ^ (132 + 132 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 132 * (5 : ZMod 13127560417) ^ 132) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 10857138362 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 13127560417) ^ 531 = 5827840030 := by
        calc
          (5 : ZMod 13127560417) ^ 531 = (5 : ZMod 13127560417) ^ (265 + 265 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = ((5 : ZMod 13127560417) ^ 265 * (5 : ZMod 13127560417) ^ 265) * (5 : ZMod 13127560417) := by rw [pow_succ, pow_add]
          _ = 5827840030 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 13127560417) ^ 1062 = 8360340152 := by
        calc
          (5 : ZMod 13127560417) ^ 1062 = (5 : ZMod 13127560417) ^ (531 + 531) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 531 * (5 : ZMod 13127560417) ^ 531 := by rw [pow_add]
          _ = 8360340152 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 13127560417) ^ 2124 = 5234173414 := by
        calc
          (5 : ZMod 13127560417) ^ 2124 = (5 : ZMod 13127560417) ^ (1062 + 1062) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 1062 * (5 : ZMod 13127560417) ^ 1062 := by rw [pow_add]
          _ = 5234173414 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 13127560417) ^ 4248 = 5039335998 := by
        calc
          (5 : ZMod 13127560417) ^ 4248 = (5 : ZMod 13127560417) ^ (2124 + 2124) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 2124 * (5 : ZMod 13127560417) ^ 2124 := by rw [pow_add]
          _ = 5039335998 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 13127560417) ^ 8496 = 3941298436 := by
        calc
          (5 : ZMod 13127560417) ^ 8496 = (5 : ZMod 13127560417) ^ (4248 + 4248) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 4248 * (5 : ZMod 13127560417) ^ 4248 := by rw [pow_add]
          _ = 3941298436 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 13127560417) ^ 16992 = 7538348405 := by
        calc
          (5 : ZMod 13127560417) ^ 16992 = (5 : ZMod 13127560417) ^ (8496 + 8496) :=
            congrArg (fun n : ℕ => (5 : ZMod 13127560417) ^ n) (by norm_num)
          _ = (5 : ZMod 13127560417) ^ 8496 * (5 : ZMod 13127560417) ^ 8496 := by rw [pow_add]
          _ = 7538348405 := by rw [factor_3_13]; decide
      change (5 : ZMod 13127560417) ^ 16992 ≠ 1
      rw [factor_3_14]
      decide

#print axioms prime_lucas_13127560417

end TotientTailPeriodKiller
end Erdos249257
