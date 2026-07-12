import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime781174033

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_382775276171 : Nat.Prime 382775276171 := by
  apply lucas_primality 382775276171 (2 : ZMod 382775276171)
  ·
      have fermat_0 : (2 : ZMod 382775276171) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 382775276171) ^ 2 = 4 := by
        calc
          (2 : ZMod 382775276171) ^ 2 = (2 : ZMod 382775276171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 1 * (2 : ZMod 382775276171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 382775276171) ^ 5 = 32 := by
        calc
          (2 : ZMod 382775276171) ^ 5 = (2 : ZMod 382775276171) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2 * (2 : ZMod 382775276171) ^ 2) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 382775276171) ^ 11 = 2048 := by
        calc
          (2 : ZMod 382775276171) ^ 11 = (2 : ZMod 382775276171) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 5 * (2 : ZMod 382775276171) ^ 5) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 382775276171) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 382775276171) ^ 22 = (2 : ZMod 382775276171) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 11 * (2 : ZMod 382775276171) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 382775276171) ^ 44 = 367298616721 := by
        calc
          (2 : ZMod 382775276171) ^ 44 = (2 : ZMod 382775276171) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 22 * (2 : ZMod 382775276171) ^ 22 := by rw [pow_add]
          _ = 367298616721 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 382775276171) ^ 89 = 9584593171 := by
        calc
          (2 : ZMod 382775276171) ^ 89 = (2 : ZMod 382775276171) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 44 * (2 : ZMod 382775276171) ^ 44) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 9584593171 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 382775276171) ^ 178 = 164598227976 := by
        calc
          (2 : ZMod 382775276171) ^ 178 = (2 : ZMod 382775276171) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 89 * (2 : ZMod 382775276171) ^ 89 := by rw [pow_add]
          _ = 164598227976 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 382775276171) ^ 356 = 10923312329 := by
        calc
          (2 : ZMod 382775276171) ^ 356 = (2 : ZMod 382775276171) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 178 * (2 : ZMod 382775276171) ^ 178 := by rw [pow_add]
          _ = 10923312329 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 382775276171) ^ 712 = 278028353089 := by
        calc
          (2 : ZMod 382775276171) ^ 712 = (2 : ZMod 382775276171) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 356 * (2 : ZMod 382775276171) ^ 356 := by rw [pow_add]
          _ = 278028353089 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 382775276171) ^ 1425 = 28268245543 := by
        calc
          (2 : ZMod 382775276171) ^ 1425 = (2 : ZMod 382775276171) ^ (712 + 712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 712 * (2 : ZMod 382775276171) ^ 712) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 28268245543 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 382775276171) ^ 2851 = 227996716772 := by
        calc
          (2 : ZMod 382775276171) ^ 2851 = (2 : ZMod 382775276171) ^ (1425 + 1425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1425 * (2 : ZMod 382775276171) ^ 1425) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 227996716772 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 382775276171) ^ 5703 = 120161854118 := by
        calc
          (2 : ZMod 382775276171) ^ 5703 = (2 : ZMod 382775276171) ^ (2851 + 2851 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2851 * (2 : ZMod 382775276171) ^ 2851) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 120161854118 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 382775276171) ^ 11407 = 18992224142 := by
        calc
          (2 : ZMod 382775276171) ^ 11407 = (2 : ZMod 382775276171) ^ (5703 + 5703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 5703 * (2 : ZMod 382775276171) ^ 5703) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 18992224142 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 382775276171) ^ 22815 = 187596033520 := by
        calc
          (2 : ZMod 382775276171) ^ 22815 = (2 : ZMod 382775276171) ^ (11407 + 11407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 11407 * (2 : ZMod 382775276171) ^ 11407) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 187596033520 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 382775276171) ^ 45630 = 258215196766 := by
        calc
          (2 : ZMod 382775276171) ^ 45630 = (2 : ZMod 382775276171) ^ (22815 + 22815) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 22815 * (2 : ZMod 382775276171) ^ 22815 := by rw [pow_add]
          _ = 258215196766 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 382775276171) ^ 91260 = 304147471045 := by
        calc
          (2 : ZMod 382775276171) ^ 91260 = (2 : ZMod 382775276171) ^ (45630 + 45630) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 45630 * (2 : ZMod 382775276171) ^ 45630 := by rw [pow_add]
          _ = 304147471045 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 382775276171) ^ 182521 = 89652936548 := by
        calc
          (2 : ZMod 382775276171) ^ 182521 = (2 : ZMod 382775276171) ^ (91260 + 91260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 91260 * (2 : ZMod 382775276171) ^ 91260) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 89652936548 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 382775276171) ^ 365042 = 2607458607 := by
        calc
          (2 : ZMod 382775276171) ^ 365042 = (2 : ZMod 382775276171) ^ (182521 + 182521) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 182521 * (2 : ZMod 382775276171) ^ 182521 := by rw [pow_add]
          _ = 2607458607 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 382775276171) ^ 730085 = 189108593552 := by
        calc
          (2 : ZMod 382775276171) ^ 730085 = (2 : ZMod 382775276171) ^ (365042 + 365042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 365042 * (2 : ZMod 382775276171) ^ 365042) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 189108593552 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 382775276171) ^ 1460171 = 86296512731 := by
        calc
          (2 : ZMod 382775276171) ^ 1460171 = (2 : ZMod 382775276171) ^ (730085 + 730085 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 730085 * (2 : ZMod 382775276171) ^ 730085) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 86296512731 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 382775276171) ^ 2920343 = 314960697575 := by
        calc
          (2 : ZMod 382775276171) ^ 2920343 = (2 : ZMod 382775276171) ^ (1460171 + 1460171 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1460171 * (2 : ZMod 382775276171) ^ 1460171) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 314960697575 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 382775276171) ^ 5840687 = 323487073359 := by
        calc
          (2 : ZMod 382775276171) ^ 5840687 = (2 : ZMod 382775276171) ^ (2920343 + 2920343 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2920343 * (2 : ZMod 382775276171) ^ 2920343) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 323487073359 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 382775276171) ^ 11681374 = 184148875342 := by
        calc
          (2 : ZMod 382775276171) ^ 11681374 = (2 : ZMod 382775276171) ^ (5840687 + 5840687) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 5840687 * (2 : ZMod 382775276171) ^ 5840687 := by rw [pow_add]
          _ = 184148875342 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 382775276171) ^ 23362748 = 32090346631 := by
        calc
          (2 : ZMod 382775276171) ^ 23362748 = (2 : ZMod 382775276171) ^ (11681374 + 11681374) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 11681374 * (2 : ZMod 382775276171) ^ 11681374 := by rw [pow_add]
          _ = 32090346631 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 382775276171) ^ 46725497 = 333547910591 := by
        calc
          (2 : ZMod 382775276171) ^ 46725497 = (2 : ZMod 382775276171) ^ (23362748 + 23362748 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 23362748 * (2 : ZMod 382775276171) ^ 23362748) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 333547910591 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 382775276171) ^ 93450995 = 188332891917 := by
        calc
          (2 : ZMod 382775276171) ^ 93450995 = (2 : ZMod 382775276171) ^ (46725497 + 46725497 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 46725497 * (2 : ZMod 382775276171) ^ 46725497) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 188332891917 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 382775276171) ^ 186901990 = 193883915749 := by
        calc
          (2 : ZMod 382775276171) ^ 186901990 = (2 : ZMod 382775276171) ^ (93450995 + 93450995) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 93450995 * (2 : ZMod 382775276171) ^ 93450995 := by rw [pow_add]
          _ = 193883915749 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 382775276171) ^ 373803980 = 294523482474 := by
        calc
          (2 : ZMod 382775276171) ^ 373803980 = (2 : ZMod 382775276171) ^ (186901990 + 186901990) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 186901990 * (2 : ZMod 382775276171) ^ 186901990 := by rw [pow_add]
          _ = 294523482474 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 382775276171) ^ 747607961 = 108710713663 := by
        calc
          (2 : ZMod 382775276171) ^ 747607961 = (2 : ZMod 382775276171) ^ (373803980 + 373803980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 373803980 * (2 : ZMod 382775276171) ^ 373803980) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 108710713663 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 382775276171) ^ 1495215922 = 201868903527 := by
        calc
          (2 : ZMod 382775276171) ^ 1495215922 = (2 : ZMod 382775276171) ^ (747607961 + 747607961) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 747607961 * (2 : ZMod 382775276171) ^ 747607961 := by rw [pow_add]
          _ = 201868903527 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 382775276171) ^ 2990431845 = 73990441730 := by
        calc
          (2 : ZMod 382775276171) ^ 2990431845 = (2 : ZMod 382775276171) ^ (1495215922 + 1495215922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1495215922 * (2 : ZMod 382775276171) ^ 1495215922) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 73990441730 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 382775276171) ^ 5980863690 = 371262260107 := by
        calc
          (2 : ZMod 382775276171) ^ 5980863690 = (2 : ZMod 382775276171) ^ (2990431845 + 2990431845) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 2990431845 * (2 : ZMod 382775276171) ^ 2990431845 := by rw [pow_add]
          _ = 371262260107 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 382775276171) ^ 11961727380 = 275701498808 := by
        calc
          (2 : ZMod 382775276171) ^ 11961727380 = (2 : ZMod 382775276171) ^ (5980863690 + 5980863690) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 5980863690 * (2 : ZMod 382775276171) ^ 5980863690 := by rw [pow_add]
          _ = 275701498808 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 382775276171) ^ 23923454760 = 54877484890 := by
        calc
          (2 : ZMod 382775276171) ^ 23923454760 = (2 : ZMod 382775276171) ^ (11961727380 + 11961727380) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 11961727380 * (2 : ZMod 382775276171) ^ 11961727380 := by rw [pow_add]
          _ = 54877484890 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 382775276171) ^ 47846909521 = 324923543499 := by
        calc
          (2 : ZMod 382775276171) ^ 47846909521 = (2 : ZMod 382775276171) ^ (23923454760 + 23923454760 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 23923454760 * (2 : ZMod 382775276171) ^ 23923454760) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 324923543499 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 382775276171) ^ 95693819042 = 102908827173 := by
        calc
          (2 : ZMod 382775276171) ^ 95693819042 = (2 : ZMod 382775276171) ^ (47846909521 + 47846909521) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 47846909521 * (2 : ZMod 382775276171) ^ 47846909521 := by rw [pow_add]
          _ = 102908827173 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 382775276171) ^ 191387638085 = 382775276170 := by
        calc
          (2 : ZMod 382775276171) ^ 191387638085 = (2 : ZMod 382775276171) ^ (95693819042 + 95693819042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 95693819042 * (2 : ZMod 382775276171) ^ 95693819042) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 382775276170 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 382775276171) ^ 382775276170 = 1 := by
        calc
          (2 : ZMod 382775276171) ^ 382775276170 = (2 : ZMod 382775276171) ^ (191387638085 + 191387638085) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 191387638085 * (2 : ZMod 382775276171) ^ 191387638085 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 2), (781174033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 2), (781174033, 1)] : List FactorBlock).map factorBlockValue).prod = 382775276171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_781174033) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 382775276171) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 382775276171) ^ 2 = 4 := by
        calc
          (2 : ZMod 382775276171) ^ 2 = (2 : ZMod 382775276171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 1 * (2 : ZMod 382775276171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 382775276171) ^ 5 = 32 := by
        calc
          (2 : ZMod 382775276171) ^ 5 = (2 : ZMod 382775276171) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2 * (2 : ZMod 382775276171) ^ 2) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 382775276171) ^ 11 = 2048 := by
        calc
          (2 : ZMod 382775276171) ^ 11 = (2 : ZMod 382775276171) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 5 * (2 : ZMod 382775276171) ^ 5) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 382775276171) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 382775276171) ^ 22 = (2 : ZMod 382775276171) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 11 * (2 : ZMod 382775276171) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 382775276171) ^ 44 = 367298616721 := by
        calc
          (2 : ZMod 382775276171) ^ 44 = (2 : ZMod 382775276171) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 22 * (2 : ZMod 382775276171) ^ 22 := by rw [pow_add]
          _ = 367298616721 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 382775276171) ^ 89 = 9584593171 := by
        calc
          (2 : ZMod 382775276171) ^ 89 = (2 : ZMod 382775276171) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 44 * (2 : ZMod 382775276171) ^ 44) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 9584593171 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 382775276171) ^ 178 = 164598227976 := by
        calc
          (2 : ZMod 382775276171) ^ 178 = (2 : ZMod 382775276171) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 89 * (2 : ZMod 382775276171) ^ 89 := by rw [pow_add]
          _ = 164598227976 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 382775276171) ^ 356 = 10923312329 := by
        calc
          (2 : ZMod 382775276171) ^ 356 = (2 : ZMod 382775276171) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 178 * (2 : ZMod 382775276171) ^ 178 := by rw [pow_add]
          _ = 10923312329 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 382775276171) ^ 712 = 278028353089 := by
        calc
          (2 : ZMod 382775276171) ^ 712 = (2 : ZMod 382775276171) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 356 * (2 : ZMod 382775276171) ^ 356 := by rw [pow_add]
          _ = 278028353089 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 382775276171) ^ 1425 = 28268245543 := by
        calc
          (2 : ZMod 382775276171) ^ 1425 = (2 : ZMod 382775276171) ^ (712 + 712 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 712 * (2 : ZMod 382775276171) ^ 712) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 28268245543 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 382775276171) ^ 2851 = 227996716772 := by
        calc
          (2 : ZMod 382775276171) ^ 2851 = (2 : ZMod 382775276171) ^ (1425 + 1425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1425 * (2 : ZMod 382775276171) ^ 1425) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 227996716772 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 382775276171) ^ 5703 = 120161854118 := by
        calc
          (2 : ZMod 382775276171) ^ 5703 = (2 : ZMod 382775276171) ^ (2851 + 2851 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2851 * (2 : ZMod 382775276171) ^ 2851) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 120161854118 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 382775276171) ^ 11407 = 18992224142 := by
        calc
          (2 : ZMod 382775276171) ^ 11407 = (2 : ZMod 382775276171) ^ (5703 + 5703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 5703 * (2 : ZMod 382775276171) ^ 5703) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 18992224142 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 382775276171) ^ 22815 = 187596033520 := by
        calc
          (2 : ZMod 382775276171) ^ 22815 = (2 : ZMod 382775276171) ^ (11407 + 11407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 11407 * (2 : ZMod 382775276171) ^ 11407) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 187596033520 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 382775276171) ^ 45630 = 258215196766 := by
        calc
          (2 : ZMod 382775276171) ^ 45630 = (2 : ZMod 382775276171) ^ (22815 + 22815) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 22815 * (2 : ZMod 382775276171) ^ 22815 := by rw [pow_add]
          _ = 258215196766 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 382775276171) ^ 91260 = 304147471045 := by
        calc
          (2 : ZMod 382775276171) ^ 91260 = (2 : ZMod 382775276171) ^ (45630 + 45630) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 45630 * (2 : ZMod 382775276171) ^ 45630 := by rw [pow_add]
          _ = 304147471045 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 382775276171) ^ 182521 = 89652936548 := by
        calc
          (2 : ZMod 382775276171) ^ 182521 = (2 : ZMod 382775276171) ^ (91260 + 91260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 91260 * (2 : ZMod 382775276171) ^ 91260) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 89652936548 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 382775276171) ^ 365042 = 2607458607 := by
        calc
          (2 : ZMod 382775276171) ^ 365042 = (2 : ZMod 382775276171) ^ (182521 + 182521) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 182521 * (2 : ZMod 382775276171) ^ 182521 := by rw [pow_add]
          _ = 2607458607 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 382775276171) ^ 730085 = 189108593552 := by
        calc
          (2 : ZMod 382775276171) ^ 730085 = (2 : ZMod 382775276171) ^ (365042 + 365042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 365042 * (2 : ZMod 382775276171) ^ 365042) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 189108593552 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 382775276171) ^ 1460171 = 86296512731 := by
        calc
          (2 : ZMod 382775276171) ^ 1460171 = (2 : ZMod 382775276171) ^ (730085 + 730085 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 730085 * (2 : ZMod 382775276171) ^ 730085) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 86296512731 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 382775276171) ^ 2920343 = 314960697575 := by
        calc
          (2 : ZMod 382775276171) ^ 2920343 = (2 : ZMod 382775276171) ^ (1460171 + 1460171 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1460171 * (2 : ZMod 382775276171) ^ 1460171) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 314960697575 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 382775276171) ^ 5840687 = 323487073359 := by
        calc
          (2 : ZMod 382775276171) ^ 5840687 = (2 : ZMod 382775276171) ^ (2920343 + 2920343 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2920343 * (2 : ZMod 382775276171) ^ 2920343) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 323487073359 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 382775276171) ^ 11681374 = 184148875342 := by
        calc
          (2 : ZMod 382775276171) ^ 11681374 = (2 : ZMod 382775276171) ^ (5840687 + 5840687) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 5840687 * (2 : ZMod 382775276171) ^ 5840687 := by rw [pow_add]
          _ = 184148875342 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 382775276171) ^ 23362748 = 32090346631 := by
        calc
          (2 : ZMod 382775276171) ^ 23362748 = (2 : ZMod 382775276171) ^ (11681374 + 11681374) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 11681374 * (2 : ZMod 382775276171) ^ 11681374 := by rw [pow_add]
          _ = 32090346631 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 382775276171) ^ 46725497 = 333547910591 := by
        calc
          (2 : ZMod 382775276171) ^ 46725497 = (2 : ZMod 382775276171) ^ (23362748 + 23362748 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 23362748 * (2 : ZMod 382775276171) ^ 23362748) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 333547910591 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 382775276171) ^ 93450995 = 188332891917 := by
        calc
          (2 : ZMod 382775276171) ^ 93450995 = (2 : ZMod 382775276171) ^ (46725497 + 46725497 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 46725497 * (2 : ZMod 382775276171) ^ 46725497) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 188332891917 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 382775276171) ^ 186901990 = 193883915749 := by
        calc
          (2 : ZMod 382775276171) ^ 186901990 = (2 : ZMod 382775276171) ^ (93450995 + 93450995) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 93450995 * (2 : ZMod 382775276171) ^ 93450995 := by rw [pow_add]
          _ = 193883915749 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 382775276171) ^ 373803980 = 294523482474 := by
        calc
          (2 : ZMod 382775276171) ^ 373803980 = (2 : ZMod 382775276171) ^ (186901990 + 186901990) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 186901990 * (2 : ZMod 382775276171) ^ 186901990 := by rw [pow_add]
          _ = 294523482474 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 382775276171) ^ 747607961 = 108710713663 := by
        calc
          (2 : ZMod 382775276171) ^ 747607961 = (2 : ZMod 382775276171) ^ (373803980 + 373803980 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 373803980 * (2 : ZMod 382775276171) ^ 373803980) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 108710713663 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 382775276171) ^ 1495215922 = 201868903527 := by
        calc
          (2 : ZMod 382775276171) ^ 1495215922 = (2 : ZMod 382775276171) ^ (747607961 + 747607961) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 747607961 * (2 : ZMod 382775276171) ^ 747607961 := by rw [pow_add]
          _ = 201868903527 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 382775276171) ^ 2990431845 = 73990441730 := by
        calc
          (2 : ZMod 382775276171) ^ 2990431845 = (2 : ZMod 382775276171) ^ (1495215922 + 1495215922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1495215922 * (2 : ZMod 382775276171) ^ 1495215922) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 73990441730 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 382775276171) ^ 5980863690 = 371262260107 := by
        calc
          (2 : ZMod 382775276171) ^ 5980863690 = (2 : ZMod 382775276171) ^ (2990431845 + 2990431845) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 2990431845 * (2 : ZMod 382775276171) ^ 2990431845 := by rw [pow_add]
          _ = 371262260107 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 382775276171) ^ 11961727380 = 275701498808 := by
        calc
          (2 : ZMod 382775276171) ^ 11961727380 = (2 : ZMod 382775276171) ^ (5980863690 + 5980863690) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 5980863690 * (2 : ZMod 382775276171) ^ 5980863690 := by rw [pow_add]
          _ = 275701498808 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 382775276171) ^ 23923454760 = 54877484890 := by
        calc
          (2 : ZMod 382775276171) ^ 23923454760 = (2 : ZMod 382775276171) ^ (11961727380 + 11961727380) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 11961727380 * (2 : ZMod 382775276171) ^ 11961727380 := by rw [pow_add]
          _ = 54877484890 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 382775276171) ^ 47846909521 = 324923543499 := by
        calc
          (2 : ZMod 382775276171) ^ 47846909521 = (2 : ZMod 382775276171) ^ (23923454760 + 23923454760 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 23923454760 * (2 : ZMod 382775276171) ^ 23923454760) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 324923543499 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 382775276171) ^ 95693819042 = 102908827173 := by
        calc
          (2 : ZMod 382775276171) ^ 95693819042 = (2 : ZMod 382775276171) ^ (47846909521 + 47846909521) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 47846909521 * (2 : ZMod 382775276171) ^ 47846909521 := by rw [pow_add]
          _ = 102908827173 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 382775276171) ^ 191387638085 = 382775276170 := by
        calc
          (2 : ZMod 382775276171) ^ 191387638085 = (2 : ZMod 382775276171) ^ (95693819042 + 95693819042 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 95693819042 * (2 : ZMod 382775276171) ^ 95693819042) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 382775276170 := by rw [factor_0_36]; decide
      change (2 : ZMod 382775276171) ^ 191387638085 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (2 : ZMod 382775276171) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 382775276171) ^ 2 = 4 := by
        calc
          (2 : ZMod 382775276171) ^ 2 = (2 : ZMod 382775276171) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 1 * (2 : ZMod 382775276171) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 382775276171) ^ 4 = 16 := by
        calc
          (2 : ZMod 382775276171) ^ 4 = (2 : ZMod 382775276171) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 2 * (2 : ZMod 382775276171) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 382775276171) ^ 8 = 256 := by
        calc
          (2 : ZMod 382775276171) ^ 8 = (2 : ZMod 382775276171) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 4 * (2 : ZMod 382775276171) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 382775276171) ^ 17 = 131072 := by
        calc
          (2 : ZMod 382775276171) ^ 17 = (2 : ZMod 382775276171) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 8 * (2 : ZMod 382775276171) ^ 8) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 382775276171) ^ 35 = 34359738368 := by
        calc
          (2 : ZMod 382775276171) ^ 35 = (2 : ZMod 382775276171) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 17 * (2 : ZMod 382775276171) ^ 17) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 34359738368 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 382775276171) ^ 71 = 120889120003 := by
        calc
          (2 : ZMod 382775276171) ^ 71 = (2 : ZMod 382775276171) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 35 * (2 : ZMod 382775276171) ^ 35) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 120889120003 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 382775276171) ^ 142 = 247160877622 := by
        calc
          (2 : ZMod 382775276171) ^ 142 = (2 : ZMod 382775276171) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 71 * (2 : ZMod 382775276171) ^ 71 := by rw [pow_add]
          _ = 247160877622 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 382775276171) ^ 285 = 336053639950 := by
        calc
          (2 : ZMod 382775276171) ^ 285 = (2 : ZMod 382775276171) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 142 * (2 : ZMod 382775276171) ^ 142) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 336053639950 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 382775276171) ^ 570 = 278103686876 := by
        calc
          (2 : ZMod 382775276171) ^ 570 = (2 : ZMod 382775276171) ^ (285 + 285) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 285 * (2 : ZMod 382775276171) ^ 285 := by rw [pow_add]
          _ = 278103686876 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 382775276171) ^ 1140 = 306292876498 := by
        calc
          (2 : ZMod 382775276171) ^ 1140 = (2 : ZMod 382775276171) ^ (570 + 570) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 570 * (2 : ZMod 382775276171) ^ 570 := by rw [pow_add]
          _ = 306292876498 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 382775276171) ^ 2281 = 229077424212 := by
        calc
          (2 : ZMod 382775276171) ^ 2281 = (2 : ZMod 382775276171) ^ (1140 + 1140 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1140 * (2 : ZMod 382775276171) ^ 1140) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 229077424212 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 382775276171) ^ 4563 = 97264941569 := by
        calc
          (2 : ZMod 382775276171) ^ 4563 = (2 : ZMod 382775276171) ^ (2281 + 2281 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2281 * (2 : ZMod 382775276171) ^ 2281) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 97264941569 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 382775276171) ^ 9126 = 30759319697 := by
        calc
          (2 : ZMod 382775276171) ^ 9126 = (2 : ZMod 382775276171) ^ (4563 + 4563) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 4563 * (2 : ZMod 382775276171) ^ 4563 := by rw [pow_add]
          _ = 30759319697 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 382775276171) ^ 18252 = 107650869908 := by
        calc
          (2 : ZMod 382775276171) ^ 18252 = (2 : ZMod 382775276171) ^ (9126 + 9126) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 9126 * (2 : ZMod 382775276171) ^ 9126 := by rw [pow_add]
          _ = 107650869908 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 382775276171) ^ 36504 = 340553157356 := by
        calc
          (2 : ZMod 382775276171) ^ 36504 = (2 : ZMod 382775276171) ^ (18252 + 18252) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 18252 * (2 : ZMod 382775276171) ^ 18252 := by rw [pow_add]
          _ = 340553157356 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 382775276171) ^ 73008 = 164214883894 := by
        calc
          (2 : ZMod 382775276171) ^ 73008 = (2 : ZMod 382775276171) ^ (36504 + 36504) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 36504 * (2 : ZMod 382775276171) ^ 36504 := by rw [pow_add]
          _ = 164214883894 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 382775276171) ^ 146017 = 271785869638 := by
        calc
          (2 : ZMod 382775276171) ^ 146017 = (2 : ZMod 382775276171) ^ (73008 + 73008 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 73008 * (2 : ZMod 382775276171) ^ 73008) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 271785869638 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 382775276171) ^ 292034 = 243474374125 := by
        calc
          (2 : ZMod 382775276171) ^ 292034 = (2 : ZMod 382775276171) ^ (146017 + 146017) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 146017 * (2 : ZMod 382775276171) ^ 146017 := by rw [pow_add]
          _ = 243474374125 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 382775276171) ^ 584068 = 193965470376 := by
        calc
          (2 : ZMod 382775276171) ^ 584068 = (2 : ZMod 382775276171) ^ (292034 + 292034) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 292034 * (2 : ZMod 382775276171) ^ 292034 := by rw [pow_add]
          _ = 193965470376 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 382775276171) ^ 1168137 = 90097323919 := by
        calc
          (2 : ZMod 382775276171) ^ 1168137 = (2 : ZMod 382775276171) ^ (584068 + 584068 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 584068 * (2 : ZMod 382775276171) ^ 584068) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 90097323919 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 382775276171) ^ 2336274 = 290697192437 := by
        calc
          (2 : ZMod 382775276171) ^ 2336274 = (2 : ZMod 382775276171) ^ (1168137 + 1168137) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 1168137 * (2 : ZMod 382775276171) ^ 1168137 := by rw [pow_add]
          _ = 290697192437 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 382775276171) ^ 4672549 = 272389657272 := by
        calc
          (2 : ZMod 382775276171) ^ 4672549 = (2 : ZMod 382775276171) ^ (2336274 + 2336274 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 2336274 * (2 : ZMod 382775276171) ^ 2336274) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 272389657272 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 382775276171) ^ 9345099 = 234777897710 := by
        calc
          (2 : ZMod 382775276171) ^ 9345099 = (2 : ZMod 382775276171) ^ (4672549 + 4672549 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 4672549 * (2 : ZMod 382775276171) ^ 4672549) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 234777897710 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 382775276171) ^ 18690199 = 132601713766 := by
        calc
          (2 : ZMod 382775276171) ^ 18690199 = (2 : ZMod 382775276171) ^ (9345099 + 9345099 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 9345099 * (2 : ZMod 382775276171) ^ 9345099) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 132601713766 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 382775276171) ^ 37380398 = 4815578589 := by
        calc
          (2 : ZMod 382775276171) ^ 37380398 = (2 : ZMod 382775276171) ^ (18690199 + 18690199) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 18690199 * (2 : ZMod 382775276171) ^ 18690199 := by rw [pow_add]
          _ = 4815578589 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 382775276171) ^ 74760796 = 102479163201 := by
        calc
          (2 : ZMod 382775276171) ^ 74760796 = (2 : ZMod 382775276171) ^ (37380398 + 37380398) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 37380398 * (2 : ZMod 382775276171) ^ 37380398 := by rw [pow_add]
          _ = 102479163201 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 382775276171) ^ 149521592 = 271310086842 := by
        calc
          (2 : ZMod 382775276171) ^ 149521592 = (2 : ZMod 382775276171) ^ (74760796 + 74760796) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 74760796 * (2 : ZMod 382775276171) ^ 74760796 := by rw [pow_add]
          _ = 271310086842 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 382775276171) ^ 299043184 = 146038011478 := by
        calc
          (2 : ZMod 382775276171) ^ 299043184 = (2 : ZMod 382775276171) ^ (149521592 + 149521592) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 149521592 * (2 : ZMod 382775276171) ^ 149521592 := by rw [pow_add]
          _ = 146038011478 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 382775276171) ^ 598086369 = 106341438433 := by
        calc
          (2 : ZMod 382775276171) ^ 598086369 = (2 : ZMod 382775276171) ^ (299043184 + 299043184 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 299043184 * (2 : ZMod 382775276171) ^ 299043184) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 106341438433 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 382775276171) ^ 1196172738 = 277458252471 := by
        calc
          (2 : ZMod 382775276171) ^ 1196172738 = (2 : ZMod 382775276171) ^ (598086369 + 598086369) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 598086369 * (2 : ZMod 382775276171) ^ 598086369 := by rw [pow_add]
          _ = 277458252471 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 382775276171) ^ 2392345476 = 262911949518 := by
        calc
          (2 : ZMod 382775276171) ^ 2392345476 = (2 : ZMod 382775276171) ^ (1196172738 + 1196172738) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 1196172738 * (2 : ZMod 382775276171) ^ 1196172738 := by rw [pow_add]
          _ = 262911949518 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 382775276171) ^ 4784690952 = 181272408949 := by
        calc
          (2 : ZMod 382775276171) ^ 4784690952 = (2 : ZMod 382775276171) ^ (2392345476 + 2392345476) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 2392345476 * (2 : ZMod 382775276171) ^ 2392345476 := by rw [pow_add]
          _ = 181272408949 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 382775276171) ^ 9569381904 = 167345072204 := by
        calc
          (2 : ZMod 382775276171) ^ 9569381904 = (2 : ZMod 382775276171) ^ (4784690952 + 4784690952) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 4784690952 * (2 : ZMod 382775276171) ^ 4784690952 := by rw [pow_add]
          _ = 167345072204 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 382775276171) ^ 19138763808 = 235894378118 := by
        calc
          (2 : ZMod 382775276171) ^ 19138763808 = (2 : ZMod 382775276171) ^ (9569381904 + 9569381904) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 9569381904 * (2 : ZMod 382775276171) ^ 9569381904 := by rw [pow_add]
          _ = 235894378118 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 382775276171) ^ 38277527617 = 147190204200 := by
        calc
          (2 : ZMod 382775276171) ^ 38277527617 = (2 : ZMod 382775276171) ^ (19138763808 + 19138763808 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 19138763808 * (2 : ZMod 382775276171) ^ 19138763808) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 147190204200 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 382775276171) ^ 76555055234 = 348740642695 := by
        calc
          (2 : ZMod 382775276171) ^ 76555055234 = (2 : ZMod 382775276171) ^ (38277527617 + 38277527617) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 38277527617 * (2 : ZMod 382775276171) ^ 38277527617 := by rw [pow_add]
          _ = 348740642695 := by rw [factor_1_35]; decide
      change (2 : ZMod 382775276171) ^ 76555055234 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (2 : ZMod 382775276171) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 382775276171) ^ 3 = 8 := by
        calc
          (2 : ZMod 382775276171) ^ 3 = (2 : ZMod 382775276171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1 * (2 : ZMod 382775276171) ^ 1) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 382775276171) ^ 6 = 64 := by
        calc
          (2 : ZMod 382775276171) ^ 6 = (2 : ZMod 382775276171) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 3 * (2 : ZMod 382775276171) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 382775276171) ^ 12 = 4096 := by
        calc
          (2 : ZMod 382775276171) ^ 12 = (2 : ZMod 382775276171) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 6 * (2 : ZMod 382775276171) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 382775276171) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 382775276171) ^ 25 = (2 : ZMod 382775276171) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 12 * (2 : ZMod 382775276171) ^ 12) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 382775276171) ^ 50 = 157819623713 := by
        calc
          (2 : ZMod 382775276171) ^ 50 = (2 : ZMod 382775276171) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 25 * (2 : ZMod 382775276171) ^ 25 := by rw [pow_add]
          _ = 157819623713 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 382775276171) ^ 101 = 215415458974 := by
        calc
          (2 : ZMod 382775276171) ^ 101 = (2 : ZMod 382775276171) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 50 * (2 : ZMod 382775276171) ^ 50) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 215415458974 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 382775276171) ^ 203 = 277091503531 := by
        calc
          (2 : ZMod 382775276171) ^ 203 = (2 : ZMod 382775276171) ^ (101 + 101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 101 * (2 : ZMod 382775276171) ^ 101) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 277091503531 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 382775276171) ^ 407 = 239779608507 := by
        calc
          (2 : ZMod 382775276171) ^ 407 = (2 : ZMod 382775276171) ^ (203 + 203 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 203 * (2 : ZMod 382775276171) ^ 203) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 239779608507 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 382775276171) ^ 814 = 144914724419 := by
        calc
          (2 : ZMod 382775276171) ^ 814 = (2 : ZMod 382775276171) ^ (407 + 407) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 407 * (2 : ZMod 382775276171) ^ 407 := by rw [pow_add]
          _ = 144914724419 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 382775276171) ^ 1629 = 365554773019 := by
        calc
          (2 : ZMod 382775276171) ^ 1629 = (2 : ZMod 382775276171) ^ (814 + 814 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 814 * (2 : ZMod 382775276171) ^ 814) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 365554773019 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 382775276171) ^ 3259 = 115482259579 := by
        calc
          (2 : ZMod 382775276171) ^ 3259 = (2 : ZMod 382775276171) ^ (1629 + 1629 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1629 * (2 : ZMod 382775276171) ^ 1629) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 115482259579 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 382775276171) ^ 6518 = 64488665916 := by
        calc
          (2 : ZMod 382775276171) ^ 6518 = (2 : ZMod 382775276171) ^ (3259 + 3259) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 3259 * (2 : ZMod 382775276171) ^ 3259 := by rw [pow_add]
          _ = 64488665916 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 382775276171) ^ 13037 = 338206369445 := by
        calc
          (2 : ZMod 382775276171) ^ 13037 = (2 : ZMod 382775276171) ^ (6518 + 6518 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 6518 * (2 : ZMod 382775276171) ^ 6518) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 338206369445 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 382775276171) ^ 26074 = 66862008054 := by
        calc
          (2 : ZMod 382775276171) ^ 26074 = (2 : ZMod 382775276171) ^ (13037 + 13037) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 13037 * (2 : ZMod 382775276171) ^ 13037 := by rw [pow_add]
          _ = 66862008054 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 382775276171) ^ 52148 = 142300963347 := by
        calc
          (2 : ZMod 382775276171) ^ 52148 = (2 : ZMod 382775276171) ^ (26074 + 26074) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 26074 * (2 : ZMod 382775276171) ^ 26074 := by rw [pow_add]
          _ = 142300963347 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 382775276171) ^ 104297 = 35657626266 := by
        calc
          (2 : ZMod 382775276171) ^ 104297 = (2 : ZMod 382775276171) ^ (52148 + 52148 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 52148 * (2 : ZMod 382775276171) ^ 52148) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 35657626266 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 382775276171) ^ 208595 = 173951376065 := by
        calc
          (2 : ZMod 382775276171) ^ 208595 = (2 : ZMod 382775276171) ^ (104297 + 104297 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 104297 * (2 : ZMod 382775276171) ^ 104297) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 173951376065 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 382775276171) ^ 417191 = 198486731702 := by
        calc
          (2 : ZMod 382775276171) ^ 417191 = (2 : ZMod 382775276171) ^ (208595 + 208595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 208595 * (2 : ZMod 382775276171) ^ 208595) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 198486731702 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 382775276171) ^ 834383 = 371174606843 := by
        calc
          (2 : ZMod 382775276171) ^ 834383 = (2 : ZMod 382775276171) ^ (417191 + 417191 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 417191 * (2 : ZMod 382775276171) ^ 417191) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 371174606843 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 382775276171) ^ 1668767 = 264919521818 := by
        calc
          (2 : ZMod 382775276171) ^ 1668767 = (2 : ZMod 382775276171) ^ (834383 + 834383 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 834383 * (2 : ZMod 382775276171) ^ 834383) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 264919521818 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 382775276171) ^ 3337535 = 101854034243 := by
        calc
          (2 : ZMod 382775276171) ^ 3337535 = (2 : ZMod 382775276171) ^ (1668767 + 1668767 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1668767 * (2 : ZMod 382775276171) ^ 1668767) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 101854034243 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 382775276171) ^ 6675071 = 245660210835 := by
        calc
          (2 : ZMod 382775276171) ^ 6675071 = (2 : ZMod 382775276171) ^ (3337535 + 3337535 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 3337535 * (2 : ZMod 382775276171) ^ 3337535) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 245660210835 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 382775276171) ^ 13350142 = 107124459601 := by
        calc
          (2 : ZMod 382775276171) ^ 13350142 = (2 : ZMod 382775276171) ^ (6675071 + 6675071) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 6675071 * (2 : ZMod 382775276171) ^ 6675071 := by rw [pow_add]
          _ = 107124459601 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 382775276171) ^ 26700284 = 300068921554 := by
        calc
          (2 : ZMod 382775276171) ^ 26700284 = (2 : ZMod 382775276171) ^ (13350142 + 13350142) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 13350142 * (2 : ZMod 382775276171) ^ 13350142 := by rw [pow_add]
          _ = 300068921554 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 382775276171) ^ 53400568 = 88968063060 := by
        calc
          (2 : ZMod 382775276171) ^ 53400568 = (2 : ZMod 382775276171) ^ (26700284 + 26700284) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 26700284 * (2 : ZMod 382775276171) ^ 26700284 := by rw [pow_add]
          _ = 88968063060 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 382775276171) ^ 106801137 = 76426050027 := by
        calc
          (2 : ZMod 382775276171) ^ 106801137 = (2 : ZMod 382775276171) ^ (53400568 + 53400568 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 53400568 * (2 : ZMod 382775276171) ^ 53400568) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 76426050027 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 382775276171) ^ 213602274 = 24716341147 := by
        calc
          (2 : ZMod 382775276171) ^ 213602274 = (2 : ZMod 382775276171) ^ (106801137 + 106801137) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 106801137 * (2 : ZMod 382775276171) ^ 106801137 := by rw [pow_add]
          _ = 24716341147 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 382775276171) ^ 427204549 = 349646529204 := by
        calc
          (2 : ZMod 382775276171) ^ 427204549 = (2 : ZMod 382775276171) ^ (213602274 + 213602274 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 213602274 * (2 : ZMod 382775276171) ^ 213602274) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 349646529204 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 382775276171) ^ 854409098 = 121230042672 := by
        calc
          (2 : ZMod 382775276171) ^ 854409098 = (2 : ZMod 382775276171) ^ (427204549 + 427204549) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 427204549 * (2 : ZMod 382775276171) ^ 427204549 := by rw [pow_add]
          _ = 121230042672 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 382775276171) ^ 1708818197 = 260457463434 := by
        calc
          (2 : ZMod 382775276171) ^ 1708818197 = (2 : ZMod 382775276171) ^ (854409098 + 854409098 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 854409098 * (2 : ZMod 382775276171) ^ 854409098) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 260457463434 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 382775276171) ^ 3417636394 = 8540680491 := by
        calc
          (2 : ZMod 382775276171) ^ 3417636394 = (2 : ZMod 382775276171) ^ (1708818197 + 1708818197) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 1708818197 * (2 : ZMod 382775276171) ^ 1708818197 := by rw [pow_add]
          _ = 8540680491 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 382775276171) ^ 6835272788 = 305772149349 := by
        calc
          (2 : ZMod 382775276171) ^ 6835272788 = (2 : ZMod 382775276171) ^ (3417636394 + 3417636394) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 3417636394 * (2 : ZMod 382775276171) ^ 3417636394 := by rw [pow_add]
          _ = 305772149349 := by rw [factor_2_31]; decide
      have factor_2_33 : (2 : ZMod 382775276171) ^ 13670545577 = 24183234901 := by
        calc
          (2 : ZMod 382775276171) ^ 13670545577 = (2 : ZMod 382775276171) ^ (6835272788 + 6835272788 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 6835272788 * (2 : ZMod 382775276171) ^ 6835272788) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 24183234901 := by rw [factor_2_32]; decide
      have factor_2_34 : (2 : ZMod 382775276171) ^ 27341091155 = 349719424470 := by
        calc
          (2 : ZMod 382775276171) ^ 27341091155 = (2 : ZMod 382775276171) ^ (13670545577 + 13670545577 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 13670545577 * (2 : ZMod 382775276171) ^ 13670545577) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 349719424470 := by rw [factor_2_33]; decide
      have factor_2_35 : (2 : ZMod 382775276171) ^ 54682182310 = 179014256820 := by
        calc
          (2 : ZMod 382775276171) ^ 54682182310 = (2 : ZMod 382775276171) ^ (27341091155 + 27341091155) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 27341091155 * (2 : ZMod 382775276171) ^ 27341091155 := by rw [pow_add]
          _ = 179014256820 := by rw [factor_2_34]; decide
      change (2 : ZMod 382775276171) ^ 54682182310 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (2 : ZMod 382775276171) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 382775276171) ^ 3 = 8 := by
        calc
          (2 : ZMod 382775276171) ^ 3 = (2 : ZMod 382775276171) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 1 * (2 : ZMod 382775276171) ^ 1) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 382775276171) ^ 7 = 128 := by
        calc
          (2 : ZMod 382775276171) ^ 7 = (2 : ZMod 382775276171) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 3 * (2 : ZMod 382775276171) ^ 3) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 382775276171) ^ 15 = 32768 := by
        calc
          (2 : ZMod 382775276171) ^ 15 = (2 : ZMod 382775276171) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 7 * (2 : ZMod 382775276171) ^ 7) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 382775276171) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 382775276171) ^ 30 = (2 : ZMod 382775276171) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 15 * (2 : ZMod 382775276171) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 382775276171) ^ 61 = 152256275900 := by
        calc
          (2 : ZMod 382775276171) ^ 61 = (2 : ZMod 382775276171) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 30 * (2 : ZMod 382775276171) ^ 30) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 152256275900 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 382775276171) ^ 122 = 306950980599 := by
        calc
          (2 : ZMod 382775276171) ^ 122 = (2 : ZMod 382775276171) ^ (61 + 61) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 61 * (2 : ZMod 382775276171) ^ 61 := by rw [pow_add]
          _ = 306950980599 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 382775276171) ^ 245 = 144378246095 := by
        calc
          (2 : ZMod 382775276171) ^ 245 = (2 : ZMod 382775276171) ^ (122 + 122 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = ((2 : ZMod 382775276171) ^ 122 * (2 : ZMod 382775276171) ^ 122) * (2 : ZMod 382775276171) := by rw [pow_succ, pow_add]
          _ = 144378246095 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 382775276171) ^ 490 = 190078465136 := by
        calc
          (2 : ZMod 382775276171) ^ 490 = (2 : ZMod 382775276171) ^ (245 + 245) :=
            congrArg (fun n : ℕ => (2 : ZMod 382775276171) ^ n) (by norm_num)
          _ = (2 : ZMod 382775276171) ^ 245 * (2 : ZMod 382775276171) ^ 245 := by rw [pow_add]
          _ = 190078465136 := by rw [factor_3_7]; decide
      change (2 : ZMod 382775276171) ^ 490 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_382775276171

end TotientTailPeriodKiller
end Erdos249257
