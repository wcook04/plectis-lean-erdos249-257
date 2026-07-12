import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_594253304089 : Nat.Prime 594253304089 := by
  apply lucas_primality 594253304089 (37 : ZMod 594253304089)
  ·
      have fermat_0 : (37 : ZMod 594253304089) ^ 1 = 37 := by norm_num
      have fermat_1 : (37 : ZMod 594253304089) ^ 2 = 1369 := by
        calc
          (37 : ZMod 594253304089) ^ 2 = (37 : ZMod 594253304089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1 * (37 : ZMod 594253304089) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [fermat_0]; decide
      have fermat_2 : (37 : ZMod 594253304089) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 594253304089) ^ 4 = (37 : ZMod 594253304089) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2 * (37 : ZMod 594253304089) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [fermat_1]; decide
      have fermat_3 : (37 : ZMod 594253304089) ^ 8 = 541212933476 := by
        calc
          (37 : ZMod 594253304089) ^ 8 = (37 : ZMod 594253304089) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 4 * (37 : ZMod 594253304089) ^ 4 := by rw [pow_add]
          _ = 541212933476 := by rw [fermat_2]; decide
      have fermat_4 : (37 : ZMod 594253304089) ^ 17 = 79535147131 := by
        calc
          (37 : ZMod 594253304089) ^ 17 = (37 : ZMod 594253304089) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 8 * (37 : ZMod 594253304089) ^ 8) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 79535147131 := by rw [fermat_3]; decide
      have fermat_5 : (37 : ZMod 594253304089) ^ 34 = 436982457225 := by
        calc
          (37 : ZMod 594253304089) ^ 34 = (37 : ZMod 594253304089) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 17 * (37 : ZMod 594253304089) ^ 17 := by rw [pow_add]
          _ = 436982457225 := by rw [fermat_4]; decide
      have fermat_6 : (37 : ZMod 594253304089) ^ 69 = 460763704085 := by
        calc
          (37 : ZMod 594253304089) ^ 69 = (37 : ZMod 594253304089) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 34 * (37 : ZMod 594253304089) ^ 34) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 460763704085 := by rw [fermat_5]; decide
      have fermat_7 : (37 : ZMod 594253304089) ^ 138 = 295496745126 := by
        calc
          (37 : ZMod 594253304089) ^ 138 = (37 : ZMod 594253304089) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 69 * (37 : ZMod 594253304089) ^ 69 := by rw [pow_add]
          _ = 295496745126 := by rw [fermat_6]; decide
      have fermat_8 : (37 : ZMod 594253304089) ^ 276 = 92053655078 := by
        calc
          (37 : ZMod 594253304089) ^ 276 = (37 : ZMod 594253304089) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 138 * (37 : ZMod 594253304089) ^ 138 := by rw [pow_add]
          _ = 92053655078 := by rw [fermat_7]; decide
      have fermat_9 : (37 : ZMod 594253304089) ^ 553 = 346000437071 := by
        calc
          (37 : ZMod 594253304089) ^ 553 = (37 : ZMod 594253304089) ^ (276 + 276 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 276 * (37 : ZMod 594253304089) ^ 276) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 346000437071 := by rw [fermat_8]; decide
      have fermat_10 : (37 : ZMod 594253304089) ^ 1106 = 483606078334 := by
        calc
          (37 : ZMod 594253304089) ^ 1106 = (37 : ZMod 594253304089) ^ (553 + 553) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 553 * (37 : ZMod 594253304089) ^ 553 := by rw [pow_add]
          _ = 483606078334 := by rw [fermat_9]; decide
      have fermat_11 : (37 : ZMod 594253304089) ^ 2213 = 82509361869 := by
        calc
          (37 : ZMod 594253304089) ^ 2213 = (37 : ZMod 594253304089) ^ (1106 + 1106 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 1106 * (37 : ZMod 594253304089) ^ 1106) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 82509361869 := by rw [fermat_10]; decide
      have fermat_12 : (37 : ZMod 594253304089) ^ 4427 = 370755158361 := by
        calc
          (37 : ZMod 594253304089) ^ 4427 = (37 : ZMod 594253304089) ^ (2213 + 2213 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 2213 * (37 : ZMod 594253304089) ^ 2213) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 370755158361 := by rw [fermat_11]; decide
      have fermat_13 : (37 : ZMod 594253304089) ^ 8855 = 238920469923 := by
        calc
          (37 : ZMod 594253304089) ^ 8855 = (37 : ZMod 594253304089) ^ (4427 + 4427 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 4427 * (37 : ZMod 594253304089) ^ 4427) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 238920469923 := by rw [fermat_12]; decide
      have fermat_14 : (37 : ZMod 594253304089) ^ 17710 = 47695638413 := by
        calc
          (37 : ZMod 594253304089) ^ 17710 = (37 : ZMod 594253304089) ^ (8855 + 8855) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 8855 * (37 : ZMod 594253304089) ^ 8855 := by rw [pow_add]
          _ = 47695638413 := by rw [fermat_13]; decide
      have fermat_15 : (37 : ZMod 594253304089) ^ 35420 = 107092638033 := by
        calc
          (37 : ZMod 594253304089) ^ 35420 = (37 : ZMod 594253304089) ^ (17710 + 17710) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 17710 * (37 : ZMod 594253304089) ^ 17710 := by rw [pow_add]
          _ = 107092638033 := by rw [fermat_14]; decide
      have fermat_16 : (37 : ZMod 594253304089) ^ 70840 = 315130500978 := by
        calc
          (37 : ZMod 594253304089) ^ 70840 = (37 : ZMod 594253304089) ^ (35420 + 35420) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 35420 * (37 : ZMod 594253304089) ^ 35420 := by rw [pow_add]
          _ = 315130500978 := by rw [fermat_15]; decide
      have fermat_17 : (37 : ZMod 594253304089) ^ 141681 = 516471943474 := by
        calc
          (37 : ZMod 594253304089) ^ 141681 = (37 : ZMod 594253304089) ^ (70840 + 70840 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 70840 * (37 : ZMod 594253304089) ^ 70840) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 516471943474 := by rw [fermat_16]; decide
      have fermat_18 : (37 : ZMod 594253304089) ^ 283362 = 255309787245 := by
        calc
          (37 : ZMod 594253304089) ^ 283362 = (37 : ZMod 594253304089) ^ (141681 + 141681) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 141681 * (37 : ZMod 594253304089) ^ 141681 := by rw [pow_add]
          _ = 255309787245 := by rw [fermat_17]; decide
      have fermat_19 : (37 : ZMod 594253304089) ^ 566724 = 52534235946 := by
        calc
          (37 : ZMod 594253304089) ^ 566724 = (37 : ZMod 594253304089) ^ (283362 + 283362) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 283362 * (37 : ZMod 594253304089) ^ 283362 := by rw [pow_add]
          _ = 52534235946 := by rw [fermat_18]; decide
      have fermat_20 : (37 : ZMod 594253304089) ^ 1133448 = 430097313669 := by
        calc
          (37 : ZMod 594253304089) ^ 1133448 = (37 : ZMod 594253304089) ^ (566724 + 566724) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 566724 * (37 : ZMod 594253304089) ^ 566724 := by rw [pow_add]
          _ = 430097313669 := by rw [fermat_19]; decide
      have fermat_21 : (37 : ZMod 594253304089) ^ 2266896 = 437846636468 := by
        calc
          (37 : ZMod 594253304089) ^ 2266896 = (37 : ZMod 594253304089) ^ (1133448 + 1133448) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1133448 * (37 : ZMod 594253304089) ^ 1133448 := by rw [pow_add]
          _ = 437846636468 := by rw [fermat_20]; decide
      have fermat_22 : (37 : ZMod 594253304089) ^ 4533792 = 310465966949 := by
        calc
          (37 : ZMod 594253304089) ^ 4533792 = (37 : ZMod 594253304089) ^ (2266896 + 2266896) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2266896 * (37 : ZMod 594253304089) ^ 2266896 := by rw [pow_add]
          _ = 310465966949 := by rw [fermat_21]; decide
      have fermat_23 : (37 : ZMod 594253304089) ^ 9067585 = 313540546178 := by
        calc
          (37 : ZMod 594253304089) ^ 9067585 = (37 : ZMod 594253304089) ^ (4533792 + 4533792 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 4533792 * (37 : ZMod 594253304089) ^ 4533792) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 313540546178 := by rw [fermat_22]; decide
      have fermat_24 : (37 : ZMod 594253304089) ^ 18135171 = 23046427576 := by
        calc
          (37 : ZMod 594253304089) ^ 18135171 = (37 : ZMod 594253304089) ^ (9067585 + 9067585 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 9067585 * (37 : ZMod 594253304089) ^ 9067585) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 23046427576 := by rw [fermat_23]; decide
      have fermat_25 : (37 : ZMod 594253304089) ^ 36270343 = 545816668582 := by
        calc
          (37 : ZMod 594253304089) ^ 36270343 = (37 : ZMod 594253304089) ^ (18135171 + 18135171 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 18135171 * (37 : ZMod 594253304089) ^ 18135171) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 545816668582 := by rw [fermat_24]; decide
      have fermat_26 : (37 : ZMod 594253304089) ^ 72540686 = 283985323869 := by
        calc
          (37 : ZMod 594253304089) ^ 72540686 = (37 : ZMod 594253304089) ^ (36270343 + 36270343) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 36270343 * (37 : ZMod 594253304089) ^ 36270343 := by rw [pow_add]
          _ = 283985323869 := by rw [fermat_25]; decide
      have fermat_27 : (37 : ZMod 594253304089) ^ 145081373 = 137539987194 := by
        calc
          (37 : ZMod 594253304089) ^ 145081373 = (37 : ZMod 594253304089) ^ (72540686 + 72540686 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 72540686 * (37 : ZMod 594253304089) ^ 72540686) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 137539987194 := by rw [fermat_26]; decide
      have fermat_28 : (37 : ZMod 594253304089) ^ 290162746 = 238497829290 := by
        calc
          (37 : ZMod 594253304089) ^ 290162746 = (37 : ZMod 594253304089) ^ (145081373 + 145081373) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 145081373 * (37 : ZMod 594253304089) ^ 145081373 := by rw [pow_add]
          _ = 238497829290 := by rw [fermat_27]; decide
      have fermat_29 : (37 : ZMod 594253304089) ^ 580325492 = 67704884547 := by
        calc
          (37 : ZMod 594253304089) ^ 580325492 = (37 : ZMod 594253304089) ^ (290162746 + 290162746) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 290162746 * (37 : ZMod 594253304089) ^ 290162746 := by rw [pow_add]
          _ = 67704884547 := by rw [fermat_28]; decide
      have fermat_30 : (37 : ZMod 594253304089) ^ 1160650984 = 100457045117 := by
        calc
          (37 : ZMod 594253304089) ^ 1160650984 = (37 : ZMod 594253304089) ^ (580325492 + 580325492) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 580325492 * (37 : ZMod 594253304089) ^ 580325492 := by rw [pow_add]
          _ = 100457045117 := by rw [fermat_29]; decide
      have fermat_31 : (37 : ZMod 594253304089) ^ 2321301969 = 66307974870 := by
        calc
          (37 : ZMod 594253304089) ^ 2321301969 = (37 : ZMod 594253304089) ^ (1160650984 + 1160650984 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 1160650984 * (37 : ZMod 594253304089) ^ 1160650984) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 66307974870 := by rw [fermat_30]; decide
      have fermat_32 : (37 : ZMod 594253304089) ^ 4642603938 = 267671777972 := by
        calc
          (37 : ZMod 594253304089) ^ 4642603938 = (37 : ZMod 594253304089) ^ (2321301969 + 2321301969) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2321301969 * (37 : ZMod 594253304089) ^ 2321301969 := by rw [pow_add]
          _ = 267671777972 := by rw [fermat_31]; decide
      have fermat_33 : (37 : ZMod 594253304089) ^ 9285207876 = 194241125192 := by
        calc
          (37 : ZMod 594253304089) ^ 9285207876 = (37 : ZMod 594253304089) ^ (4642603938 + 4642603938) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 4642603938 * (37 : ZMod 594253304089) ^ 4642603938 := by rw [pow_add]
          _ = 194241125192 := by rw [fermat_32]; decide
      have fermat_34 : (37 : ZMod 594253304089) ^ 18570415752 = 141563328707 := by
        calc
          (37 : ZMod 594253304089) ^ 18570415752 = (37 : ZMod 594253304089) ^ (9285207876 + 9285207876) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 9285207876 * (37 : ZMod 594253304089) ^ 9285207876 := by rw [pow_add]
          _ = 141563328707 := by rw [fermat_33]; decide
      have fermat_35 : (37 : ZMod 594253304089) ^ 37140831505 = 400592863594 := by
        calc
          (37 : ZMod 594253304089) ^ 37140831505 = (37 : ZMod 594253304089) ^ (18570415752 + 18570415752 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 18570415752 * (37 : ZMod 594253304089) ^ 18570415752) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 400592863594 := by rw [fermat_34]; decide
      have fermat_36 : (37 : ZMod 594253304089) ^ 74281663011 = 471039083629 := by
        calc
          (37 : ZMod 594253304089) ^ 74281663011 = (37 : ZMod 594253304089) ^ (37140831505 + 37140831505 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 37140831505 * (37 : ZMod 594253304089) ^ 37140831505) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 471039083629 := by rw [fermat_35]; decide
      have fermat_37 : (37 : ZMod 594253304089) ^ 148563326022 = 460428041497 := by
        calc
          (37 : ZMod 594253304089) ^ 148563326022 = (37 : ZMod 594253304089) ^ (74281663011 + 74281663011) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 74281663011 * (37 : ZMod 594253304089) ^ 74281663011 := by rw [pow_add]
          _ = 460428041497 := by rw [fermat_36]; decide
      have fermat_38 : (37 : ZMod 594253304089) ^ 297126652044 = 594253304088 := by
        calc
          (37 : ZMod 594253304089) ^ 297126652044 = (37 : ZMod 594253304089) ^ (148563326022 + 148563326022) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 148563326022 * (37 : ZMod 594253304089) ^ 148563326022 := by rw [pow_add]
          _ = 594253304088 := by rw [fermat_37]; decide
      have fermat_39 : (37 : ZMod 594253304089) ^ 594253304088 = 1 := by
        calc
          (37 : ZMod 594253304089) ^ 594253304088 = (37 : ZMod 594253304089) ^ (297126652044 + 297126652044) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 297126652044 * (37 : ZMod 594253304089) ^ 297126652044 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13127, 1), (1886231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13127, 1), (1886231, 1)] : List FactorBlock).map factorBlockValue).prod = 594253304089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (37 : ZMod 594253304089) ^ 1 = 37 := by norm_num
      have factor_0_1 : (37 : ZMod 594253304089) ^ 2 = 1369 := by
        calc
          (37 : ZMod 594253304089) ^ 2 = (37 : ZMod 594253304089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1 * (37 : ZMod 594253304089) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_0_0]; decide
      have factor_0_2 : (37 : ZMod 594253304089) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 594253304089) ^ 4 = (37 : ZMod 594253304089) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2 * (37 : ZMod 594253304089) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_0_1]; decide
      have factor_0_3 : (37 : ZMod 594253304089) ^ 8 = 541212933476 := by
        calc
          (37 : ZMod 594253304089) ^ 8 = (37 : ZMod 594253304089) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 4 * (37 : ZMod 594253304089) ^ 4 := by rw [pow_add]
          _ = 541212933476 := by rw [factor_0_2]; decide
      have factor_0_4 : (37 : ZMod 594253304089) ^ 17 = 79535147131 := by
        calc
          (37 : ZMod 594253304089) ^ 17 = (37 : ZMod 594253304089) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 8 * (37 : ZMod 594253304089) ^ 8) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 79535147131 := by rw [factor_0_3]; decide
      have factor_0_5 : (37 : ZMod 594253304089) ^ 34 = 436982457225 := by
        calc
          (37 : ZMod 594253304089) ^ 34 = (37 : ZMod 594253304089) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 17 * (37 : ZMod 594253304089) ^ 17 := by rw [pow_add]
          _ = 436982457225 := by rw [factor_0_4]; decide
      have factor_0_6 : (37 : ZMod 594253304089) ^ 69 = 460763704085 := by
        calc
          (37 : ZMod 594253304089) ^ 69 = (37 : ZMod 594253304089) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 34 * (37 : ZMod 594253304089) ^ 34) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 460763704085 := by rw [factor_0_5]; decide
      have factor_0_7 : (37 : ZMod 594253304089) ^ 138 = 295496745126 := by
        calc
          (37 : ZMod 594253304089) ^ 138 = (37 : ZMod 594253304089) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 69 * (37 : ZMod 594253304089) ^ 69 := by rw [pow_add]
          _ = 295496745126 := by rw [factor_0_6]; decide
      have factor_0_8 : (37 : ZMod 594253304089) ^ 276 = 92053655078 := by
        calc
          (37 : ZMod 594253304089) ^ 276 = (37 : ZMod 594253304089) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 138 * (37 : ZMod 594253304089) ^ 138 := by rw [pow_add]
          _ = 92053655078 := by rw [factor_0_7]; decide
      have factor_0_9 : (37 : ZMod 594253304089) ^ 553 = 346000437071 := by
        calc
          (37 : ZMod 594253304089) ^ 553 = (37 : ZMod 594253304089) ^ (276 + 276 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 276 * (37 : ZMod 594253304089) ^ 276) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 346000437071 := by rw [factor_0_8]; decide
      have factor_0_10 : (37 : ZMod 594253304089) ^ 1106 = 483606078334 := by
        calc
          (37 : ZMod 594253304089) ^ 1106 = (37 : ZMod 594253304089) ^ (553 + 553) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 553 * (37 : ZMod 594253304089) ^ 553 := by rw [pow_add]
          _ = 483606078334 := by rw [factor_0_9]; decide
      have factor_0_11 : (37 : ZMod 594253304089) ^ 2213 = 82509361869 := by
        calc
          (37 : ZMod 594253304089) ^ 2213 = (37 : ZMod 594253304089) ^ (1106 + 1106 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 1106 * (37 : ZMod 594253304089) ^ 1106) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 82509361869 := by rw [factor_0_10]; decide
      have factor_0_12 : (37 : ZMod 594253304089) ^ 4427 = 370755158361 := by
        calc
          (37 : ZMod 594253304089) ^ 4427 = (37 : ZMod 594253304089) ^ (2213 + 2213 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 2213 * (37 : ZMod 594253304089) ^ 2213) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 370755158361 := by rw [factor_0_11]; decide
      have factor_0_13 : (37 : ZMod 594253304089) ^ 8855 = 238920469923 := by
        calc
          (37 : ZMod 594253304089) ^ 8855 = (37 : ZMod 594253304089) ^ (4427 + 4427 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 4427 * (37 : ZMod 594253304089) ^ 4427) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 238920469923 := by rw [factor_0_12]; decide
      have factor_0_14 : (37 : ZMod 594253304089) ^ 17710 = 47695638413 := by
        calc
          (37 : ZMod 594253304089) ^ 17710 = (37 : ZMod 594253304089) ^ (8855 + 8855) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 8855 * (37 : ZMod 594253304089) ^ 8855 := by rw [pow_add]
          _ = 47695638413 := by rw [factor_0_13]; decide
      have factor_0_15 : (37 : ZMod 594253304089) ^ 35420 = 107092638033 := by
        calc
          (37 : ZMod 594253304089) ^ 35420 = (37 : ZMod 594253304089) ^ (17710 + 17710) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 17710 * (37 : ZMod 594253304089) ^ 17710 := by rw [pow_add]
          _ = 107092638033 := by rw [factor_0_14]; decide
      have factor_0_16 : (37 : ZMod 594253304089) ^ 70840 = 315130500978 := by
        calc
          (37 : ZMod 594253304089) ^ 70840 = (37 : ZMod 594253304089) ^ (35420 + 35420) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 35420 * (37 : ZMod 594253304089) ^ 35420 := by rw [pow_add]
          _ = 315130500978 := by rw [factor_0_15]; decide
      have factor_0_17 : (37 : ZMod 594253304089) ^ 141681 = 516471943474 := by
        calc
          (37 : ZMod 594253304089) ^ 141681 = (37 : ZMod 594253304089) ^ (70840 + 70840 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 70840 * (37 : ZMod 594253304089) ^ 70840) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 516471943474 := by rw [factor_0_16]; decide
      have factor_0_18 : (37 : ZMod 594253304089) ^ 283362 = 255309787245 := by
        calc
          (37 : ZMod 594253304089) ^ 283362 = (37 : ZMod 594253304089) ^ (141681 + 141681) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 141681 * (37 : ZMod 594253304089) ^ 141681 := by rw [pow_add]
          _ = 255309787245 := by rw [factor_0_17]; decide
      have factor_0_19 : (37 : ZMod 594253304089) ^ 566724 = 52534235946 := by
        calc
          (37 : ZMod 594253304089) ^ 566724 = (37 : ZMod 594253304089) ^ (283362 + 283362) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 283362 * (37 : ZMod 594253304089) ^ 283362 := by rw [pow_add]
          _ = 52534235946 := by rw [factor_0_18]; decide
      have factor_0_20 : (37 : ZMod 594253304089) ^ 1133448 = 430097313669 := by
        calc
          (37 : ZMod 594253304089) ^ 1133448 = (37 : ZMod 594253304089) ^ (566724 + 566724) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 566724 * (37 : ZMod 594253304089) ^ 566724 := by rw [pow_add]
          _ = 430097313669 := by rw [factor_0_19]; decide
      have factor_0_21 : (37 : ZMod 594253304089) ^ 2266896 = 437846636468 := by
        calc
          (37 : ZMod 594253304089) ^ 2266896 = (37 : ZMod 594253304089) ^ (1133448 + 1133448) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1133448 * (37 : ZMod 594253304089) ^ 1133448 := by rw [pow_add]
          _ = 437846636468 := by rw [factor_0_20]; decide
      have factor_0_22 : (37 : ZMod 594253304089) ^ 4533792 = 310465966949 := by
        calc
          (37 : ZMod 594253304089) ^ 4533792 = (37 : ZMod 594253304089) ^ (2266896 + 2266896) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2266896 * (37 : ZMod 594253304089) ^ 2266896 := by rw [pow_add]
          _ = 310465966949 := by rw [factor_0_21]; decide
      have factor_0_23 : (37 : ZMod 594253304089) ^ 9067585 = 313540546178 := by
        calc
          (37 : ZMod 594253304089) ^ 9067585 = (37 : ZMod 594253304089) ^ (4533792 + 4533792 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 4533792 * (37 : ZMod 594253304089) ^ 4533792) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 313540546178 := by rw [factor_0_22]; decide
      have factor_0_24 : (37 : ZMod 594253304089) ^ 18135171 = 23046427576 := by
        calc
          (37 : ZMod 594253304089) ^ 18135171 = (37 : ZMod 594253304089) ^ (9067585 + 9067585 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 9067585 * (37 : ZMod 594253304089) ^ 9067585) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 23046427576 := by rw [factor_0_23]; decide
      have factor_0_25 : (37 : ZMod 594253304089) ^ 36270343 = 545816668582 := by
        calc
          (37 : ZMod 594253304089) ^ 36270343 = (37 : ZMod 594253304089) ^ (18135171 + 18135171 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 18135171 * (37 : ZMod 594253304089) ^ 18135171) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 545816668582 := by rw [factor_0_24]; decide
      have factor_0_26 : (37 : ZMod 594253304089) ^ 72540686 = 283985323869 := by
        calc
          (37 : ZMod 594253304089) ^ 72540686 = (37 : ZMod 594253304089) ^ (36270343 + 36270343) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 36270343 * (37 : ZMod 594253304089) ^ 36270343 := by rw [pow_add]
          _ = 283985323869 := by rw [factor_0_25]; decide
      have factor_0_27 : (37 : ZMod 594253304089) ^ 145081373 = 137539987194 := by
        calc
          (37 : ZMod 594253304089) ^ 145081373 = (37 : ZMod 594253304089) ^ (72540686 + 72540686 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 72540686 * (37 : ZMod 594253304089) ^ 72540686) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 137539987194 := by rw [factor_0_26]; decide
      have factor_0_28 : (37 : ZMod 594253304089) ^ 290162746 = 238497829290 := by
        calc
          (37 : ZMod 594253304089) ^ 290162746 = (37 : ZMod 594253304089) ^ (145081373 + 145081373) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 145081373 * (37 : ZMod 594253304089) ^ 145081373 := by rw [pow_add]
          _ = 238497829290 := by rw [factor_0_27]; decide
      have factor_0_29 : (37 : ZMod 594253304089) ^ 580325492 = 67704884547 := by
        calc
          (37 : ZMod 594253304089) ^ 580325492 = (37 : ZMod 594253304089) ^ (290162746 + 290162746) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 290162746 * (37 : ZMod 594253304089) ^ 290162746 := by rw [pow_add]
          _ = 67704884547 := by rw [factor_0_28]; decide
      have factor_0_30 : (37 : ZMod 594253304089) ^ 1160650984 = 100457045117 := by
        calc
          (37 : ZMod 594253304089) ^ 1160650984 = (37 : ZMod 594253304089) ^ (580325492 + 580325492) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 580325492 * (37 : ZMod 594253304089) ^ 580325492 := by rw [pow_add]
          _ = 100457045117 := by rw [factor_0_29]; decide
      have factor_0_31 : (37 : ZMod 594253304089) ^ 2321301969 = 66307974870 := by
        calc
          (37 : ZMod 594253304089) ^ 2321301969 = (37 : ZMod 594253304089) ^ (1160650984 + 1160650984 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 1160650984 * (37 : ZMod 594253304089) ^ 1160650984) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 66307974870 := by rw [factor_0_30]; decide
      have factor_0_32 : (37 : ZMod 594253304089) ^ 4642603938 = 267671777972 := by
        calc
          (37 : ZMod 594253304089) ^ 4642603938 = (37 : ZMod 594253304089) ^ (2321301969 + 2321301969) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2321301969 * (37 : ZMod 594253304089) ^ 2321301969 := by rw [pow_add]
          _ = 267671777972 := by rw [factor_0_31]; decide
      have factor_0_33 : (37 : ZMod 594253304089) ^ 9285207876 = 194241125192 := by
        calc
          (37 : ZMod 594253304089) ^ 9285207876 = (37 : ZMod 594253304089) ^ (4642603938 + 4642603938) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 4642603938 * (37 : ZMod 594253304089) ^ 4642603938 := by rw [pow_add]
          _ = 194241125192 := by rw [factor_0_32]; decide
      have factor_0_34 : (37 : ZMod 594253304089) ^ 18570415752 = 141563328707 := by
        calc
          (37 : ZMod 594253304089) ^ 18570415752 = (37 : ZMod 594253304089) ^ (9285207876 + 9285207876) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 9285207876 * (37 : ZMod 594253304089) ^ 9285207876 := by rw [pow_add]
          _ = 141563328707 := by rw [factor_0_33]; decide
      have factor_0_35 : (37 : ZMod 594253304089) ^ 37140831505 = 400592863594 := by
        calc
          (37 : ZMod 594253304089) ^ 37140831505 = (37 : ZMod 594253304089) ^ (18570415752 + 18570415752 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 18570415752 * (37 : ZMod 594253304089) ^ 18570415752) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 400592863594 := by rw [factor_0_34]; decide
      have factor_0_36 : (37 : ZMod 594253304089) ^ 74281663011 = 471039083629 := by
        calc
          (37 : ZMod 594253304089) ^ 74281663011 = (37 : ZMod 594253304089) ^ (37140831505 + 37140831505 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 37140831505 * (37 : ZMod 594253304089) ^ 37140831505) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 471039083629 := by rw [factor_0_35]; decide
      have factor_0_37 : (37 : ZMod 594253304089) ^ 148563326022 = 460428041497 := by
        calc
          (37 : ZMod 594253304089) ^ 148563326022 = (37 : ZMod 594253304089) ^ (74281663011 + 74281663011) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 74281663011 * (37 : ZMod 594253304089) ^ 74281663011 := by rw [pow_add]
          _ = 460428041497 := by rw [factor_0_36]; decide
      have factor_0_38 : (37 : ZMod 594253304089) ^ 297126652044 = 594253304088 := by
        calc
          (37 : ZMod 594253304089) ^ 297126652044 = (37 : ZMod 594253304089) ^ (148563326022 + 148563326022) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 148563326022 * (37 : ZMod 594253304089) ^ 148563326022 := by rw [pow_add]
          _ = 594253304088 := by rw [factor_0_37]; decide
      change (37 : ZMod 594253304089) ^ 297126652044 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (37 : ZMod 594253304089) ^ 1 = 37 := by norm_num
      have factor_1_1 : (37 : ZMod 594253304089) ^ 2 = 1369 := by
        calc
          (37 : ZMod 594253304089) ^ 2 = (37 : ZMod 594253304089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1 * (37 : ZMod 594253304089) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_1_0]; decide
      have factor_1_2 : (37 : ZMod 594253304089) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 594253304089) ^ 5 = (37 : ZMod 594253304089) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 2 * (37 : ZMod 594253304089) ^ 2) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_1_1]; decide
      have factor_1_3 : (37 : ZMod 594253304089) ^ 11 = 559548430169 := by
        calc
          (37 : ZMod 594253304089) ^ 11 = (37 : ZMod 594253304089) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 5 * (37 : ZMod 594253304089) ^ 5) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 559548430169 := by rw [factor_1_2]; decide
      have factor_1_4 : (37 : ZMod 594253304089) ^ 23 = 418981047951 := by
        calc
          (37 : ZMod 594253304089) ^ 23 = (37 : ZMod 594253304089) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 11 * (37 : ZMod 594253304089) ^ 11) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 418981047951 := by rw [factor_1_3]; decide
      have factor_1_5 : (37 : ZMod 594253304089) ^ 46 = 46998366521 := by
        calc
          (37 : ZMod 594253304089) ^ 46 = (37 : ZMod 594253304089) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 23 * (37 : ZMod 594253304089) ^ 23 := by rw [pow_add]
          _ = 46998366521 := by rw [factor_1_4]; decide
      have factor_1_6 : (37 : ZMod 594253304089) ^ 92 = 103941398413 := by
        calc
          (37 : ZMod 594253304089) ^ 92 = (37 : ZMod 594253304089) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 46 * (37 : ZMod 594253304089) ^ 46 := by rw [pow_add]
          _ = 103941398413 := by rw [factor_1_5]; decide
      have factor_1_7 : (37 : ZMod 594253304089) ^ 184 = 149559416400 := by
        calc
          (37 : ZMod 594253304089) ^ 184 = (37 : ZMod 594253304089) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 92 * (37 : ZMod 594253304089) ^ 92 := by rw [pow_add]
          _ = 149559416400 := by rw [factor_1_6]; decide
      have factor_1_8 : (37 : ZMod 594253304089) ^ 368 = 82953151206 := by
        calc
          (37 : ZMod 594253304089) ^ 368 = (37 : ZMod 594253304089) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 184 * (37 : ZMod 594253304089) ^ 184 := by rw [pow_add]
          _ = 82953151206 := by rw [factor_1_7]; decide
      have factor_1_9 : (37 : ZMod 594253304089) ^ 737 = 564348756740 := by
        calc
          (37 : ZMod 594253304089) ^ 737 = (37 : ZMod 594253304089) ^ (368 + 368 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 368 * (37 : ZMod 594253304089) ^ 368) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 564348756740 := by rw [factor_1_8]; decide
      have factor_1_10 : (37 : ZMod 594253304089) ^ 1475 = 453859448836 := by
        calc
          (37 : ZMod 594253304089) ^ 1475 = (37 : ZMod 594253304089) ^ (737 + 737 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 737 * (37 : ZMod 594253304089) ^ 737) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 453859448836 := by rw [factor_1_9]; decide
      have factor_1_11 : (37 : ZMod 594253304089) ^ 2951 = 304257551671 := by
        calc
          (37 : ZMod 594253304089) ^ 2951 = (37 : ZMod 594253304089) ^ (1475 + 1475 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 1475 * (37 : ZMod 594253304089) ^ 1475) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 304257551671 := by rw [factor_1_10]; decide
      have factor_1_12 : (37 : ZMod 594253304089) ^ 5903 = 69264078976 := by
        calc
          (37 : ZMod 594253304089) ^ 5903 = (37 : ZMod 594253304089) ^ (2951 + 2951 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 2951 * (37 : ZMod 594253304089) ^ 2951) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 69264078976 := by rw [factor_1_11]; decide
      have factor_1_13 : (37 : ZMod 594253304089) ^ 11806 = 168550512277 := by
        calc
          (37 : ZMod 594253304089) ^ 11806 = (37 : ZMod 594253304089) ^ (5903 + 5903) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 5903 * (37 : ZMod 594253304089) ^ 5903 := by rw [pow_add]
          _ = 168550512277 := by rw [factor_1_12]; decide
      have factor_1_14 : (37 : ZMod 594253304089) ^ 23613 = 49673781424 := by
        calc
          (37 : ZMod 594253304089) ^ 23613 = (37 : ZMod 594253304089) ^ (11806 + 11806 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 11806 * (37 : ZMod 594253304089) ^ 11806) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 49673781424 := by rw [factor_1_13]; decide
      have factor_1_15 : (37 : ZMod 594253304089) ^ 47227 = 480741789054 := by
        calc
          (37 : ZMod 594253304089) ^ 47227 = (37 : ZMod 594253304089) ^ (23613 + 23613 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 23613 * (37 : ZMod 594253304089) ^ 23613) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 480741789054 := by rw [factor_1_14]; decide
      have factor_1_16 : (37 : ZMod 594253304089) ^ 94454 = 173747038592 := by
        calc
          (37 : ZMod 594253304089) ^ 94454 = (37 : ZMod 594253304089) ^ (47227 + 47227) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 47227 * (37 : ZMod 594253304089) ^ 47227 := by rw [pow_add]
          _ = 173747038592 := by rw [factor_1_15]; decide
      have factor_1_17 : (37 : ZMod 594253304089) ^ 188908 = 428163042768 := by
        calc
          (37 : ZMod 594253304089) ^ 188908 = (37 : ZMod 594253304089) ^ (94454 + 94454) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 94454 * (37 : ZMod 594253304089) ^ 94454 := by rw [pow_add]
          _ = 428163042768 := by rw [factor_1_16]; decide
      have factor_1_18 : (37 : ZMod 594253304089) ^ 377816 = 436534676661 := by
        calc
          (37 : ZMod 594253304089) ^ 377816 = (37 : ZMod 594253304089) ^ (188908 + 188908) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 188908 * (37 : ZMod 594253304089) ^ 188908 := by rw [pow_add]
          _ = 436534676661 := by rw [factor_1_17]; decide
      have factor_1_19 : (37 : ZMod 594253304089) ^ 755632 = 263219303406 := by
        calc
          (37 : ZMod 594253304089) ^ 755632 = (37 : ZMod 594253304089) ^ (377816 + 377816) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 377816 * (37 : ZMod 594253304089) ^ 377816 := by rw [pow_add]
          _ = 263219303406 := by rw [factor_1_18]; decide
      have factor_1_20 : (37 : ZMod 594253304089) ^ 1511264 = 245018975570 := by
        calc
          (37 : ZMod 594253304089) ^ 1511264 = (37 : ZMod 594253304089) ^ (755632 + 755632) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 755632 * (37 : ZMod 594253304089) ^ 755632 := by rw [pow_add]
          _ = 245018975570 := by rw [factor_1_19]; decide
      have factor_1_21 : (37 : ZMod 594253304089) ^ 3022528 = 100900648453 := by
        calc
          (37 : ZMod 594253304089) ^ 3022528 = (37 : ZMod 594253304089) ^ (1511264 + 1511264) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1511264 * (37 : ZMod 594253304089) ^ 1511264 := by rw [pow_add]
          _ = 100900648453 := by rw [factor_1_20]; decide
      have factor_1_22 : (37 : ZMod 594253304089) ^ 6045057 = 420143909390 := by
        calc
          (37 : ZMod 594253304089) ^ 6045057 = (37 : ZMod 594253304089) ^ (3022528 + 3022528 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 3022528 * (37 : ZMod 594253304089) ^ 3022528) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 420143909390 := by rw [factor_1_21]; decide
      have factor_1_23 : (37 : ZMod 594253304089) ^ 12090114 = 134184965860 := by
        calc
          (37 : ZMod 594253304089) ^ 12090114 = (37 : ZMod 594253304089) ^ (6045057 + 6045057) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 6045057 * (37 : ZMod 594253304089) ^ 6045057 := by rw [pow_add]
          _ = 134184965860 := by rw [factor_1_22]; decide
      have factor_1_24 : (37 : ZMod 594253304089) ^ 24180228 = 235669136582 := by
        calc
          (37 : ZMod 594253304089) ^ 24180228 = (37 : ZMod 594253304089) ^ (12090114 + 12090114) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 12090114 * (37 : ZMod 594253304089) ^ 12090114 := by rw [pow_add]
          _ = 235669136582 := by rw [factor_1_23]; decide
      have factor_1_25 : (37 : ZMod 594253304089) ^ 48360457 = 299460597442 := by
        calc
          (37 : ZMod 594253304089) ^ 48360457 = (37 : ZMod 594253304089) ^ (24180228 + 24180228 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 24180228 * (37 : ZMod 594253304089) ^ 24180228) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 299460597442 := by rw [factor_1_24]; decide
      have factor_1_26 : (37 : ZMod 594253304089) ^ 96720915 = 75544801368 := by
        calc
          (37 : ZMod 594253304089) ^ 96720915 = (37 : ZMod 594253304089) ^ (48360457 + 48360457 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 48360457 * (37 : ZMod 594253304089) ^ 48360457) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 75544801368 := by rw [factor_1_25]; decide
      have factor_1_27 : (37 : ZMod 594253304089) ^ 193441830 = 449290472782 := by
        calc
          (37 : ZMod 594253304089) ^ 193441830 = (37 : ZMod 594253304089) ^ (96720915 + 96720915) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 96720915 * (37 : ZMod 594253304089) ^ 96720915 := by rw [pow_add]
          _ = 449290472782 := by rw [factor_1_26]; decide
      have factor_1_28 : (37 : ZMod 594253304089) ^ 386883661 = 1835903092 := by
        calc
          (37 : ZMod 594253304089) ^ 386883661 = (37 : ZMod 594253304089) ^ (193441830 + 193441830 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 193441830 * (37 : ZMod 594253304089) ^ 193441830) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 1835903092 := by rw [factor_1_27]; decide
      have factor_1_29 : (37 : ZMod 594253304089) ^ 773767323 = 122162783037 := by
        calc
          (37 : ZMod 594253304089) ^ 773767323 = (37 : ZMod 594253304089) ^ (386883661 + 386883661 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 386883661 * (37 : ZMod 594253304089) ^ 386883661) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 122162783037 := by rw [factor_1_28]; decide
      have factor_1_30 : (37 : ZMod 594253304089) ^ 1547534646 = 42734550230 := by
        calc
          (37 : ZMod 594253304089) ^ 1547534646 = (37 : ZMod 594253304089) ^ (773767323 + 773767323) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 773767323 * (37 : ZMod 594253304089) ^ 773767323 := by rw [pow_add]
          _ = 42734550230 := by rw [factor_1_29]; decide
      have factor_1_31 : (37 : ZMod 594253304089) ^ 3095069292 = 281218469500 := by
        calc
          (37 : ZMod 594253304089) ^ 3095069292 = (37 : ZMod 594253304089) ^ (1547534646 + 1547534646) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1547534646 * (37 : ZMod 594253304089) ^ 1547534646 := by rw [pow_add]
          _ = 281218469500 := by rw [factor_1_30]; decide
      have factor_1_32 : (37 : ZMod 594253304089) ^ 6190138584 = 320559698922 := by
        calc
          (37 : ZMod 594253304089) ^ 6190138584 = (37 : ZMod 594253304089) ^ (3095069292 + 3095069292) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 3095069292 * (37 : ZMod 594253304089) ^ 3095069292 := by rw [pow_add]
          _ = 320559698922 := by rw [factor_1_31]; decide
      have factor_1_33 : (37 : ZMod 594253304089) ^ 12380277168 = 152274245176 := by
        calc
          (37 : ZMod 594253304089) ^ 12380277168 = (37 : ZMod 594253304089) ^ (6190138584 + 6190138584) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 6190138584 * (37 : ZMod 594253304089) ^ 6190138584 := by rw [pow_add]
          _ = 152274245176 := by rw [factor_1_32]; decide
      have factor_1_34 : (37 : ZMod 594253304089) ^ 24760554337 = 319715088395 := by
        calc
          (37 : ZMod 594253304089) ^ 24760554337 = (37 : ZMod 594253304089) ^ (12380277168 + 12380277168 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 12380277168 * (37 : ZMod 594253304089) ^ 12380277168) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 319715088395 := by rw [factor_1_33]; decide
      have factor_1_35 : (37 : ZMod 594253304089) ^ 49521108674 = 203633724087 := by
        calc
          (37 : ZMod 594253304089) ^ 49521108674 = (37 : ZMod 594253304089) ^ (24760554337 + 24760554337) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 24760554337 * (37 : ZMod 594253304089) ^ 24760554337 := by rw [pow_add]
          _ = 203633724087 := by rw [factor_1_34]; decide
      have factor_1_36 : (37 : ZMod 594253304089) ^ 99042217348 = 186269937542 := by
        calc
          (37 : ZMod 594253304089) ^ 99042217348 = (37 : ZMod 594253304089) ^ (49521108674 + 49521108674) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 49521108674 * (37 : ZMod 594253304089) ^ 49521108674 := by rw [pow_add]
          _ = 186269937542 := by rw [factor_1_35]; decide
      have factor_1_37 : (37 : ZMod 594253304089) ^ 198084434696 = 186269937541 := by
        calc
          (37 : ZMod 594253304089) ^ 198084434696 = (37 : ZMod 594253304089) ^ (99042217348 + 99042217348) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 99042217348 * (37 : ZMod 594253304089) ^ 99042217348 := by rw [pow_add]
          _ = 186269937541 := by rw [factor_1_36]; decide
      change (37 : ZMod 594253304089) ^ 198084434696 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (37 : ZMod 594253304089) ^ 1 = 37 := by norm_num
      have factor_2_1 : (37 : ZMod 594253304089) ^ 2 = 1369 := by
        calc
          (37 : ZMod 594253304089) ^ 2 = (37 : ZMod 594253304089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1 * (37 : ZMod 594253304089) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_2_0]; decide
      have factor_2_2 : (37 : ZMod 594253304089) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 594253304089) ^ 5 = (37 : ZMod 594253304089) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 2 * (37 : ZMod 594253304089) ^ 2) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_2_1]; decide
      have factor_2_3 : (37 : ZMod 594253304089) ^ 10 = 480889033750 := by
        calc
          (37 : ZMod 594253304089) ^ 10 = (37 : ZMod 594253304089) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 5 * (37 : ZMod 594253304089) ^ 5 := by rw [pow_add]
          _ = 480889033750 := by rw [factor_2_2]; decide
      have factor_2_4 : (37 : ZMod 594253304089) ^ 21 = 360591105509 := by
        calc
          (37 : ZMod 594253304089) ^ 21 = (37 : ZMod 594253304089) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 10 * (37 : ZMod 594253304089) ^ 10) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 360591105509 := by rw [factor_2_3]; decide
      have factor_2_5 : (37 : ZMod 594253304089) ^ 43 = 236843478201 := by
        calc
          (37 : ZMod 594253304089) ^ 43 = (37 : ZMod 594253304089) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 21 * (37 : ZMod 594253304089) ^ 21) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 236843478201 := by rw [factor_2_4]; decide
      have factor_2_6 : (37 : ZMod 594253304089) ^ 86 = 329189649350 := by
        calc
          (37 : ZMod 594253304089) ^ 86 = (37 : ZMod 594253304089) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 43 * (37 : ZMod 594253304089) ^ 43 := by rw [pow_add]
          _ = 329189649350 := by rw [factor_2_5]; decide
      have factor_2_7 : (37 : ZMod 594253304089) ^ 172 = 572876908189 := by
        calc
          (37 : ZMod 594253304089) ^ 172 = (37 : ZMod 594253304089) ^ (86 + 86) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 86 * (37 : ZMod 594253304089) ^ 86 := by rw [pow_add]
          _ = 572876908189 := by rw [factor_2_6]; decide
      have factor_2_8 : (37 : ZMod 594253304089) ^ 345 = 247855714972 := by
        calc
          (37 : ZMod 594253304089) ^ 345 = (37 : ZMod 594253304089) ^ (172 + 172 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 172 * (37 : ZMod 594253304089) ^ 172) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 247855714972 := by rw [factor_2_7]; decide
      have factor_2_9 : (37 : ZMod 594253304089) ^ 690 = 256631965711 := by
        calc
          (37 : ZMod 594253304089) ^ 690 = (37 : ZMod 594253304089) ^ (345 + 345) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 345 * (37 : ZMod 594253304089) ^ 345 := by rw [pow_add]
          _ = 256631965711 := by rw [factor_2_8]; decide
      have factor_2_10 : (37 : ZMod 594253304089) ^ 1381 = 568866996280 := by
        calc
          (37 : ZMod 594253304089) ^ 1381 = (37 : ZMod 594253304089) ^ (690 + 690 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 690 * (37 : ZMod 594253304089) ^ 690) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 568866996280 := by rw [factor_2_9]; decide
      have factor_2_11 : (37 : ZMod 594253304089) ^ 2763 = 563857876200 := by
        calc
          (37 : ZMod 594253304089) ^ 2763 = (37 : ZMod 594253304089) ^ (1381 + 1381 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 1381 * (37 : ZMod 594253304089) ^ 1381) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 563857876200 := by rw [factor_2_10]; decide
      have factor_2_12 : (37 : ZMod 594253304089) ^ 5526 = 310361399834 := by
        calc
          (37 : ZMod 594253304089) ^ 5526 = (37 : ZMod 594253304089) ^ (2763 + 2763) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2763 * (37 : ZMod 594253304089) ^ 2763 := by rw [pow_add]
          _ = 310361399834 := by rw [factor_2_11]; decide
      have factor_2_13 : (37 : ZMod 594253304089) ^ 11052 = 407356534775 := by
        calc
          (37 : ZMod 594253304089) ^ 11052 = (37 : ZMod 594253304089) ^ (5526 + 5526) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 5526 * (37 : ZMod 594253304089) ^ 5526 := by rw [pow_add]
          _ = 407356534775 := by rw [factor_2_12]; decide
      have factor_2_14 : (37 : ZMod 594253304089) ^ 22104 = 57098076612 := by
        calc
          (37 : ZMod 594253304089) ^ 22104 = (37 : ZMod 594253304089) ^ (11052 + 11052) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 11052 * (37 : ZMod 594253304089) ^ 11052 := by rw [pow_add]
          _ = 57098076612 := by rw [factor_2_13]; decide
      have factor_2_15 : (37 : ZMod 594253304089) ^ 44208 = 352311716719 := by
        calc
          (37 : ZMod 594253304089) ^ 44208 = (37 : ZMod 594253304089) ^ (22104 + 22104) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 22104 * (37 : ZMod 594253304089) ^ 22104 := by rw [pow_add]
          _ = 352311716719 := by rw [factor_2_14]; decide
      have factor_2_16 : (37 : ZMod 594253304089) ^ 88417 = 584708472660 := by
        calc
          (37 : ZMod 594253304089) ^ 88417 = (37 : ZMod 594253304089) ^ (44208 + 44208 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 44208 * (37 : ZMod 594253304089) ^ 44208) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 584708472660 := by rw [factor_2_15]; decide
      have factor_2_17 : (37 : ZMod 594253304089) ^ 176834 = 71630822837 := by
        calc
          (37 : ZMod 594253304089) ^ 176834 = (37 : ZMod 594253304089) ^ (88417 + 88417) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 88417 * (37 : ZMod 594253304089) ^ 88417 := by rw [pow_add]
          _ = 71630822837 := by rw [factor_2_16]; decide
      have factor_2_18 : (37 : ZMod 594253304089) ^ 353668 = 333597898227 := by
        calc
          (37 : ZMod 594253304089) ^ 353668 = (37 : ZMod 594253304089) ^ (176834 + 176834) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 176834 * (37 : ZMod 594253304089) ^ 176834 := by rw [pow_add]
          _ = 333597898227 := by rw [factor_2_17]; decide
      have factor_2_19 : (37 : ZMod 594253304089) ^ 707336 = 273519531254 := by
        calc
          (37 : ZMod 594253304089) ^ 707336 = (37 : ZMod 594253304089) ^ (353668 + 353668) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 353668 * (37 : ZMod 594253304089) ^ 353668 := by rw [pow_add]
          _ = 273519531254 := by rw [factor_2_18]; decide
      have factor_2_20 : (37 : ZMod 594253304089) ^ 1414673 = 211275156291 := by
        calc
          (37 : ZMod 594253304089) ^ 1414673 = (37 : ZMod 594253304089) ^ (707336 + 707336 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 707336 * (37 : ZMod 594253304089) ^ 707336) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 211275156291 := by rw [factor_2_19]; decide
      have factor_2_21 : (37 : ZMod 594253304089) ^ 2829346 = 303959473621 := by
        calc
          (37 : ZMod 594253304089) ^ 2829346 = (37 : ZMod 594253304089) ^ (1414673 + 1414673) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1414673 * (37 : ZMod 594253304089) ^ 1414673 := by rw [pow_add]
          _ = 303959473621 := by rw [factor_2_20]; decide
      have factor_2_22 : (37 : ZMod 594253304089) ^ 5658693 = 169731920316 := by
        calc
          (37 : ZMod 594253304089) ^ 5658693 = (37 : ZMod 594253304089) ^ (2829346 + 2829346 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 2829346 * (37 : ZMod 594253304089) ^ 2829346) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 169731920316 := by rw [factor_2_21]; decide
      have factor_2_23 : (37 : ZMod 594253304089) ^ 11317386 = 508057780746 := by
        calc
          (37 : ZMod 594253304089) ^ 11317386 = (37 : ZMod 594253304089) ^ (5658693 + 5658693) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 5658693 * (37 : ZMod 594253304089) ^ 5658693 := by rw [pow_add]
          _ = 508057780746 := by rw [factor_2_22]; decide
      have factor_2_24 : (37 : ZMod 594253304089) ^ 22634772 = 124751368955 := by
        calc
          (37 : ZMod 594253304089) ^ 22634772 = (37 : ZMod 594253304089) ^ (11317386 + 11317386) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 11317386 * (37 : ZMod 594253304089) ^ 11317386 := by rw [pow_add]
          _ = 124751368955 := by rw [factor_2_23]; decide
      have factor_2_25 : (37 : ZMod 594253304089) ^ 45269544 = 301447175759 := by
        calc
          (37 : ZMod 594253304089) ^ 45269544 = (37 : ZMod 594253304089) ^ (22634772 + 22634772) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 22634772 * (37 : ZMod 594253304089) ^ 22634772 := by rw [pow_add]
          _ = 301447175759 := by rw [factor_2_24]; decide
      change (37 : ZMod 594253304089) ^ 45269544 ≠ 1
      rw [factor_2_25]
      decide
    ·
      have factor_3_0 : (37 : ZMod 594253304089) ^ 1 = 37 := by norm_num
      have factor_3_1 : (37 : ZMod 594253304089) ^ 2 = 1369 := by
        calc
          (37 : ZMod 594253304089) ^ 2 = (37 : ZMod 594253304089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 1 * (37 : ZMod 594253304089) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_3_0]; decide
      have factor_3_2 : (37 : ZMod 594253304089) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 594253304089) ^ 4 = (37 : ZMod 594253304089) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2 * (37 : ZMod 594253304089) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_3_1]; decide
      have factor_3_3 : (37 : ZMod 594253304089) ^ 9 = 414519503675 := by
        calc
          (37 : ZMod 594253304089) ^ 9 = (37 : ZMod 594253304089) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 4 * (37 : ZMod 594253304089) ^ 4) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 414519503675 := by rw [factor_3_2]; decide
      have factor_3_4 : (37 : ZMod 594253304089) ^ 19 = 135261774052 := by
        calc
          (37 : ZMod 594253304089) ^ 19 = (37 : ZMod 594253304089) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 9 * (37 : ZMod 594253304089) ^ 9) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 135261774052 := by rw [factor_3_3]; decide
      have factor_3_5 : (37 : ZMod 594253304089) ^ 38 = 533958575163 := by
        calc
          (37 : ZMod 594253304089) ^ 38 = (37 : ZMod 594253304089) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 19 * (37 : ZMod 594253304089) ^ 19 := by rw [pow_add]
          _ = 533958575163 := by rw [factor_3_4]; decide
      have factor_3_6 : (37 : ZMod 594253304089) ^ 76 = 12404544689 := by
        calc
          (37 : ZMod 594253304089) ^ 76 = (37 : ZMod 594253304089) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 38 * (37 : ZMod 594253304089) ^ 38 := by rw [pow_add]
          _ = 12404544689 := by rw [factor_3_5]; decide
      have factor_3_7 : (37 : ZMod 594253304089) ^ 153 = 163681133009 := by
        calc
          (37 : ZMod 594253304089) ^ 153 = (37 : ZMod 594253304089) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 76 * (37 : ZMod 594253304089) ^ 76) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 163681133009 := by rw [factor_3_6]; decide
      have factor_3_8 : (37 : ZMod 594253304089) ^ 307 = 481163014966 := by
        calc
          (37 : ZMod 594253304089) ^ 307 = (37 : ZMod 594253304089) ^ (153 + 153 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 153 * (37 : ZMod 594253304089) ^ 153) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 481163014966 := by rw [factor_3_7]; decide
      have factor_3_9 : (37 : ZMod 594253304089) ^ 615 = 2733849589 := by
        calc
          (37 : ZMod 594253304089) ^ 615 = (37 : ZMod 594253304089) ^ (307 + 307 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 307 * (37 : ZMod 594253304089) ^ 307) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 2733849589 := by rw [factor_3_8]; decide
      have factor_3_10 : (37 : ZMod 594253304089) ^ 1230 = 261695250497 := by
        calc
          (37 : ZMod 594253304089) ^ 1230 = (37 : ZMod 594253304089) ^ (615 + 615) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 615 * (37 : ZMod 594253304089) ^ 615 := by rw [pow_add]
          _ = 261695250497 := by rw [factor_3_9]; decide
      have factor_3_11 : (37 : ZMod 594253304089) ^ 2461 = 316215548625 := by
        calc
          (37 : ZMod 594253304089) ^ 2461 = (37 : ZMod 594253304089) ^ (1230 + 1230 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 1230 * (37 : ZMod 594253304089) ^ 1230) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 316215548625 := by rw [factor_3_10]; decide
      have factor_3_12 : (37 : ZMod 594253304089) ^ 4922 = 451293435701 := by
        calc
          (37 : ZMod 594253304089) ^ 4922 = (37 : ZMod 594253304089) ^ (2461 + 2461) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 2461 * (37 : ZMod 594253304089) ^ 2461 := by rw [pow_add]
          _ = 451293435701 := by rw [factor_3_11]; decide
      have factor_3_13 : (37 : ZMod 594253304089) ^ 9845 = 286854490905 := by
        calc
          (37 : ZMod 594253304089) ^ 9845 = (37 : ZMod 594253304089) ^ (4922 + 4922 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 4922 * (37 : ZMod 594253304089) ^ 4922) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 286854490905 := by rw [factor_3_12]; decide
      have factor_3_14 : (37 : ZMod 594253304089) ^ 19690 = 76170329191 := by
        calc
          (37 : ZMod 594253304089) ^ 19690 = (37 : ZMod 594253304089) ^ (9845 + 9845) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 9845 * (37 : ZMod 594253304089) ^ 9845 := by rw [pow_add]
          _ = 76170329191 := by rw [factor_3_13]; decide
      have factor_3_15 : (37 : ZMod 594253304089) ^ 39381 = 273959403899 := by
        calc
          (37 : ZMod 594253304089) ^ 39381 = (37 : ZMod 594253304089) ^ (19690 + 19690 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = ((37 : ZMod 594253304089) ^ 19690 * (37 : ZMod 594253304089) ^ 19690) * (37 : ZMod 594253304089) := by rw [pow_succ, pow_add]
          _ = 273959403899 := by rw [factor_3_14]; decide
      have factor_3_16 : (37 : ZMod 594253304089) ^ 78762 = 552008274992 := by
        calc
          (37 : ZMod 594253304089) ^ 78762 = (37 : ZMod 594253304089) ^ (39381 + 39381) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 39381 * (37 : ZMod 594253304089) ^ 39381 := by rw [pow_add]
          _ = 552008274992 := by rw [factor_3_15]; decide
      have factor_3_17 : (37 : ZMod 594253304089) ^ 157524 = 442154846969 := by
        calc
          (37 : ZMod 594253304089) ^ 157524 = (37 : ZMod 594253304089) ^ (78762 + 78762) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 78762 * (37 : ZMod 594253304089) ^ 78762 := by rw [pow_add]
          _ = 442154846969 := by rw [factor_3_16]; decide
      have factor_3_18 : (37 : ZMod 594253304089) ^ 315048 = 399246837882 := by
        calc
          (37 : ZMod 594253304089) ^ 315048 = (37 : ZMod 594253304089) ^ (157524 + 157524) :=
            congrArg (fun n : ℕ => (37 : ZMod 594253304089) ^ n) (by norm_num)
          _ = (37 : ZMod 594253304089) ^ 157524 * (37 : ZMod 594253304089) ^ 157524 := by rw [pow_add]
          _ = 399246837882 := by rw [factor_3_17]; decide
      change (37 : ZMod 594253304089) ^ 315048 ≠ 1
      rw [factor_3_18]
      decide

#print axioms prime_lucas_594253304089

end TotientTailPeriodKiller
end Erdos249257
