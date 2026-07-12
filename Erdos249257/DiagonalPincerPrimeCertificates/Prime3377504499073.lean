import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3377504499073 : Nat.Prime 3377504499073 := by
  apply lucas_primality 3377504499073 (5 : ZMod 3377504499073)
  ·
      have fermat_0 : (5 : ZMod 3377504499073) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 3377504499073) ^ 3 = 125 := by
        calc
          (5 : ZMod 3377504499073) ^ 3 = (5 : ZMod 3377504499073) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1 * (5 : ZMod 3377504499073) ^ 1) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 3377504499073) ^ 6 = 15625 := by
        calc
          (5 : ZMod 3377504499073) ^ 6 = (5 : ZMod 3377504499073) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 3 * (5 : ZMod 3377504499073) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 3377504499073) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 3377504499073) ^ 12 = (5 : ZMod 3377504499073) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 6 * (5 : ZMod 3377504499073) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 3377504499073) ^ 24 = 1822880249394 := by
        calc
          (5 : ZMod 3377504499073) ^ 24 = (5 : ZMod 3377504499073) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 12 * (5 : ZMod 3377504499073) ^ 12 := by rw [pow_add]
          _ = 1822880249394 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 3377504499073) ^ 49 = 2152614979733 := by
        calc
          (5 : ZMod 3377504499073) ^ 49 = (5 : ZMod 3377504499073) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 24 * (5 : ZMod 3377504499073) ^ 24) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2152614979733 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 3377504499073) ^ 98 = 1709260071508 := by
        calc
          (5 : ZMod 3377504499073) ^ 98 = (5 : ZMod 3377504499073) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 49 * (5 : ZMod 3377504499073) ^ 49 := by rw [pow_add]
          _ = 1709260071508 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 3377504499073) ^ 196 = 3305600131802 := by
        calc
          (5 : ZMod 3377504499073) ^ 196 = (5 : ZMod 3377504499073) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 98 * (5 : ZMod 3377504499073) ^ 98 := by rw [pow_add]
          _ = 3305600131802 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 3377504499073) ^ 393 = 2447448509664 := by
        calc
          (5 : ZMod 3377504499073) ^ 393 = (5 : ZMod 3377504499073) ^ (196 + 196 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 196 * (5 : ZMod 3377504499073) ^ 196) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2447448509664 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 3377504499073) ^ 786 = 373040450826 := by
        calc
          (5 : ZMod 3377504499073) ^ 786 = (5 : ZMod 3377504499073) ^ (393 + 393) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 393 * (5 : ZMod 3377504499073) ^ 393 := by rw [pow_add]
          _ = 373040450826 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 3377504499073) ^ 1572 = 2637676325931 := by
        calc
          (5 : ZMod 3377504499073) ^ 1572 = (5 : ZMod 3377504499073) ^ (786 + 786) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 786 * (5 : ZMod 3377504499073) ^ 786 := by rw [pow_add]
          _ = 2637676325931 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 3377504499073) ^ 3145 = 2936972885001 := by
        calc
          (5 : ZMod 3377504499073) ^ 3145 = (5 : ZMod 3377504499073) ^ (1572 + 1572 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1572 * (5 : ZMod 3377504499073) ^ 1572) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2936972885001 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 3377504499073) ^ 6291 = 2840767890748 := by
        calc
          (5 : ZMod 3377504499073) ^ 6291 = (5 : ZMod 3377504499073) ^ (3145 + 3145 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 3145 * (5 : ZMod 3377504499073) ^ 3145) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2840767890748 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 3377504499073) ^ 12582 = 265585392154 := by
        calc
          (5 : ZMod 3377504499073) ^ 12582 = (5 : ZMod 3377504499073) ^ (6291 + 6291) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 6291 * (5 : ZMod 3377504499073) ^ 6291 := by rw [pow_add]
          _ = 265585392154 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 3377504499073) ^ 25164 = 804420924652 := by
        calc
          (5 : ZMod 3377504499073) ^ 25164 = (5 : ZMod 3377504499073) ^ (12582 + 12582) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 12582 * (5 : ZMod 3377504499073) ^ 12582 := by rw [pow_add]
          _ = 804420924652 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 3377504499073) ^ 50328 = 1465170151687 := by
        calc
          (5 : ZMod 3377504499073) ^ 50328 = (5 : ZMod 3377504499073) ^ (25164 + 25164) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 25164 * (5 : ZMod 3377504499073) ^ 25164 := by rw [pow_add]
          _ = 1465170151687 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 3377504499073) ^ 100657 = 1964063780864 := by
        calc
          (5 : ZMod 3377504499073) ^ 100657 = (5 : ZMod 3377504499073) ^ (50328 + 50328 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 50328 * (5 : ZMod 3377504499073) ^ 50328) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1964063780864 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 3377504499073) ^ 201314 = 1512707512576 := by
        calc
          (5 : ZMod 3377504499073) ^ 201314 = (5 : ZMod 3377504499073) ^ (100657 + 100657) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 100657 * (5 : ZMod 3377504499073) ^ 100657 := by rw [pow_add]
          _ = 1512707512576 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 3377504499073) ^ 402629 = 1338909566013 := by
        calc
          (5 : ZMod 3377504499073) ^ 402629 = (5 : ZMod 3377504499073) ^ (201314 + 201314 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 201314 * (5 : ZMod 3377504499073) ^ 201314) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1338909566013 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 3377504499073) ^ 805259 = 2102207640323 := by
        calc
          (5 : ZMod 3377504499073) ^ 805259 = (5 : ZMod 3377504499073) ^ (402629 + 402629 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 402629 * (5 : ZMod 3377504499073) ^ 402629) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2102207640323 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 3377504499073) ^ 1610519 = 1708398374334 := by
        calc
          (5 : ZMod 3377504499073) ^ 1610519 = (5 : ZMod 3377504499073) ^ (805259 + 805259 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 805259 * (5 : ZMod 3377504499073) ^ 805259) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1708398374334 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 3377504499073) ^ 3221039 = 1820765166484 := by
        calc
          (5 : ZMod 3377504499073) ^ 3221039 = (5 : ZMod 3377504499073) ^ (1610519 + 1610519 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1610519 * (5 : ZMod 3377504499073) ^ 1610519) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1820765166484 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 3377504499073) ^ 6442078 = 309795800228 := by
        calc
          (5 : ZMod 3377504499073) ^ 6442078 = (5 : ZMod 3377504499073) ^ (3221039 + 3221039) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 3221039 * (5 : ZMod 3377504499073) ^ 3221039 := by rw [pow_add]
          _ = 309795800228 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 3377504499073) ^ 12884157 = 1822538645249 := by
        calc
          (5 : ZMod 3377504499073) ^ 12884157 = (5 : ZMod 3377504499073) ^ (6442078 + 6442078 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 6442078 * (5 : ZMod 3377504499073) ^ 6442078) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1822538645249 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 3377504499073) ^ 25768314 = 77592921753 := by
        calc
          (5 : ZMod 3377504499073) ^ 25768314 = (5 : ZMod 3377504499073) ^ (12884157 + 12884157) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 12884157 * (5 : ZMod 3377504499073) ^ 12884157 := by rw [pow_add]
          _ = 77592921753 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 3377504499073) ^ 51536628 = 3096074880236 := by
        calc
          (5 : ZMod 3377504499073) ^ 51536628 = (5 : ZMod 3377504499073) ^ (25768314 + 25768314) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 25768314 * (5 : ZMod 3377504499073) ^ 25768314 := by rw [pow_add]
          _ = 3096074880236 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 3377504499073) ^ 103073257 = 1655688311306 := by
        calc
          (5 : ZMod 3377504499073) ^ 103073257 = (5 : ZMod 3377504499073) ^ (51536628 + 51536628 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 51536628 * (5 : ZMod 3377504499073) ^ 51536628) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1655688311306 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 3377504499073) ^ 206146514 = 1134848882026 := by
        calc
          (5 : ZMod 3377504499073) ^ 206146514 = (5 : ZMod 3377504499073) ^ (103073257 + 103073257) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 103073257 * (5 : ZMod 3377504499073) ^ 103073257 := by rw [pow_add]
          _ = 1134848882026 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 3377504499073) ^ 412293029 = 169333078657 := by
        calc
          (5 : ZMod 3377504499073) ^ 412293029 = (5 : ZMod 3377504499073) ^ (206146514 + 206146514 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 206146514 * (5 : ZMod 3377504499073) ^ 206146514) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 169333078657 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 3377504499073) ^ 824586059 = 2637681870439 := by
        calc
          (5 : ZMod 3377504499073) ^ 824586059 = (5 : ZMod 3377504499073) ^ (412293029 + 412293029 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 412293029 * (5 : ZMod 3377504499073) ^ 412293029) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2637681870439 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 3377504499073) ^ 1649172118 = 1691960653725 := by
        calc
          (5 : ZMod 3377504499073) ^ 1649172118 = (5 : ZMod 3377504499073) ^ (824586059 + 824586059) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 824586059 * (5 : ZMod 3377504499073) ^ 824586059 := by rw [pow_add]
          _ = 1691960653725 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 3377504499073) ^ 3298344237 = 1903847006843 := by
        calc
          (5 : ZMod 3377504499073) ^ 3298344237 = (5 : ZMod 3377504499073) ^ (1649172118 + 1649172118 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1649172118 * (5 : ZMod 3377504499073) ^ 1649172118) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1903847006843 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 3377504499073) ^ 6596688474 = 3271035582140 := by
        calc
          (5 : ZMod 3377504499073) ^ 6596688474 = (5 : ZMod 3377504499073) ^ (3298344237 + 3298344237) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 3298344237 * (5 : ZMod 3377504499073) ^ 3298344237 := by rw [pow_add]
          _ = 3271035582140 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 3377504499073) ^ 13193376949 = 692918299390 := by
        calc
          (5 : ZMod 3377504499073) ^ 13193376949 = (5 : ZMod 3377504499073) ^ (6596688474 + 6596688474 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 6596688474 * (5 : ZMod 3377504499073) ^ 6596688474) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 692918299390 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 3377504499073) ^ 26386753899 = 1641502241956 := by
        calc
          (5 : ZMod 3377504499073) ^ 26386753899 = (5 : ZMod 3377504499073) ^ (13193376949 + 13193376949 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 13193376949 * (5 : ZMod 3377504499073) ^ 13193376949) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1641502241956 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 3377504499073) ^ 52773507798 = 97064325550 := by
        calc
          (5 : ZMod 3377504499073) ^ 52773507798 = (5 : ZMod 3377504499073) ^ (26386753899 + 26386753899) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 26386753899 * (5 : ZMod 3377504499073) ^ 26386753899 := by rw [pow_add]
          _ = 97064325550 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 3377504499073) ^ 105547015596 = 1012008823335 := by
        calc
          (5 : ZMod 3377504499073) ^ 105547015596 = (5 : ZMod 3377504499073) ^ (52773507798 + 52773507798) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 52773507798 * (5 : ZMod 3377504499073) ^ 52773507798 := by rw [pow_add]
          _ = 1012008823335 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 3377504499073) ^ 211094031192 = 2457925438501 := by
        calc
          (5 : ZMod 3377504499073) ^ 211094031192 = (5 : ZMod 3377504499073) ^ (105547015596 + 105547015596) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 105547015596 * (5 : ZMod 3377504499073) ^ 105547015596 := by rw [pow_add]
          _ = 2457925438501 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 3377504499073) ^ 422188062384 = 1123564031558 := by
        calc
          (5 : ZMod 3377504499073) ^ 422188062384 = (5 : ZMod 3377504499073) ^ (211094031192 + 211094031192) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 211094031192 * (5 : ZMod 3377504499073) ^ 211094031192 := by rw [pow_add]
          _ = 1123564031558 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 3377504499073) ^ 844376124768 = 354518784811 := by
        calc
          (5 : ZMod 3377504499073) ^ 844376124768 = (5 : ZMod 3377504499073) ^ (422188062384 + 422188062384) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 422188062384 * (5 : ZMod 3377504499073) ^ 422188062384 := by rw [pow_add]
          _ = 354518784811 := by rw [fermat_38]; decide
      have fermat_40 : (5 : ZMod 3377504499073) ^ 1688752249536 = 3377504499072 := by
        calc
          (5 : ZMod 3377504499073) ^ 1688752249536 = (5 : ZMod 3377504499073) ^ (844376124768 + 844376124768) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 844376124768 * (5 : ZMod 3377504499073) ^ 844376124768 := by rw [pow_add]
          _ = 3377504499072 := by rw [fermat_39]; decide
      have fermat_41 : (5 : ZMod 3377504499073) ^ 3377504499072 = 1 := by
        calc
          (5 : ZMod 3377504499073) ^ 3377504499072 = (5 : ZMod 3377504499073) ^ (1688752249536 + 1688752249536) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1688752249536 * (5 : ZMod 3377504499073) ^ 1688752249536 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (11, 1), (19, 1), (109, 1), (386093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (11, 1), (19, 1), (109, 1), (386093, 1)] : List FactorBlock).map factorBlockValue).prod = 3377504499073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 3377504499073) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 3377504499073) ^ 3 = 125 := by
        calc
          (5 : ZMod 3377504499073) ^ 3 = (5 : ZMod 3377504499073) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1 * (5 : ZMod 3377504499073) ^ 1) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 3377504499073) ^ 6 = 15625 := by
        calc
          (5 : ZMod 3377504499073) ^ 6 = (5 : ZMod 3377504499073) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 3 * (5 : ZMod 3377504499073) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 3377504499073) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 3377504499073) ^ 12 = (5 : ZMod 3377504499073) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 6 * (5 : ZMod 3377504499073) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 3377504499073) ^ 24 = 1822880249394 := by
        calc
          (5 : ZMod 3377504499073) ^ 24 = (5 : ZMod 3377504499073) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 12 * (5 : ZMod 3377504499073) ^ 12 := by rw [pow_add]
          _ = 1822880249394 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 3377504499073) ^ 49 = 2152614979733 := by
        calc
          (5 : ZMod 3377504499073) ^ 49 = (5 : ZMod 3377504499073) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 24 * (5 : ZMod 3377504499073) ^ 24) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2152614979733 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 3377504499073) ^ 98 = 1709260071508 := by
        calc
          (5 : ZMod 3377504499073) ^ 98 = (5 : ZMod 3377504499073) ^ (49 + 49) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 49 * (5 : ZMod 3377504499073) ^ 49 := by rw [pow_add]
          _ = 1709260071508 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 3377504499073) ^ 196 = 3305600131802 := by
        calc
          (5 : ZMod 3377504499073) ^ 196 = (5 : ZMod 3377504499073) ^ (98 + 98) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 98 * (5 : ZMod 3377504499073) ^ 98 := by rw [pow_add]
          _ = 3305600131802 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 3377504499073) ^ 393 = 2447448509664 := by
        calc
          (5 : ZMod 3377504499073) ^ 393 = (5 : ZMod 3377504499073) ^ (196 + 196 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 196 * (5 : ZMod 3377504499073) ^ 196) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2447448509664 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 3377504499073) ^ 786 = 373040450826 := by
        calc
          (5 : ZMod 3377504499073) ^ 786 = (5 : ZMod 3377504499073) ^ (393 + 393) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 393 * (5 : ZMod 3377504499073) ^ 393 := by rw [pow_add]
          _ = 373040450826 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 3377504499073) ^ 1572 = 2637676325931 := by
        calc
          (5 : ZMod 3377504499073) ^ 1572 = (5 : ZMod 3377504499073) ^ (786 + 786) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 786 * (5 : ZMod 3377504499073) ^ 786 := by rw [pow_add]
          _ = 2637676325931 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 3377504499073) ^ 3145 = 2936972885001 := by
        calc
          (5 : ZMod 3377504499073) ^ 3145 = (5 : ZMod 3377504499073) ^ (1572 + 1572 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1572 * (5 : ZMod 3377504499073) ^ 1572) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2936972885001 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 3377504499073) ^ 6291 = 2840767890748 := by
        calc
          (5 : ZMod 3377504499073) ^ 6291 = (5 : ZMod 3377504499073) ^ (3145 + 3145 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 3145 * (5 : ZMod 3377504499073) ^ 3145) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2840767890748 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 3377504499073) ^ 12582 = 265585392154 := by
        calc
          (5 : ZMod 3377504499073) ^ 12582 = (5 : ZMod 3377504499073) ^ (6291 + 6291) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 6291 * (5 : ZMod 3377504499073) ^ 6291 := by rw [pow_add]
          _ = 265585392154 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 3377504499073) ^ 25164 = 804420924652 := by
        calc
          (5 : ZMod 3377504499073) ^ 25164 = (5 : ZMod 3377504499073) ^ (12582 + 12582) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 12582 * (5 : ZMod 3377504499073) ^ 12582 := by rw [pow_add]
          _ = 804420924652 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 3377504499073) ^ 50328 = 1465170151687 := by
        calc
          (5 : ZMod 3377504499073) ^ 50328 = (5 : ZMod 3377504499073) ^ (25164 + 25164) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 25164 * (5 : ZMod 3377504499073) ^ 25164 := by rw [pow_add]
          _ = 1465170151687 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 3377504499073) ^ 100657 = 1964063780864 := by
        calc
          (5 : ZMod 3377504499073) ^ 100657 = (5 : ZMod 3377504499073) ^ (50328 + 50328 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 50328 * (5 : ZMod 3377504499073) ^ 50328) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1964063780864 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 3377504499073) ^ 201314 = 1512707512576 := by
        calc
          (5 : ZMod 3377504499073) ^ 201314 = (5 : ZMod 3377504499073) ^ (100657 + 100657) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 100657 * (5 : ZMod 3377504499073) ^ 100657 := by rw [pow_add]
          _ = 1512707512576 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 3377504499073) ^ 402629 = 1338909566013 := by
        calc
          (5 : ZMod 3377504499073) ^ 402629 = (5 : ZMod 3377504499073) ^ (201314 + 201314 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 201314 * (5 : ZMod 3377504499073) ^ 201314) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1338909566013 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 3377504499073) ^ 805259 = 2102207640323 := by
        calc
          (5 : ZMod 3377504499073) ^ 805259 = (5 : ZMod 3377504499073) ^ (402629 + 402629 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 402629 * (5 : ZMod 3377504499073) ^ 402629) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2102207640323 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 3377504499073) ^ 1610519 = 1708398374334 := by
        calc
          (5 : ZMod 3377504499073) ^ 1610519 = (5 : ZMod 3377504499073) ^ (805259 + 805259 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 805259 * (5 : ZMod 3377504499073) ^ 805259) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1708398374334 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 3377504499073) ^ 3221039 = 1820765166484 := by
        calc
          (5 : ZMod 3377504499073) ^ 3221039 = (5 : ZMod 3377504499073) ^ (1610519 + 1610519 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1610519 * (5 : ZMod 3377504499073) ^ 1610519) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1820765166484 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 3377504499073) ^ 6442078 = 309795800228 := by
        calc
          (5 : ZMod 3377504499073) ^ 6442078 = (5 : ZMod 3377504499073) ^ (3221039 + 3221039) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 3221039 * (5 : ZMod 3377504499073) ^ 3221039 := by rw [pow_add]
          _ = 309795800228 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 3377504499073) ^ 12884157 = 1822538645249 := by
        calc
          (5 : ZMod 3377504499073) ^ 12884157 = (5 : ZMod 3377504499073) ^ (6442078 + 6442078 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 6442078 * (5 : ZMod 3377504499073) ^ 6442078) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1822538645249 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 3377504499073) ^ 25768314 = 77592921753 := by
        calc
          (5 : ZMod 3377504499073) ^ 25768314 = (5 : ZMod 3377504499073) ^ (12884157 + 12884157) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 12884157 * (5 : ZMod 3377504499073) ^ 12884157 := by rw [pow_add]
          _ = 77592921753 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 3377504499073) ^ 51536628 = 3096074880236 := by
        calc
          (5 : ZMod 3377504499073) ^ 51536628 = (5 : ZMod 3377504499073) ^ (25768314 + 25768314) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 25768314 * (5 : ZMod 3377504499073) ^ 25768314 := by rw [pow_add]
          _ = 3096074880236 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 3377504499073) ^ 103073257 = 1655688311306 := by
        calc
          (5 : ZMod 3377504499073) ^ 103073257 = (5 : ZMod 3377504499073) ^ (51536628 + 51536628 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 51536628 * (5 : ZMod 3377504499073) ^ 51536628) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1655688311306 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 3377504499073) ^ 206146514 = 1134848882026 := by
        calc
          (5 : ZMod 3377504499073) ^ 206146514 = (5 : ZMod 3377504499073) ^ (103073257 + 103073257) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 103073257 * (5 : ZMod 3377504499073) ^ 103073257 := by rw [pow_add]
          _ = 1134848882026 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 3377504499073) ^ 412293029 = 169333078657 := by
        calc
          (5 : ZMod 3377504499073) ^ 412293029 = (5 : ZMod 3377504499073) ^ (206146514 + 206146514 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 206146514 * (5 : ZMod 3377504499073) ^ 206146514) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 169333078657 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 3377504499073) ^ 824586059 = 2637681870439 := by
        calc
          (5 : ZMod 3377504499073) ^ 824586059 = (5 : ZMod 3377504499073) ^ (412293029 + 412293029 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 412293029 * (5 : ZMod 3377504499073) ^ 412293029) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2637681870439 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 3377504499073) ^ 1649172118 = 1691960653725 := by
        calc
          (5 : ZMod 3377504499073) ^ 1649172118 = (5 : ZMod 3377504499073) ^ (824586059 + 824586059) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 824586059 * (5 : ZMod 3377504499073) ^ 824586059 := by rw [pow_add]
          _ = 1691960653725 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 3377504499073) ^ 3298344237 = 1903847006843 := by
        calc
          (5 : ZMod 3377504499073) ^ 3298344237 = (5 : ZMod 3377504499073) ^ (1649172118 + 1649172118 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1649172118 * (5 : ZMod 3377504499073) ^ 1649172118) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1903847006843 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 3377504499073) ^ 6596688474 = 3271035582140 := by
        calc
          (5 : ZMod 3377504499073) ^ 6596688474 = (5 : ZMod 3377504499073) ^ (3298344237 + 3298344237) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 3298344237 * (5 : ZMod 3377504499073) ^ 3298344237 := by rw [pow_add]
          _ = 3271035582140 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 3377504499073) ^ 13193376949 = 692918299390 := by
        calc
          (5 : ZMod 3377504499073) ^ 13193376949 = (5 : ZMod 3377504499073) ^ (6596688474 + 6596688474 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 6596688474 * (5 : ZMod 3377504499073) ^ 6596688474) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 692918299390 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 3377504499073) ^ 26386753899 = 1641502241956 := by
        calc
          (5 : ZMod 3377504499073) ^ 26386753899 = (5 : ZMod 3377504499073) ^ (13193376949 + 13193376949 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 13193376949 * (5 : ZMod 3377504499073) ^ 13193376949) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1641502241956 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 3377504499073) ^ 52773507798 = 97064325550 := by
        calc
          (5 : ZMod 3377504499073) ^ 52773507798 = (5 : ZMod 3377504499073) ^ (26386753899 + 26386753899) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 26386753899 * (5 : ZMod 3377504499073) ^ 26386753899 := by rw [pow_add]
          _ = 97064325550 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 3377504499073) ^ 105547015596 = 1012008823335 := by
        calc
          (5 : ZMod 3377504499073) ^ 105547015596 = (5 : ZMod 3377504499073) ^ (52773507798 + 52773507798) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 52773507798 * (5 : ZMod 3377504499073) ^ 52773507798 := by rw [pow_add]
          _ = 1012008823335 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 3377504499073) ^ 211094031192 = 2457925438501 := by
        calc
          (5 : ZMod 3377504499073) ^ 211094031192 = (5 : ZMod 3377504499073) ^ (105547015596 + 105547015596) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 105547015596 * (5 : ZMod 3377504499073) ^ 105547015596 := by rw [pow_add]
          _ = 2457925438501 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 3377504499073) ^ 422188062384 = 1123564031558 := by
        calc
          (5 : ZMod 3377504499073) ^ 422188062384 = (5 : ZMod 3377504499073) ^ (211094031192 + 211094031192) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 211094031192 * (5 : ZMod 3377504499073) ^ 211094031192 := by rw [pow_add]
          _ = 1123564031558 := by rw [factor_0_37]; decide
      have factor_0_39 : (5 : ZMod 3377504499073) ^ 844376124768 = 354518784811 := by
        calc
          (5 : ZMod 3377504499073) ^ 844376124768 = (5 : ZMod 3377504499073) ^ (422188062384 + 422188062384) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 422188062384 * (5 : ZMod 3377504499073) ^ 422188062384 := by rw [pow_add]
          _ = 354518784811 := by rw [factor_0_38]; decide
      have factor_0_40 : (5 : ZMod 3377504499073) ^ 1688752249536 = 3377504499072 := by
        calc
          (5 : ZMod 3377504499073) ^ 1688752249536 = (5 : ZMod 3377504499073) ^ (844376124768 + 844376124768) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 844376124768 * (5 : ZMod 3377504499073) ^ 844376124768 := by rw [pow_add]
          _ = 3377504499072 := by rw [factor_0_39]; decide
      change (5 : ZMod 3377504499073) ^ 1688752249536 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (5 : ZMod 3377504499073) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 3377504499073) ^ 2 = 25 := by
        calc
          (5 : ZMod 3377504499073) ^ 2 = (5 : ZMod 3377504499073) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1 * (5 : ZMod 3377504499073) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 3377504499073) ^ 4 = 625 := by
        calc
          (5 : ZMod 3377504499073) ^ 4 = (5 : ZMod 3377504499073) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2 * (5 : ZMod 3377504499073) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 3377504499073) ^ 8 = 390625 := by
        calc
          (5 : ZMod 3377504499073) ^ 8 = (5 : ZMod 3377504499073) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4 * (5 : ZMod 3377504499073) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 3377504499073) ^ 16 = 152587890625 := by
        calc
          (5 : ZMod 3377504499073) ^ 16 = (5 : ZMod 3377504499073) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 8 * (5 : ZMod 3377504499073) ^ 8 := by rw [pow_add]
          _ = 152587890625 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 3377504499073) ^ 32 = 211402466025 := by
        calc
          (5 : ZMod 3377504499073) ^ 32 = (5 : ZMod 3377504499073) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 16 * (5 : ZMod 3377504499073) ^ 16 := by rw [pow_add]
          _ = 211402466025 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 3377504499073) ^ 65 = 3250958145648 := by
        calc
          (5 : ZMod 3377504499073) ^ 65 = (5 : ZMod 3377504499073) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 32 * (5 : ZMod 3377504499073) ^ 32) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 3250958145648 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 3377504499073) ^ 131 = 579954609118 := by
        calc
          (5 : ZMod 3377504499073) ^ 131 = (5 : ZMod 3377504499073) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 65 * (5 : ZMod 3377504499073) ^ 65) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 579954609118 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 3377504499073) ^ 262 = 2276522360606 := by
        calc
          (5 : ZMod 3377504499073) ^ 262 = (5 : ZMod 3377504499073) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 131 * (5 : ZMod 3377504499073) ^ 131 := by rw [pow_add]
          _ = 2276522360606 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 3377504499073) ^ 524 = 1609794110423 := by
        calc
          (5 : ZMod 3377504499073) ^ 524 = (5 : ZMod 3377504499073) ^ (262 + 262) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 262 * (5 : ZMod 3377504499073) ^ 262 := by rw [pow_add]
          _ = 1609794110423 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 3377504499073) ^ 1048 = 3200507168178 := by
        calc
          (5 : ZMod 3377504499073) ^ 1048 = (5 : ZMod 3377504499073) ^ (524 + 524) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 524 * (5 : ZMod 3377504499073) ^ 524 := by rw [pow_add]
          _ = 3200507168178 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 3377504499073) ^ 2097 = 2044044195760 := by
        calc
          (5 : ZMod 3377504499073) ^ 2097 = (5 : ZMod 3377504499073) ^ (1048 + 1048 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1048 * (5 : ZMod 3377504499073) ^ 1048) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2044044195760 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 3377504499073) ^ 4194 = 3242118296394 := by
        calc
          (5 : ZMod 3377504499073) ^ 4194 = (5 : ZMod 3377504499073) ^ (2097 + 2097) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2097 * (5 : ZMod 3377504499073) ^ 2097 := by rw [pow_add]
          _ = 3242118296394 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 3377504499073) ^ 8388 = 1792948847740 := by
        calc
          (5 : ZMod 3377504499073) ^ 8388 = (5 : ZMod 3377504499073) ^ (4194 + 4194) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4194 * (5 : ZMod 3377504499073) ^ 4194 := by rw [pow_add]
          _ = 1792948847740 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 3377504499073) ^ 16776 = 1310695620585 := by
        calc
          (5 : ZMod 3377504499073) ^ 16776 = (5 : ZMod 3377504499073) ^ (8388 + 8388) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 8388 * (5 : ZMod 3377504499073) ^ 8388 := by rw [pow_add]
          _ = 1310695620585 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 3377504499073) ^ 33552 = 2938601971633 := by
        calc
          (5 : ZMod 3377504499073) ^ 33552 = (5 : ZMod 3377504499073) ^ (16776 + 16776) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 16776 * (5 : ZMod 3377504499073) ^ 16776 := by rw [pow_add]
          _ = 2938601971633 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 3377504499073) ^ 67104 = 768898103009 := by
        calc
          (5 : ZMod 3377504499073) ^ 67104 = (5 : ZMod 3377504499073) ^ (33552 + 33552) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 33552 * (5 : ZMod 3377504499073) ^ 33552 := by rw [pow_add]
          _ = 768898103009 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 3377504499073) ^ 134209 = 310450692470 := by
        calc
          (5 : ZMod 3377504499073) ^ 134209 = (5 : ZMod 3377504499073) ^ (67104 + 67104 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 67104 * (5 : ZMod 3377504499073) ^ 67104) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 310450692470 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 3377504499073) ^ 268419 = 2839527343854 := by
        calc
          (5 : ZMod 3377504499073) ^ 268419 = (5 : ZMod 3377504499073) ^ (134209 + 134209 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 134209 * (5 : ZMod 3377504499073) ^ 134209) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2839527343854 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 3377504499073) ^ 536839 = 777354487566 := by
        calc
          (5 : ZMod 3377504499073) ^ 536839 = (5 : ZMod 3377504499073) ^ (268419 + 268419 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 268419 * (5 : ZMod 3377504499073) ^ 268419) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 777354487566 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 3377504499073) ^ 1073679 = 648080812504 := by
        calc
          (5 : ZMod 3377504499073) ^ 1073679 = (5 : ZMod 3377504499073) ^ (536839 + 536839 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 536839 * (5 : ZMod 3377504499073) ^ 536839) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 648080812504 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 3377504499073) ^ 2147359 = 2003826370900 := by
        calc
          (5 : ZMod 3377504499073) ^ 2147359 = (5 : ZMod 3377504499073) ^ (1073679 + 1073679 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1073679 * (5 : ZMod 3377504499073) ^ 1073679) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2003826370900 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 3377504499073) ^ 4294719 = 412639489471 := by
        calc
          (5 : ZMod 3377504499073) ^ 4294719 = (5 : ZMod 3377504499073) ^ (2147359 + 2147359 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 2147359 * (5 : ZMod 3377504499073) ^ 2147359) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 412639489471 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 3377504499073) ^ 8589438 = 2943296045889 := by
        calc
          (5 : ZMod 3377504499073) ^ 8589438 = (5 : ZMod 3377504499073) ^ (4294719 + 4294719) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4294719 * (5 : ZMod 3377504499073) ^ 4294719 := by rw [pow_add]
          _ = 2943296045889 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 3377504499073) ^ 17178876 = 470900636217 := by
        calc
          (5 : ZMod 3377504499073) ^ 17178876 = (5 : ZMod 3377504499073) ^ (8589438 + 8589438) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 8589438 * (5 : ZMod 3377504499073) ^ 8589438 := by rw [pow_add]
          _ = 470900636217 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 3377504499073) ^ 34357752 = 2760811101003 := by
        calc
          (5 : ZMod 3377504499073) ^ 34357752 = (5 : ZMod 3377504499073) ^ (17178876 + 17178876) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 17178876 * (5 : ZMod 3377504499073) ^ 17178876 := by rw [pow_add]
          _ = 2760811101003 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 3377504499073) ^ 68715504 = 740902388524 := by
        calc
          (5 : ZMod 3377504499073) ^ 68715504 = (5 : ZMod 3377504499073) ^ (34357752 + 34357752) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 34357752 * (5 : ZMod 3377504499073) ^ 34357752 := by rw [pow_add]
          _ = 740902388524 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 3377504499073) ^ 137431009 = 1039149628222 := by
        calc
          (5 : ZMod 3377504499073) ^ 137431009 = (5 : ZMod 3377504499073) ^ (68715504 + 68715504 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 68715504 * (5 : ZMod 3377504499073) ^ 68715504) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1039149628222 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 3377504499073) ^ 274862019 = 1076782940816 := by
        calc
          (5 : ZMod 3377504499073) ^ 274862019 = (5 : ZMod 3377504499073) ^ (137431009 + 137431009 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 137431009 * (5 : ZMod 3377504499073) ^ 137431009) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1076782940816 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 3377504499073) ^ 549724039 = 2600565596734 := by
        calc
          (5 : ZMod 3377504499073) ^ 549724039 = (5 : ZMod 3377504499073) ^ (274862019 + 274862019 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 274862019 * (5 : ZMod 3377504499073) ^ 274862019) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2600565596734 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 3377504499073) ^ 1099448079 = 2075406628596 := by
        calc
          (5 : ZMod 3377504499073) ^ 1099448079 = (5 : ZMod 3377504499073) ^ (549724039 + 549724039 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 549724039 * (5 : ZMod 3377504499073) ^ 549724039) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2075406628596 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 3377504499073) ^ 2198896158 = 1556785780729 := by
        calc
          (5 : ZMod 3377504499073) ^ 2198896158 = (5 : ZMod 3377504499073) ^ (1099448079 + 1099448079) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1099448079 * (5 : ZMod 3377504499073) ^ 1099448079 := by rw [pow_add]
          _ = 1556785780729 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 3377504499073) ^ 4397792316 = 48613767355 := by
        calc
          (5 : ZMod 3377504499073) ^ 4397792316 = (5 : ZMod 3377504499073) ^ (2198896158 + 2198896158) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2198896158 * (5 : ZMod 3377504499073) ^ 2198896158 := by rw [pow_add]
          _ = 48613767355 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 3377504499073) ^ 8795584633 = 1658943230515 := by
        calc
          (5 : ZMod 3377504499073) ^ 8795584633 = (5 : ZMod 3377504499073) ^ (4397792316 + 4397792316 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 4397792316 * (5 : ZMod 3377504499073) ^ 4397792316) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1658943230515 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 3377504499073) ^ 17591169266 = 217037365796 := by
        calc
          (5 : ZMod 3377504499073) ^ 17591169266 = (5 : ZMod 3377504499073) ^ (8795584633 + 8795584633) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 8795584633 * (5 : ZMod 3377504499073) ^ 8795584633 := by rw [pow_add]
          _ = 217037365796 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 3377504499073) ^ 35182338532 = 698152461301 := by
        calc
          (5 : ZMod 3377504499073) ^ 35182338532 = (5 : ZMod 3377504499073) ^ (17591169266 + 17591169266) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 17591169266 * (5 : ZMod 3377504499073) ^ 17591169266 := by rw [pow_add]
          _ = 698152461301 := by rw [factor_1_34]; decide
      have factor_1_36 : (5 : ZMod 3377504499073) ^ 70364677064 = 1432164043678 := by
        calc
          (5 : ZMod 3377504499073) ^ 70364677064 = (5 : ZMod 3377504499073) ^ (35182338532 + 35182338532) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 35182338532 * (5 : ZMod 3377504499073) ^ 35182338532 := by rw [pow_add]
          _ = 1432164043678 := by rw [factor_1_35]; decide
      have factor_1_37 : (5 : ZMod 3377504499073) ^ 140729354128 = 679793048638 := by
        calc
          (5 : ZMod 3377504499073) ^ 140729354128 = (5 : ZMod 3377504499073) ^ (70364677064 + 70364677064) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 70364677064 * (5 : ZMod 3377504499073) ^ 70364677064 := by rw [pow_add]
          _ = 679793048638 := by rw [factor_1_36]; decide
      have factor_1_38 : (5 : ZMod 3377504499073) ^ 281458708256 = 1595298069869 := by
        calc
          (5 : ZMod 3377504499073) ^ 281458708256 = (5 : ZMod 3377504499073) ^ (140729354128 + 140729354128) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 140729354128 * (5 : ZMod 3377504499073) ^ 140729354128 := by rw [pow_add]
          _ = 1595298069869 := by rw [factor_1_37]; decide
      have factor_1_39 : (5 : ZMod 3377504499073) ^ 562917416512 = 2481451268684 := by
        calc
          (5 : ZMod 3377504499073) ^ 562917416512 = (5 : ZMod 3377504499073) ^ (281458708256 + 281458708256) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 281458708256 * (5 : ZMod 3377504499073) ^ 281458708256 := by rw [pow_add]
          _ = 2481451268684 := by rw [factor_1_38]; decide
      have factor_1_40 : (5 : ZMod 3377504499073) ^ 1125834833024 = 2481451268683 := by
        calc
          (5 : ZMod 3377504499073) ^ 1125834833024 = (5 : ZMod 3377504499073) ^ (562917416512 + 562917416512) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 562917416512 * (5 : ZMod 3377504499073) ^ 562917416512 := by rw [pow_add]
          _ = 2481451268683 := by rw [factor_1_39]; decide
      change (5 : ZMod 3377504499073) ^ 1125834833024 ≠ 1
      rw [factor_1_40]
      decide
    ·
      have factor_2_0 : (5 : ZMod 3377504499073) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 3377504499073) ^ 2 = 25 := by
        calc
          (5 : ZMod 3377504499073) ^ 2 = (5 : ZMod 3377504499073) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1 * (5 : ZMod 3377504499073) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 3377504499073) ^ 4 = 625 := by
        calc
          (5 : ZMod 3377504499073) ^ 4 = (5 : ZMod 3377504499073) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2 * (5 : ZMod 3377504499073) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 3377504499073) ^ 8 = 390625 := by
        calc
          (5 : ZMod 3377504499073) ^ 8 = (5 : ZMod 3377504499073) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4 * (5 : ZMod 3377504499073) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 3377504499073) ^ 17 = 762939453125 := by
        calc
          (5 : ZMod 3377504499073) ^ 17 = (5 : ZMod 3377504499073) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 8 * (5 : ZMod 3377504499073) ^ 8) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 762939453125 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 3377504499073) ^ 35 = 2782776759614 := by
        calc
          (5 : ZMod 3377504499073) ^ 35 = (5 : ZMod 3377504499073) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 17 * (5 : ZMod 3377504499073) ^ 17) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2782776759614 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 3377504499073) ^ 71 = 1930864191153 := by
        calc
          (5 : ZMod 3377504499073) ^ 71 = (5 : ZMod 3377504499073) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 35 * (5 : ZMod 3377504499073) ^ 35) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1930864191153 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 3377504499073) ^ 142 = 739149613025 := by
        calc
          (5 : ZMod 3377504499073) ^ 142 = (5 : ZMod 3377504499073) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 71 * (5 : ZMod 3377504499073) ^ 71 := by rw [pow_add]
          _ = 739149613025 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 3377504499073) ^ 285 = 113944411633 := by
        calc
          (5 : ZMod 3377504499073) ^ 285 = (5 : ZMod 3377504499073) ^ (142 + 142 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 142 * (5 : ZMod 3377504499073) ^ 142) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 113944411633 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 3377504499073) ^ 571 = 636623357777 := by
        calc
          (5 : ZMod 3377504499073) ^ 571 = (5 : ZMod 3377504499073) ^ (285 + 285 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 285 * (5 : ZMod 3377504499073) ^ 285) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 636623357777 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 3377504499073) ^ 1143 = 3332055283454 := by
        calc
          (5 : ZMod 3377504499073) ^ 1143 = (5 : ZMod 3377504499073) ^ (571 + 571 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 571 * (5 : ZMod 3377504499073) ^ 571) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 3332055283454 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 3377504499073) ^ 2287 = 2673226392833 := by
        calc
          (5 : ZMod 3377504499073) ^ 2287 = (5 : ZMod 3377504499073) ^ (1143 + 1143 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1143 * (5 : ZMod 3377504499073) ^ 1143) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2673226392833 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 3377504499073) ^ 4575 = 40976948207 := by
        calc
          (5 : ZMod 3377504499073) ^ 4575 = (5 : ZMod 3377504499073) ^ (2287 + 2287 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 2287 * (5 : ZMod 3377504499073) ^ 2287) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 40976948207 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 3377504499073) ^ 9150 = 2943938651402 := by
        calc
          (5 : ZMod 3377504499073) ^ 9150 = (5 : ZMod 3377504499073) ^ (4575 + 4575) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4575 * (5 : ZMod 3377504499073) ^ 4575 := by rw [pow_add]
          _ = 2943938651402 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 3377504499073) ^ 18301 = 1133858125854 := by
        calc
          (5 : ZMod 3377504499073) ^ 18301 = (5 : ZMod 3377504499073) ^ (9150 + 9150 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 9150 * (5 : ZMod 3377504499073) ^ 9150) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1133858125854 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 3377504499073) ^ 36602 = 2443982670798 := by
        calc
          (5 : ZMod 3377504499073) ^ 36602 = (5 : ZMod 3377504499073) ^ (18301 + 18301) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 18301 * (5 : ZMod 3377504499073) ^ 18301 := by rw [pow_add]
          _ = 2443982670798 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 3377504499073) ^ 73205 = 2021917671582 := by
        calc
          (5 : ZMod 3377504499073) ^ 73205 = (5 : ZMod 3377504499073) ^ (36602 + 36602 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 36602 * (5 : ZMod 3377504499073) ^ 36602) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2021917671582 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 3377504499073) ^ 146410 = 1235364712516 := by
        calc
          (5 : ZMod 3377504499073) ^ 146410 = (5 : ZMod 3377504499073) ^ (73205 + 73205) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 73205 * (5 : ZMod 3377504499073) ^ 73205 := by rw [pow_add]
          _ = 1235364712516 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 3377504499073) ^ 292821 = 1005631141357 := by
        calc
          (5 : ZMod 3377504499073) ^ 292821 = (5 : ZMod 3377504499073) ^ (146410 + 146410 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 146410 * (5 : ZMod 3377504499073) ^ 146410) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1005631141357 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 3377504499073) ^ 585643 = 2136160835590 := by
        calc
          (5 : ZMod 3377504499073) ^ 585643 = (5 : ZMod 3377504499073) ^ (292821 + 292821 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 292821 * (5 : ZMod 3377504499073) ^ 292821) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2136160835590 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 3377504499073) ^ 1171287 = 1413158836887 := by
        calc
          (5 : ZMod 3377504499073) ^ 1171287 = (5 : ZMod 3377504499073) ^ (585643 + 585643 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 585643 * (5 : ZMod 3377504499073) ^ 585643) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1413158836887 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 3377504499073) ^ 2342574 = 1115350517676 := by
        calc
          (5 : ZMod 3377504499073) ^ 2342574 = (5 : ZMod 3377504499073) ^ (1171287 + 1171287) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1171287 * (5 : ZMod 3377504499073) ^ 1171287 := by rw [pow_add]
          _ = 1115350517676 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 3377504499073) ^ 4685148 = 2039046170384 := by
        calc
          (5 : ZMod 3377504499073) ^ 4685148 = (5 : ZMod 3377504499073) ^ (2342574 + 2342574) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2342574 * (5 : ZMod 3377504499073) ^ 2342574 := by rw [pow_add]
          _ = 2039046170384 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 3377504499073) ^ 9370296 = 2412804852032 := by
        calc
          (5 : ZMod 3377504499073) ^ 9370296 = (5 : ZMod 3377504499073) ^ (4685148 + 4685148) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4685148 * (5 : ZMod 3377504499073) ^ 4685148 := by rw [pow_add]
          _ = 2412804852032 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 3377504499073) ^ 18740592 = 1617170670994 := by
        calc
          (5 : ZMod 3377504499073) ^ 18740592 = (5 : ZMod 3377504499073) ^ (9370296 + 9370296) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 9370296 * (5 : ZMod 3377504499073) ^ 9370296 := by rw [pow_add]
          _ = 1617170670994 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 3377504499073) ^ 37481184 = 3257549382126 := by
        calc
          (5 : ZMod 3377504499073) ^ 37481184 = (5 : ZMod 3377504499073) ^ (18740592 + 18740592) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 18740592 * (5 : ZMod 3377504499073) ^ 18740592 := by rw [pow_add]
          _ = 3257549382126 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 3377504499073) ^ 74962369 = 1743764414092 := by
        calc
          (5 : ZMod 3377504499073) ^ 74962369 = (5 : ZMod 3377504499073) ^ (37481184 + 37481184 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 37481184 * (5 : ZMod 3377504499073) ^ 37481184) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1743764414092 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 3377504499073) ^ 149924738 = 1579624746477 := by
        calc
          (5 : ZMod 3377504499073) ^ 149924738 = (5 : ZMod 3377504499073) ^ (74962369 + 74962369) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 74962369 * (5 : ZMod 3377504499073) ^ 74962369 := by rw [pow_add]
          _ = 1579624746477 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 3377504499073) ^ 299849476 = 3353659920616 := by
        calc
          (5 : ZMod 3377504499073) ^ 299849476 = (5 : ZMod 3377504499073) ^ (149924738 + 149924738) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 149924738 * (5 : ZMod 3377504499073) ^ 149924738 := by rw [pow_add]
          _ = 3353659920616 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 3377504499073) ^ 599698952 = 2264990256977 := by
        calc
          (5 : ZMod 3377504499073) ^ 599698952 = (5 : ZMod 3377504499073) ^ (299849476 + 299849476) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 299849476 * (5 : ZMod 3377504499073) ^ 299849476 := by rw [pow_add]
          _ = 2264990256977 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 3377504499073) ^ 1199397904 = 3373832387143 := by
        calc
          (5 : ZMod 3377504499073) ^ 1199397904 = (5 : ZMod 3377504499073) ^ (599698952 + 599698952) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 599698952 * (5 : ZMod 3377504499073) ^ 599698952 := by rw [pow_add]
          _ = 3373832387143 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 3377504499073) ^ 2398795809 = 1611368476368 := by
        calc
          (5 : ZMod 3377504499073) ^ 2398795809 = (5 : ZMod 3377504499073) ^ (1199397904 + 1199397904 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1199397904 * (5 : ZMod 3377504499073) ^ 1199397904) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1611368476368 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 3377504499073) ^ 4797591618 = 3372478979572 := by
        calc
          (5 : ZMod 3377504499073) ^ 4797591618 = (5 : ZMod 3377504499073) ^ (2398795809 + 2398795809) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2398795809 * (5 : ZMod 3377504499073) ^ 2398795809 := by rw [pow_add]
          _ = 3372478979572 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 3377504499073) ^ 9595183236 = 2452375083529 := by
        calc
          (5 : ZMod 3377504499073) ^ 9595183236 = (5 : ZMod 3377504499073) ^ (4797591618 + 4797591618) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4797591618 * (5 : ZMod 3377504499073) ^ 4797591618 := by rw [pow_add]
          _ = 2452375083529 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 3377504499073) ^ 19190366472 = 1379468486295 := by
        calc
          (5 : ZMod 3377504499073) ^ 19190366472 = (5 : ZMod 3377504499073) ^ (9595183236 + 9595183236) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 9595183236 * (5 : ZMod 3377504499073) ^ 9595183236 := by rw [pow_add]
          _ = 1379468486295 := by rw [factor_2_33]; decide
      have factor_2_35 : (5 : ZMod 3377504499073) ^ 38380732944 = 1921077165722 := by
        calc
          (5 : ZMod 3377504499073) ^ 38380732944 = (5 : ZMod 3377504499073) ^ (19190366472 + 19190366472) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 19190366472 * (5 : ZMod 3377504499073) ^ 19190366472 := by rw [pow_add]
          _ = 1921077165722 := by rw [factor_2_34]; decide
      have factor_2_36 : (5 : ZMod 3377504499073) ^ 76761465888 = 2732769801487 := by
        calc
          (5 : ZMod 3377504499073) ^ 76761465888 = (5 : ZMod 3377504499073) ^ (38380732944 + 38380732944) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 38380732944 * (5 : ZMod 3377504499073) ^ 38380732944 := by rw [pow_add]
          _ = 2732769801487 := by rw [factor_2_35]; decide
      have factor_2_37 : (5 : ZMod 3377504499073) ^ 153522931776 = 1269037239045 := by
        calc
          (5 : ZMod 3377504499073) ^ 153522931776 = (5 : ZMod 3377504499073) ^ (76761465888 + 76761465888) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 76761465888 * (5 : ZMod 3377504499073) ^ 76761465888 := by rw [pow_add]
          _ = 1269037239045 := by rw [factor_2_36]; decide
      have factor_2_38 : (5 : ZMod 3377504499073) ^ 307045863552 = 2574861510252 := by
        calc
          (5 : ZMod 3377504499073) ^ 307045863552 = (5 : ZMod 3377504499073) ^ (153522931776 + 153522931776) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 153522931776 * (5 : ZMod 3377504499073) ^ 153522931776 := by rw [pow_add]
          _ = 2574861510252 := by rw [factor_2_37]; decide
      change (5 : ZMod 3377504499073) ^ 307045863552 ≠ 1
      rw [factor_2_38]
      decide
    ·
      have factor_3_0 : (5 : ZMod 3377504499073) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 3377504499073) ^ 2 = 25 := by
        calc
          (5 : ZMod 3377504499073) ^ 2 = (5 : ZMod 3377504499073) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1 * (5 : ZMod 3377504499073) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 3377504499073) ^ 5 = 3125 := by
        calc
          (5 : ZMod 3377504499073) ^ 5 = (5 : ZMod 3377504499073) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 2 * (5 : ZMod 3377504499073) ^ 2) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 3377504499073) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 3377504499073) ^ 10 = (5 : ZMod 3377504499073) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 5 * (5 : ZMod 3377504499073) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 3377504499073) ^ 20 = 797305666581 := by
        calc
          (5 : ZMod 3377504499073) ^ 20 = (5 : ZMod 3377504499073) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 10 * (5 : ZMod 3377504499073) ^ 10 := by rw [pow_add]
          _ = 797305666581 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 3377504499073) ^ 41 = 2271452402021 := by
        calc
          (5 : ZMod 3377504499073) ^ 41 = (5 : ZMod 3377504499073) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 20 * (5 : ZMod 3377504499073) ^ 20) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2271452402021 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 3377504499073) ^ 82 = 140430080459 := by
        calc
          (5 : ZMod 3377504499073) ^ 82 = (5 : ZMod 3377504499073) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 41 * (5 : ZMod 3377504499073) ^ 41 := by rw [pow_add]
          _ = 140430080459 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 3377504499073) ^ 165 = 1138433725422 := by
        calc
          (5 : ZMod 3377504499073) ^ 165 = (5 : ZMod 3377504499073) ^ (82 + 82 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 82 * (5 : ZMod 3377504499073) ^ 82) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1138433725422 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 3377504499073) ^ 331 = 2591285844627 := by
        calc
          (5 : ZMod 3377504499073) ^ 331 = (5 : ZMod 3377504499073) ^ (165 + 165 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 165 * (5 : ZMod 3377504499073) ^ 165) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2591285844627 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 3377504499073) ^ 662 = 2310371801578 := by
        calc
          (5 : ZMod 3377504499073) ^ 662 = (5 : ZMod 3377504499073) ^ (331 + 331) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 331 * (5 : ZMod 3377504499073) ^ 331 := by rw [pow_add]
          _ = 2310371801578 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 3377504499073) ^ 1324 = 1942434130857 := by
        calc
          (5 : ZMod 3377504499073) ^ 1324 = (5 : ZMod 3377504499073) ^ (662 + 662) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 662 * (5 : ZMod 3377504499073) ^ 662 := by rw [pow_add]
          _ = 1942434130857 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 3377504499073) ^ 2648 = 723085653830 := by
        calc
          (5 : ZMod 3377504499073) ^ 2648 = (5 : ZMod 3377504499073) ^ (1324 + 1324) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1324 * (5 : ZMod 3377504499073) ^ 1324 := by rw [pow_add]
          _ = 723085653830 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 3377504499073) ^ 5297 = 2132970309566 := by
        calc
          (5 : ZMod 3377504499073) ^ 5297 = (5 : ZMod 3377504499073) ^ (2648 + 2648 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 2648 * (5 : ZMod 3377504499073) ^ 2648) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2132970309566 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 3377504499073) ^ 10595 = 3288931489892 := by
        calc
          (5 : ZMod 3377504499073) ^ 10595 = (5 : ZMod 3377504499073) ^ (5297 + 5297 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 5297 * (5 : ZMod 3377504499073) ^ 5297) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 3288931489892 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 3377504499073) ^ 21191 = 92298138356 := by
        calc
          (5 : ZMod 3377504499073) ^ 21191 = (5 : ZMod 3377504499073) ^ (10595 + 10595 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 10595 * (5 : ZMod 3377504499073) ^ 10595) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 92298138356 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 3377504499073) ^ 42382 = 2033996908878 := by
        calc
          (5 : ZMod 3377504499073) ^ 42382 = (5 : ZMod 3377504499073) ^ (21191 + 21191) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 21191 * (5 : ZMod 3377504499073) ^ 21191 := by rw [pow_add]
          _ = 2033996908878 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 3377504499073) ^ 84764 = 1433663936960 := by
        calc
          (5 : ZMod 3377504499073) ^ 84764 = (5 : ZMod 3377504499073) ^ (42382 + 42382) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 42382 * (5 : ZMod 3377504499073) ^ 42382 := by rw [pow_add]
          _ = 1433663936960 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 3377504499073) ^ 169528 = 2402793977092 := by
        calc
          (5 : ZMod 3377504499073) ^ 169528 = (5 : ZMod 3377504499073) ^ (84764 + 84764) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 84764 * (5 : ZMod 3377504499073) ^ 84764 := by rw [pow_add]
          _ = 2402793977092 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 3377504499073) ^ 339056 = 781642703178 := by
        calc
          (5 : ZMod 3377504499073) ^ 339056 = (5 : ZMod 3377504499073) ^ (169528 + 169528) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 169528 * (5 : ZMod 3377504499073) ^ 169528 := by rw [pow_add]
          _ = 781642703178 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 3377504499073) ^ 678113 = 1130099670868 := by
        calc
          (5 : ZMod 3377504499073) ^ 678113 = (5 : ZMod 3377504499073) ^ (339056 + 339056 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 339056 * (5 : ZMod 3377504499073) ^ 339056) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1130099670868 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 3377504499073) ^ 1356227 = 1268401146310 := by
        calc
          (5 : ZMod 3377504499073) ^ 1356227 = (5 : ZMod 3377504499073) ^ (678113 + 678113 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 678113 * (5 : ZMod 3377504499073) ^ 678113) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1268401146310 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 3377504499073) ^ 2712454 = 2700612181672 := by
        calc
          (5 : ZMod 3377504499073) ^ 2712454 = (5 : ZMod 3377504499073) ^ (1356227 + 1356227) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1356227 * (5 : ZMod 3377504499073) ^ 1356227 := by rw [pow_add]
          _ = 2700612181672 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 3377504499073) ^ 5424908 = 1524500233179 := by
        calc
          (5 : ZMod 3377504499073) ^ 5424908 = (5 : ZMod 3377504499073) ^ (2712454 + 2712454) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2712454 * (5 : ZMod 3377504499073) ^ 2712454 := by rw [pow_add]
          _ = 1524500233179 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 3377504499073) ^ 10849816 = 2867880569653 := by
        calc
          (5 : ZMod 3377504499073) ^ 10849816 = (5 : ZMod 3377504499073) ^ (5424908 + 5424908) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 5424908 * (5 : ZMod 3377504499073) ^ 5424908 := by rw [pow_add]
          _ = 2867880569653 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 3377504499073) ^ 21699633 = 2109428060037 := by
        calc
          (5 : ZMod 3377504499073) ^ 21699633 = (5 : ZMod 3377504499073) ^ (10849816 + 10849816 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 10849816 * (5 : ZMod 3377504499073) ^ 10849816) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2109428060037 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 3377504499073) ^ 43399266 = 365747961134 := by
        calc
          (5 : ZMod 3377504499073) ^ 43399266 = (5 : ZMod 3377504499073) ^ (21699633 + 21699633) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 21699633 * (5 : ZMod 3377504499073) ^ 21699633 := by rw [pow_add]
          _ = 365747961134 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 3377504499073) ^ 86798532 = 1518248590788 := by
        calc
          (5 : ZMod 3377504499073) ^ 86798532 = (5 : ZMod 3377504499073) ^ (43399266 + 43399266) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 43399266 * (5 : ZMod 3377504499073) ^ 43399266 := by rw [pow_add]
          _ = 1518248590788 := by rw [factor_3_25]; decide
      have factor_3_27 : (5 : ZMod 3377504499073) ^ 173597065 = 130933353363 := by
        calc
          (5 : ZMod 3377504499073) ^ 173597065 = (5 : ZMod 3377504499073) ^ (86798532 + 86798532 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 86798532 * (5 : ZMod 3377504499073) ^ 86798532) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 130933353363 := by rw [factor_3_26]; decide
      have factor_3_28 : (5 : ZMod 3377504499073) ^ 347194130 = 2145418069910 := by
        calc
          (5 : ZMod 3377504499073) ^ 347194130 = (5 : ZMod 3377504499073) ^ (173597065 + 173597065) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 173597065 * (5 : ZMod 3377504499073) ^ 173597065 := by rw [pow_add]
          _ = 2145418069910 := by rw [factor_3_27]; decide
      have factor_3_29 : (5 : ZMod 3377504499073) ^ 694388260 = 855471694477 := by
        calc
          (5 : ZMod 3377504499073) ^ 694388260 = (5 : ZMod 3377504499073) ^ (347194130 + 347194130) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 347194130 * (5 : ZMod 3377504499073) ^ 347194130 := by rw [pow_add]
          _ = 855471694477 := by rw [factor_3_28]; decide
      have factor_3_30 : (5 : ZMod 3377504499073) ^ 1388776521 = 1700037876779 := by
        calc
          (5 : ZMod 3377504499073) ^ 1388776521 = (5 : ZMod 3377504499073) ^ (694388260 + 694388260 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 694388260 * (5 : ZMod 3377504499073) ^ 694388260) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1700037876779 := by rw [factor_3_29]; decide
      have factor_3_31 : (5 : ZMod 3377504499073) ^ 2777553042 = 860157612827 := by
        calc
          (5 : ZMod 3377504499073) ^ 2777553042 = (5 : ZMod 3377504499073) ^ (1388776521 + 1388776521) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1388776521 * (5 : ZMod 3377504499073) ^ 1388776521 := by rw [pow_add]
          _ = 860157612827 := by rw [factor_3_30]; decide
      have factor_3_32 : (5 : ZMod 3377504499073) ^ 5555106084 = 2161904543070 := by
        calc
          (5 : ZMod 3377504499073) ^ 5555106084 = (5 : ZMod 3377504499073) ^ (2777553042 + 2777553042) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2777553042 * (5 : ZMod 3377504499073) ^ 2777553042 := by rw [pow_add]
          _ = 2161904543070 := by rw [factor_3_31]; decide
      have factor_3_33 : (5 : ZMod 3377504499073) ^ 11110212168 = 1872574331504 := by
        calc
          (5 : ZMod 3377504499073) ^ 11110212168 = (5 : ZMod 3377504499073) ^ (5555106084 + 5555106084) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 5555106084 * (5 : ZMod 3377504499073) ^ 5555106084 := by rw [pow_add]
          _ = 1872574331504 := by rw [factor_3_32]; decide
      have factor_3_34 : (5 : ZMod 3377504499073) ^ 22220424336 = 3167742242456 := by
        calc
          (5 : ZMod 3377504499073) ^ 22220424336 = (5 : ZMod 3377504499073) ^ (11110212168 + 11110212168) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 11110212168 * (5 : ZMod 3377504499073) ^ 11110212168 := by rw [pow_add]
          _ = 3167742242456 := by rw [factor_3_33]; decide
      have factor_3_35 : (5 : ZMod 3377504499073) ^ 44440848672 = 56436132001 := by
        calc
          (5 : ZMod 3377504499073) ^ 44440848672 = (5 : ZMod 3377504499073) ^ (22220424336 + 22220424336) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 22220424336 * (5 : ZMod 3377504499073) ^ 22220424336 := by rw [pow_add]
          _ = 56436132001 := by rw [factor_3_34]; decide
      have factor_3_36 : (5 : ZMod 3377504499073) ^ 88881697344 = 2096520055907 := by
        calc
          (5 : ZMod 3377504499073) ^ 88881697344 = (5 : ZMod 3377504499073) ^ (44440848672 + 44440848672) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 44440848672 * (5 : ZMod 3377504499073) ^ 44440848672 := by rw [pow_add]
          _ = 2096520055907 := by rw [factor_3_35]; decide
      have factor_3_37 : (5 : ZMod 3377504499073) ^ 177763394688 = 2629069028735 := by
        calc
          (5 : ZMod 3377504499073) ^ 177763394688 = (5 : ZMod 3377504499073) ^ (88881697344 + 88881697344) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 88881697344 * (5 : ZMod 3377504499073) ^ 88881697344 := by rw [pow_add]
          _ = 2629069028735 := by rw [factor_3_36]; decide
      change (5 : ZMod 3377504499073) ^ 177763394688 ≠ 1
      rw [factor_3_37]
      decide
    ·
      have factor_4_0 : (5 : ZMod 3377504499073) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 3377504499073) ^ 3 = 125 := by
        calc
          (5 : ZMod 3377504499073) ^ 3 = (5 : ZMod 3377504499073) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1 * (5 : ZMod 3377504499073) ^ 1) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 3377504499073) ^ 7 = 78125 := by
        calc
          (5 : ZMod 3377504499073) ^ 7 = (5 : ZMod 3377504499073) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 3 * (5 : ZMod 3377504499073) ^ 3) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 78125 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 3377504499073) ^ 14 = 6103515625 := by
        calc
          (5 : ZMod 3377504499073) ^ 14 = (5 : ZMod 3377504499073) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 7 * (5 : ZMod 3377504499073) ^ 7 := by rw [pow_add]
          _ = 6103515625 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 3377504499073) ^ 28 = 1081139683649 := by
        calc
          (5 : ZMod 3377504499073) ^ 28 = (5 : ZMod 3377504499073) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 14 * (5 : ZMod 3377504499073) ^ 14 := by rw [pow_add]
          _ = 1081139683649 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 3377504499073) ^ 57 = 1706368989045 := by
        calc
          (5 : ZMod 3377504499073) ^ 57 = (5 : ZMod 3377504499073) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 28 * (5 : ZMod 3377504499073) ^ 28) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1706368989045 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 3377504499073) ^ 115 = 1503218763552 := by
        calc
          (5 : ZMod 3377504499073) ^ 115 = (5 : ZMod 3377504499073) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 57 * (5 : ZMod 3377504499073) ^ 57) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1503218763552 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 3377504499073) ^ 230 = 1273437122042 := by
        calc
          (5 : ZMod 3377504499073) ^ 230 = (5 : ZMod 3377504499073) ^ (115 + 115) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 115 * (5 : ZMod 3377504499073) ^ 115 := by rw [pow_add]
          _ = 1273437122042 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 3377504499073) ^ 461 = 1947518816127 := by
        calc
          (5 : ZMod 3377504499073) ^ 461 = (5 : ZMod 3377504499073) ^ (230 + 230 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 230 * (5 : ZMod 3377504499073) ^ 230) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1947518816127 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 3377504499073) ^ 923 = 272087644908 := by
        calc
          (5 : ZMod 3377504499073) ^ 923 = (5 : ZMod 3377504499073) ^ (461 + 461 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 461 * (5 : ZMod 3377504499073) ^ 461) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 272087644908 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 3377504499073) ^ 1846 = 5491723654 := by
        calc
          (5 : ZMod 3377504499073) ^ 1846 = (5 : ZMod 3377504499073) ^ (923 + 923) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 923 * (5 : ZMod 3377504499073) ^ 923 := by rw [pow_add]
          _ = 5491723654 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 3377504499073) ^ 3693 = 687303745077 := by
        calc
          (5 : ZMod 3377504499073) ^ 3693 = (5 : ZMod 3377504499073) ^ (1846 + 1846 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1846 * (5 : ZMod 3377504499073) ^ 1846) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 687303745077 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 3377504499073) ^ 7387 = 1117253720570 := by
        calc
          (5 : ZMod 3377504499073) ^ 7387 = (5 : ZMod 3377504499073) ^ (3693 + 3693 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 3693 * (5 : ZMod 3377504499073) ^ 3693) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1117253720570 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 3377504499073) ^ 14775 = 1648314249632 := by
        calc
          (5 : ZMod 3377504499073) ^ 14775 = (5 : ZMod 3377504499073) ^ (7387 + 7387 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 7387 * (5 : ZMod 3377504499073) ^ 7387) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1648314249632 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 3377504499073) ^ 29550 = 1793415510718 := by
        calc
          (5 : ZMod 3377504499073) ^ 29550 = (5 : ZMod 3377504499073) ^ (14775 + 14775) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 14775 * (5 : ZMod 3377504499073) ^ 14775 := by rw [pow_add]
          _ = 1793415510718 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 3377504499073) ^ 59101 = 1771788995504 := by
        calc
          (5 : ZMod 3377504499073) ^ 59101 = (5 : ZMod 3377504499073) ^ (29550 + 29550 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 29550 * (5 : ZMod 3377504499073) ^ 29550) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1771788995504 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 3377504499073) ^ 118203 = 1405674530038 := by
        calc
          (5 : ZMod 3377504499073) ^ 118203 = (5 : ZMod 3377504499073) ^ (59101 + 59101 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 59101 * (5 : ZMod 3377504499073) ^ 59101) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1405674530038 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 3377504499073) ^ 236406 = 2264250837306 := by
        calc
          (5 : ZMod 3377504499073) ^ 236406 = (5 : ZMod 3377504499073) ^ (118203 + 118203) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 118203 * (5 : ZMod 3377504499073) ^ 118203 := by rw [pow_add]
          _ = 2264250837306 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 3377504499073) ^ 472813 = 1543433218368 := by
        calc
          (5 : ZMod 3377504499073) ^ 472813 = (5 : ZMod 3377504499073) ^ (236406 + 236406 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 236406 * (5 : ZMod 3377504499073) ^ 236406) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1543433218368 := by rw [factor_4_17]; decide
      have factor_4_19 : (5 : ZMod 3377504499073) ^ 945626 = 1584297804660 := by
        calc
          (5 : ZMod 3377504499073) ^ 945626 = (5 : ZMod 3377504499073) ^ (472813 + 472813) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 472813 * (5 : ZMod 3377504499073) ^ 472813 := by rw [pow_add]
          _ = 1584297804660 := by rw [factor_4_18]; decide
      have factor_4_20 : (5 : ZMod 3377504499073) ^ 1891252 = 3264010895776 := by
        calc
          (5 : ZMod 3377504499073) ^ 1891252 = (5 : ZMod 3377504499073) ^ (945626 + 945626) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 945626 * (5 : ZMod 3377504499073) ^ 945626 := by rw [pow_add]
          _ = 3264010895776 := by rw [factor_4_19]; decide
      have factor_4_21 : (5 : ZMod 3377504499073) ^ 3782504 = 2490015661985 := by
        calc
          (5 : ZMod 3377504499073) ^ 3782504 = (5 : ZMod 3377504499073) ^ (1891252 + 1891252) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1891252 * (5 : ZMod 3377504499073) ^ 1891252 := by rw [pow_add]
          _ = 2490015661985 := by rw [factor_4_20]; decide
      have factor_4_22 : (5 : ZMod 3377504499073) ^ 7565009 = 1698285001192 := by
        calc
          (5 : ZMod 3377504499073) ^ 7565009 = (5 : ZMod 3377504499073) ^ (3782504 + 3782504 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 3782504 * (5 : ZMod 3377504499073) ^ 3782504) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1698285001192 := by rw [factor_4_21]; decide
      have factor_4_23 : (5 : ZMod 3377504499073) ^ 15130019 = 2756896192280 := by
        calc
          (5 : ZMod 3377504499073) ^ 15130019 = (5 : ZMod 3377504499073) ^ (7565009 + 7565009 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 7565009 * (5 : ZMod 3377504499073) ^ 7565009) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2756896192280 := by rw [factor_4_22]; decide
      have factor_4_24 : (5 : ZMod 3377504499073) ^ 30260038 = 1138671787004 := by
        calc
          (5 : ZMod 3377504499073) ^ 30260038 = (5 : ZMod 3377504499073) ^ (15130019 + 15130019) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 15130019 * (5 : ZMod 3377504499073) ^ 15130019 := by rw [pow_add]
          _ = 1138671787004 := by rw [factor_4_23]; decide
      have factor_4_25 : (5 : ZMod 3377504499073) ^ 60520077 = 3253029998369 := by
        calc
          (5 : ZMod 3377504499073) ^ 60520077 = (5 : ZMod 3377504499073) ^ (30260038 + 30260038 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 30260038 * (5 : ZMod 3377504499073) ^ 30260038) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 3253029998369 := by rw [factor_4_24]; decide
      have factor_4_26 : (5 : ZMod 3377504499073) ^ 121040155 = 3078945777277 := by
        calc
          (5 : ZMod 3377504499073) ^ 121040155 = (5 : ZMod 3377504499073) ^ (60520077 + 60520077 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 60520077 * (5 : ZMod 3377504499073) ^ 60520077) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 3078945777277 := by rw [factor_4_25]; decide
      have factor_4_27 : (5 : ZMod 3377504499073) ^ 242080311 = 509780108558 := by
        calc
          (5 : ZMod 3377504499073) ^ 242080311 = (5 : ZMod 3377504499073) ^ (121040155 + 121040155 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 121040155 * (5 : ZMod 3377504499073) ^ 121040155) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 509780108558 := by rw [factor_4_26]; decide
      have factor_4_28 : (5 : ZMod 3377504499073) ^ 484160622 = 324090970682 := by
        calc
          (5 : ZMod 3377504499073) ^ 484160622 = (5 : ZMod 3377504499073) ^ (242080311 + 242080311) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 242080311 * (5 : ZMod 3377504499073) ^ 242080311 := by rw [pow_add]
          _ = 324090970682 := by rw [factor_4_27]; decide
      have factor_4_29 : (5 : ZMod 3377504499073) ^ 968321244 = 1489847985091 := by
        calc
          (5 : ZMod 3377504499073) ^ 968321244 = (5 : ZMod 3377504499073) ^ (484160622 + 484160622) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 484160622 * (5 : ZMod 3377504499073) ^ 484160622 := by rw [pow_add]
          _ = 1489847985091 := by rw [factor_4_28]; decide
      have factor_4_30 : (5 : ZMod 3377504499073) ^ 1936642488 = 573457077598 := by
        calc
          (5 : ZMod 3377504499073) ^ 1936642488 = (5 : ZMod 3377504499073) ^ (968321244 + 968321244) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 968321244 * (5 : ZMod 3377504499073) ^ 968321244 := by rw [pow_add]
          _ = 573457077598 := by rw [factor_4_29]; decide
      have factor_4_31 : (5 : ZMod 3377504499073) ^ 3873284976 = 97286648653 := by
        calc
          (5 : ZMod 3377504499073) ^ 3873284976 = (5 : ZMod 3377504499073) ^ (1936642488 + 1936642488) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1936642488 * (5 : ZMod 3377504499073) ^ 1936642488 := by rw [pow_add]
          _ = 97286648653 := by rw [factor_4_30]; decide
      have factor_4_32 : (5 : ZMod 3377504499073) ^ 7746569952 = 390855927820 := by
        calc
          (5 : ZMod 3377504499073) ^ 7746569952 = (5 : ZMod 3377504499073) ^ (3873284976 + 3873284976) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 3873284976 * (5 : ZMod 3377504499073) ^ 3873284976 := by rw [pow_add]
          _ = 390855927820 := by rw [factor_4_31]; decide
      have factor_4_33 : (5 : ZMod 3377504499073) ^ 15493139904 = 1919839046529 := by
        calc
          (5 : ZMod 3377504499073) ^ 15493139904 = (5 : ZMod 3377504499073) ^ (7746569952 + 7746569952) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 7746569952 * (5 : ZMod 3377504499073) ^ 7746569952 := by rw [pow_add]
          _ = 1919839046529 := by rw [factor_4_32]; decide
      have factor_4_34 : (5 : ZMod 3377504499073) ^ 30986279808 = 3265742879984 := by
        calc
          (5 : ZMod 3377504499073) ^ 30986279808 = (5 : ZMod 3377504499073) ^ (15493139904 + 15493139904) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 15493139904 * (5 : ZMod 3377504499073) ^ 15493139904 := by rw [pow_add]
          _ = 3265742879984 := by rw [factor_4_33]; decide
      change (5 : ZMod 3377504499073) ^ 30986279808 ≠ 1
      rw [factor_4_34]
      decide
    ·
      have factor_5_0 : (5 : ZMod 3377504499073) ^ 1 = 5 := by norm_num
      have factor_5_1 : (5 : ZMod 3377504499073) ^ 2 = 25 := by
        calc
          (5 : ZMod 3377504499073) ^ 2 = (5 : ZMod 3377504499073) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1 * (5 : ZMod 3377504499073) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_5_0]; decide
      have factor_5_2 : (5 : ZMod 3377504499073) ^ 4 = 625 := by
        calc
          (5 : ZMod 3377504499073) ^ 4 = (5 : ZMod 3377504499073) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2 * (5 : ZMod 3377504499073) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_5_1]; decide
      have factor_5_3 : (5 : ZMod 3377504499073) ^ 8 = 390625 := by
        calc
          (5 : ZMod 3377504499073) ^ 8 = (5 : ZMod 3377504499073) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4 * (5 : ZMod 3377504499073) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_5_2]; decide
      have factor_5_4 : (5 : ZMod 3377504499073) ^ 16 = 152587890625 := by
        calc
          (5 : ZMod 3377504499073) ^ 16 = (5 : ZMod 3377504499073) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 8 * (5 : ZMod 3377504499073) ^ 8 := by rw [pow_add]
          _ = 152587890625 := by rw [factor_5_3]; decide
      have factor_5_5 : (5 : ZMod 3377504499073) ^ 33 = 1057012330125 := by
        calc
          (5 : ZMod 3377504499073) ^ 33 = (5 : ZMod 3377504499073) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 16 * (5 : ZMod 3377504499073) ^ 16) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1057012330125 := by rw [factor_5_4]; decide
      have factor_5_6 : (5 : ZMod 3377504499073) ^ 66 = 2744772731948 := by
        calc
          (5 : ZMod 3377504499073) ^ 66 = (5 : ZMod 3377504499073) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 33 * (5 : ZMod 3377504499073) ^ 33 := by rw [pow_add]
          _ = 2744772731948 := by rw [factor_5_5]; decide
      have factor_5_7 : (5 : ZMod 3377504499073) ^ 133 = 988847231658 := by
        calc
          (5 : ZMod 3377504499073) ^ 133 = (5 : ZMod 3377504499073) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 66 * (5 : ZMod 3377504499073) ^ 66) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 988847231658 := by rw [factor_5_6]; decide
      have factor_5_8 : (5 : ZMod 3377504499073) ^ 266 = 897081269017 := by
        calc
          (5 : ZMod 3377504499073) ^ 266 = (5 : ZMod 3377504499073) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 133 * (5 : ZMod 3377504499073) ^ 133 := by rw [pow_add]
          _ = 897081269017 := by rw [factor_5_7]; decide
      have factor_5_9 : (5 : ZMod 3377504499073) ^ 533 = 51219368956 := by
        calc
          (5 : ZMod 3377504499073) ^ 533 = (5 : ZMod 3377504499073) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 266 * (5 : ZMod 3377504499073) ^ 266) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 51219368956 := by rw [factor_5_8]; decide
      have factor_5_10 : (5 : ZMod 3377504499073) ^ 1067 = 3104111853587 := by
        calc
          (5 : ZMod 3377504499073) ^ 1067 = (5 : ZMod 3377504499073) ^ (533 + 533 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 533 * (5 : ZMod 3377504499073) ^ 533) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 3104111853587 := by rw [factor_5_9]; decide
      have factor_5_11 : (5 : ZMod 3377504499073) ^ 2135 = 2259141644779 := by
        calc
          (5 : ZMod 3377504499073) ^ 2135 = (5 : ZMod 3377504499073) ^ (1067 + 1067 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 1067 * (5 : ZMod 3377504499073) ^ 1067) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 2259141644779 := by rw [factor_5_10]; decide
      have factor_5_12 : (5 : ZMod 3377504499073) ^ 4271 = 210053422705 := by
        calc
          (5 : ZMod 3377504499073) ^ 4271 = (5 : ZMod 3377504499073) ^ (2135 + 2135 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 2135 * (5 : ZMod 3377504499073) ^ 2135) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 210053422705 := by rw [factor_5_11]; decide
      have factor_5_13 : (5 : ZMod 3377504499073) ^ 8542 = 3026141146598 := by
        calc
          (5 : ZMod 3377504499073) ^ 8542 = (5 : ZMod 3377504499073) ^ (4271 + 4271) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4271 * (5 : ZMod 3377504499073) ^ 4271 := by rw [pow_add]
          _ = 3026141146598 := by rw [factor_5_12]; decide
      have factor_5_14 : (5 : ZMod 3377504499073) ^ 17085 = 1126039559943 := by
        calc
          (5 : ZMod 3377504499073) ^ 17085 = (5 : ZMod 3377504499073) ^ (8542 + 8542 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 8542 * (5 : ZMod 3377504499073) ^ 8542) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1126039559943 := by rw [factor_5_13]; decide
      have factor_5_15 : (5 : ZMod 3377504499073) ^ 34171 = 1909758034986 := by
        calc
          (5 : ZMod 3377504499073) ^ 34171 = (5 : ZMod 3377504499073) ^ (17085 + 17085 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 17085 * (5 : ZMod 3377504499073) ^ 17085) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1909758034986 := by rw [factor_5_14]; decide
      have factor_5_16 : (5 : ZMod 3377504499073) ^ 68343 = 1231967908766 := by
        calc
          (5 : ZMod 3377504499073) ^ 68343 = (5 : ZMod 3377504499073) ^ (34171 + 34171 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = ((5 : ZMod 3377504499073) ^ 34171 * (5 : ZMod 3377504499073) ^ 34171) * (5 : ZMod 3377504499073) := by rw [pow_succ, pow_add]
          _ = 1231967908766 := by rw [factor_5_15]; decide
      have factor_5_17 : (5 : ZMod 3377504499073) ^ 136686 = 1420758591813 := by
        calc
          (5 : ZMod 3377504499073) ^ 136686 = (5 : ZMod 3377504499073) ^ (68343 + 68343) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 68343 * (5 : ZMod 3377504499073) ^ 68343 := by rw [pow_add]
          _ = 1420758591813 := by rw [factor_5_16]; decide
      have factor_5_18 : (5 : ZMod 3377504499073) ^ 273372 = 2106310205376 := by
        calc
          (5 : ZMod 3377504499073) ^ 273372 = (5 : ZMod 3377504499073) ^ (136686 + 136686) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 136686 * (5 : ZMod 3377504499073) ^ 136686 := by rw [pow_add]
          _ = 2106310205376 := by rw [factor_5_17]; decide
      have factor_5_19 : (5 : ZMod 3377504499073) ^ 546744 = 2975977967551 := by
        calc
          (5 : ZMod 3377504499073) ^ 546744 = (5 : ZMod 3377504499073) ^ (273372 + 273372) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 273372 * (5 : ZMod 3377504499073) ^ 273372 := by rw [pow_add]
          _ = 2975977967551 := by rw [factor_5_18]; decide
      have factor_5_20 : (5 : ZMod 3377504499073) ^ 1093488 = 2153288526310 := by
        calc
          (5 : ZMod 3377504499073) ^ 1093488 = (5 : ZMod 3377504499073) ^ (546744 + 546744) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 546744 * (5 : ZMod 3377504499073) ^ 546744 := by rw [pow_add]
          _ = 2153288526310 := by rw [factor_5_19]; decide
      have factor_5_21 : (5 : ZMod 3377504499073) ^ 2186976 = 341516406179 := by
        calc
          (5 : ZMod 3377504499073) ^ 2186976 = (5 : ZMod 3377504499073) ^ (1093488 + 1093488) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 1093488 * (5 : ZMod 3377504499073) ^ 1093488 := by rw [pow_add]
          _ = 341516406179 := by rw [factor_5_20]; decide
      have factor_5_22 : (5 : ZMod 3377504499073) ^ 4373952 = 1774796430024 := by
        calc
          (5 : ZMod 3377504499073) ^ 4373952 = (5 : ZMod 3377504499073) ^ (2186976 + 2186976) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 2186976 * (5 : ZMod 3377504499073) ^ 2186976 := by rw [pow_add]
          _ = 1774796430024 := by rw [factor_5_21]; decide
      have factor_5_23 : (5 : ZMod 3377504499073) ^ 8747904 = 2922550613969 := by
        calc
          (5 : ZMod 3377504499073) ^ 8747904 = (5 : ZMod 3377504499073) ^ (4373952 + 4373952) :=
            congrArg (fun n : ℕ => (5 : ZMod 3377504499073) ^ n) (by norm_num)
          _ = (5 : ZMod 3377504499073) ^ 4373952 * (5 : ZMod 3377504499073) ^ 4373952 := by rw [pow_add]
          _ = 2922550613969 := by rw [factor_5_22]; decide
      change (5 : ZMod 3377504499073) ^ 8747904 ≠ 1
      rw [factor_5_23]
      decide

#print axioms prime_lucas_3377504499073

end TotientTailPeriodKiller
end Erdos249257
