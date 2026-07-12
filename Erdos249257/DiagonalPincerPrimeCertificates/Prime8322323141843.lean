import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime70528162219

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_8322323141843 : Nat.Prime 8322323141843 := by
  apply lucas_primality 8322323141843 (2 : ZMod 8322323141843)
  ·
      have fermat_0 : (2 : ZMod 8322323141843) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 8322323141843) ^ 3 = 8 := by
        calc
          (2 : ZMod 8322323141843) ^ 3 = (2 : ZMod 8322323141843) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1 * (2 : ZMod 8322323141843) ^ 1) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 8322323141843) ^ 7 = 128 := by
        calc
          (2 : ZMod 8322323141843) ^ 7 = (2 : ZMod 8322323141843) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 3 * (2 : ZMod 8322323141843) ^ 3) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 8322323141843) ^ 15 = 32768 := by
        calc
          (2 : ZMod 8322323141843) ^ 15 = (2 : ZMod 8322323141843) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 7 * (2 : ZMod 8322323141843) ^ 7) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 8322323141843) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 8322323141843) ^ 30 = (2 : ZMod 8322323141843) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 15 * (2 : ZMod 8322323141843) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 8322323141843) ^ 60 = 5112797910657 := by
        calc
          (2 : ZMod 8322323141843) ^ 60 = (2 : ZMod 8322323141843) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 30 * (2 : ZMod 8322323141843) ^ 30 := by rw [pow_add]
          _ = 5112797910657 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 8322323141843) ^ 121 = 2282948671105 := by
        calc
          (2 : ZMod 8322323141843) ^ 121 = (2 : ZMod 8322323141843) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 60 * (2 : ZMod 8322323141843) ^ 60) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 2282948671105 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 8322323141843) ^ 242 = 4739434709462 := by
        calc
          (2 : ZMod 8322323141843) ^ 242 = (2 : ZMod 8322323141843) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 121 * (2 : ZMod 8322323141843) ^ 121 := by rw [pow_add]
          _ = 4739434709462 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 8322323141843) ^ 484 = 195577795761 := by
        calc
          (2 : ZMod 8322323141843) ^ 484 = (2 : ZMod 8322323141843) ^ (242 + 242) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 242 * (2 : ZMod 8322323141843) ^ 242 := by rw [pow_add]
          _ = 195577795761 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 8322323141843) ^ 968 = 7624178328143 := by
        calc
          (2 : ZMod 8322323141843) ^ 968 = (2 : ZMod 8322323141843) ^ (484 + 484) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 484 * (2 : ZMod 8322323141843) ^ 484 := by rw [pow_add]
          _ = 7624178328143 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 8322323141843) ^ 1937 = 6305894586011 := by
        calc
          (2 : ZMod 8322323141843) ^ 1937 = (2 : ZMod 8322323141843) ^ (968 + 968 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 968 * (2 : ZMod 8322323141843) ^ 968) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 6305894586011 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 8322323141843) ^ 3875 = 849148880393 := by
        calc
          (2 : ZMod 8322323141843) ^ 3875 = (2 : ZMod 8322323141843) ^ (1937 + 1937 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1937 * (2 : ZMod 8322323141843) ^ 1937) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 849148880393 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 8322323141843) ^ 7750 = 244921511618 := by
        calc
          (2 : ZMod 8322323141843) ^ 7750 = (2 : ZMod 8322323141843) ^ (3875 + 3875) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 3875 * (2 : ZMod 8322323141843) ^ 3875 := by rw [pow_add]
          _ = 244921511618 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 8322323141843) ^ 15501 = 3786838275226 := by
        calc
          (2 : ZMod 8322323141843) ^ 15501 = (2 : ZMod 8322323141843) ^ (7750 + 7750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 7750 * (2 : ZMod 8322323141843) ^ 7750) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3786838275226 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 8322323141843) ^ 31003 = 5459142544377 := by
        calc
          (2 : ZMod 8322323141843) ^ 31003 = (2 : ZMod 8322323141843) ^ (15501 + 15501 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 15501 * (2 : ZMod 8322323141843) ^ 15501) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 5459142544377 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 8322323141843) ^ 62006 = 4894208172933 := by
        calc
          (2 : ZMod 8322323141843) ^ 62006 = (2 : ZMod 8322323141843) ^ (31003 + 31003) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 31003 * (2 : ZMod 8322323141843) ^ 31003 := by rw [pow_add]
          _ = 4894208172933 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 8322323141843) ^ 124012 = 5794385884656 := by
        calc
          (2 : ZMod 8322323141843) ^ 124012 = (2 : ZMod 8322323141843) ^ (62006 + 62006) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 62006 * (2 : ZMod 8322323141843) ^ 62006 := by rw [pow_add]
          _ = 5794385884656 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 8322323141843) ^ 248024 = 7581397593861 := by
        calc
          (2 : ZMod 8322323141843) ^ 248024 = (2 : ZMod 8322323141843) ^ (124012 + 124012) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 124012 * (2 : ZMod 8322323141843) ^ 124012 := by rw [pow_add]
          _ = 7581397593861 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 8322323141843) ^ 496049 = 3253405157295 := by
        calc
          (2 : ZMod 8322323141843) ^ 496049 = (2 : ZMod 8322323141843) ^ (248024 + 248024 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 248024 * (2 : ZMod 8322323141843) ^ 248024) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3253405157295 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 8322323141843) ^ 992098 = 2609969674279 := by
        calc
          (2 : ZMod 8322323141843) ^ 992098 = (2 : ZMod 8322323141843) ^ (496049 + 496049) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 496049 * (2 : ZMod 8322323141843) ^ 496049 := by rw [pow_add]
          _ = 2609969674279 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 8322323141843) ^ 1984196 = 7278139764531 := by
        calc
          (2 : ZMod 8322323141843) ^ 1984196 = (2 : ZMod 8322323141843) ^ (992098 + 992098) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 992098 * (2 : ZMod 8322323141843) ^ 992098 := by rw [pow_add]
          _ = 7278139764531 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 8322323141843) ^ 3968392 = 1536242807618 := by
        calc
          (2 : ZMod 8322323141843) ^ 3968392 = (2 : ZMod 8322323141843) ^ (1984196 + 1984196) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 1984196 * (2 : ZMod 8322323141843) ^ 1984196 := by rw [pow_add]
          _ = 1536242807618 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 8322323141843) ^ 7936785 = 1858912801962 := by
        calc
          (2 : ZMod 8322323141843) ^ 7936785 = (2 : ZMod 8322323141843) ^ (3968392 + 3968392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 3968392 * (2 : ZMod 8322323141843) ^ 3968392) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 1858912801962 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 8322323141843) ^ 15873571 = 460558354238 := by
        calc
          (2 : ZMod 8322323141843) ^ 15873571 = (2 : ZMod 8322323141843) ^ (7936785 + 7936785 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 7936785 * (2 : ZMod 8322323141843) ^ 7936785) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 460558354238 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 8322323141843) ^ 31747143 = 745360391146 := by
        calc
          (2 : ZMod 8322323141843) ^ 31747143 = (2 : ZMod 8322323141843) ^ (15873571 + 15873571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 15873571 * (2 : ZMod 8322323141843) ^ 15873571) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 745360391146 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 8322323141843) ^ 63494286 = 7770528047284 := by
        calc
          (2 : ZMod 8322323141843) ^ 63494286 = (2 : ZMod 8322323141843) ^ (31747143 + 31747143) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 31747143 * (2 : ZMod 8322323141843) ^ 31747143 := by rw [pow_add]
          _ = 7770528047284 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 8322323141843) ^ 126988573 = 2953521677747 := by
        calc
          (2 : ZMod 8322323141843) ^ 126988573 = (2 : ZMod 8322323141843) ^ (63494286 + 63494286 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 63494286 * (2 : ZMod 8322323141843) ^ 63494286) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 2953521677747 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 8322323141843) ^ 253977146 = 2485138776061 := by
        calc
          (2 : ZMod 8322323141843) ^ 253977146 = (2 : ZMod 8322323141843) ^ (126988573 + 126988573) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 126988573 * (2 : ZMod 8322323141843) ^ 126988573 := by rw [pow_add]
          _ = 2485138776061 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 8322323141843) ^ 507954293 = 3715973191135 := by
        calc
          (2 : ZMod 8322323141843) ^ 507954293 = (2 : ZMod 8322323141843) ^ (253977146 + 253977146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 253977146 * (2 : ZMod 8322323141843) ^ 253977146) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3715973191135 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 8322323141843) ^ 1015908586 = 2082193624243 := by
        calc
          (2 : ZMod 8322323141843) ^ 1015908586 = (2 : ZMod 8322323141843) ^ (507954293 + 507954293) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 507954293 * (2 : ZMod 8322323141843) ^ 507954293 := by rw [pow_add]
          _ = 2082193624243 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 8322323141843) ^ 2031817173 = 2500143542264 := by
        calc
          (2 : ZMod 8322323141843) ^ 2031817173 = (2 : ZMod 8322323141843) ^ (1015908586 + 1015908586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1015908586 * (2 : ZMod 8322323141843) ^ 1015908586) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 2500143542264 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 8322323141843) ^ 4063634346 = 2951767142044 := by
        calc
          (2 : ZMod 8322323141843) ^ 4063634346 = (2 : ZMod 8322323141843) ^ (2031817173 + 2031817173) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 2031817173 * (2 : ZMod 8322323141843) ^ 2031817173 := by rw [pow_add]
          _ = 2951767142044 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 8322323141843) ^ 8127268693 = 3875050317002 := by
        calc
          (2 : ZMod 8322323141843) ^ 8127268693 = (2 : ZMod 8322323141843) ^ (4063634346 + 4063634346 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 4063634346 * (2 : ZMod 8322323141843) ^ 4063634346) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3875050317002 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 8322323141843) ^ 16254537386 = 7300596777783 := by
        calc
          (2 : ZMod 8322323141843) ^ 16254537386 = (2 : ZMod 8322323141843) ^ (8127268693 + 8127268693) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 8127268693 * (2 : ZMod 8322323141843) ^ 8127268693 := by rw [pow_add]
          _ = 7300596777783 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 8322323141843) ^ 32509074772 = 1084899017598 := by
        calc
          (2 : ZMod 8322323141843) ^ 32509074772 = (2 : ZMod 8322323141843) ^ (16254537386 + 16254537386) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 16254537386 * (2 : ZMod 8322323141843) ^ 16254537386 := by rw [pow_add]
          _ = 1084899017598 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 8322323141843) ^ 65018149545 = 7687991657179 := by
        calc
          (2 : ZMod 8322323141843) ^ 65018149545 = (2 : ZMod 8322323141843) ^ (32509074772 + 32509074772 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 32509074772 * (2 : ZMod 8322323141843) ^ 32509074772) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 7687991657179 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 8322323141843) ^ 130036299091 = 474090819729 := by
        calc
          (2 : ZMod 8322323141843) ^ 130036299091 = (2 : ZMod 8322323141843) ^ (65018149545 + 65018149545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 65018149545 * (2 : ZMod 8322323141843) ^ 65018149545) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 474090819729 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 8322323141843) ^ 260072598182 = 5250366204414 := by
        calc
          (2 : ZMod 8322323141843) ^ 260072598182 = (2 : ZMod 8322323141843) ^ (130036299091 + 130036299091) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 130036299091 * (2 : ZMod 8322323141843) ^ 130036299091 := by rw [pow_add]
          _ = 5250366204414 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 8322323141843) ^ 520145196365 = 4875143961812 := by
        calc
          (2 : ZMod 8322323141843) ^ 520145196365 = (2 : ZMod 8322323141843) ^ (260072598182 + 260072598182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 260072598182 * (2 : ZMod 8322323141843) ^ 260072598182) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 4875143961812 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 8322323141843) ^ 1040290392730 = 2690579545625 := by
        calc
          (2 : ZMod 8322323141843) ^ 1040290392730 = (2 : ZMod 8322323141843) ^ (520145196365 + 520145196365) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 520145196365 * (2 : ZMod 8322323141843) ^ 520145196365 := by rw [pow_add]
          _ = 2690579545625 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 8322323141843) ^ 2080580785460 = 7136894251369 := by
        calc
          (2 : ZMod 8322323141843) ^ 2080580785460 = (2 : ZMod 8322323141843) ^ (1040290392730 + 1040290392730) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 1040290392730 * (2 : ZMod 8322323141843) ^ 1040290392730 := by rw [pow_add]
          _ = 7136894251369 := by rw [fermat_39]; decide
      have fermat_41 : (2 : ZMod 8322323141843) ^ 4161161570921 = 8322323141842 := by
        calc
          (2 : ZMod 8322323141843) ^ 4161161570921 = (2 : ZMod 8322323141843) ^ (2080580785460 + 2080580785460 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 2080580785460 * (2 : ZMod 8322323141843) ^ 2080580785460) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 8322323141842 := by rw [fermat_40]; decide
      have fermat_42 : (2 : ZMod 8322323141843) ^ 8322323141842 = 1 := by
        calc
          (2 : ZMod 8322323141843) ^ 8322323141842 = (2 : ZMod 8322323141843) ^ (4161161570921 + 4161161570921) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 4161161570921 * (2 : ZMod 8322323141843) ^ 4161161570921 := by rw [pow_add]
          _ = 1 := by rw [fermat_41]; decide
      simpa using fermat_42
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59, 1), (70528162219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59, 1), (70528162219, 1)] : List FactorBlock).map factorBlockValue).prod = 8322323141843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_70528162219) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 8322323141843) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 8322323141843) ^ 3 = 8 := by
        calc
          (2 : ZMod 8322323141843) ^ 3 = (2 : ZMod 8322323141843) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1 * (2 : ZMod 8322323141843) ^ 1) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 8322323141843) ^ 7 = 128 := by
        calc
          (2 : ZMod 8322323141843) ^ 7 = (2 : ZMod 8322323141843) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 3 * (2 : ZMod 8322323141843) ^ 3) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 8322323141843) ^ 15 = 32768 := by
        calc
          (2 : ZMod 8322323141843) ^ 15 = (2 : ZMod 8322323141843) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 7 * (2 : ZMod 8322323141843) ^ 7) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 8322323141843) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 8322323141843) ^ 30 = (2 : ZMod 8322323141843) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 15 * (2 : ZMod 8322323141843) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 8322323141843) ^ 60 = 5112797910657 := by
        calc
          (2 : ZMod 8322323141843) ^ 60 = (2 : ZMod 8322323141843) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 30 * (2 : ZMod 8322323141843) ^ 30 := by rw [pow_add]
          _ = 5112797910657 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 8322323141843) ^ 121 = 2282948671105 := by
        calc
          (2 : ZMod 8322323141843) ^ 121 = (2 : ZMod 8322323141843) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 60 * (2 : ZMod 8322323141843) ^ 60) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 2282948671105 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 8322323141843) ^ 242 = 4739434709462 := by
        calc
          (2 : ZMod 8322323141843) ^ 242 = (2 : ZMod 8322323141843) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 121 * (2 : ZMod 8322323141843) ^ 121 := by rw [pow_add]
          _ = 4739434709462 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 8322323141843) ^ 484 = 195577795761 := by
        calc
          (2 : ZMod 8322323141843) ^ 484 = (2 : ZMod 8322323141843) ^ (242 + 242) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 242 * (2 : ZMod 8322323141843) ^ 242 := by rw [pow_add]
          _ = 195577795761 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 8322323141843) ^ 968 = 7624178328143 := by
        calc
          (2 : ZMod 8322323141843) ^ 968 = (2 : ZMod 8322323141843) ^ (484 + 484) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 484 * (2 : ZMod 8322323141843) ^ 484 := by rw [pow_add]
          _ = 7624178328143 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 8322323141843) ^ 1937 = 6305894586011 := by
        calc
          (2 : ZMod 8322323141843) ^ 1937 = (2 : ZMod 8322323141843) ^ (968 + 968 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 968 * (2 : ZMod 8322323141843) ^ 968) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 6305894586011 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 8322323141843) ^ 3875 = 849148880393 := by
        calc
          (2 : ZMod 8322323141843) ^ 3875 = (2 : ZMod 8322323141843) ^ (1937 + 1937 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1937 * (2 : ZMod 8322323141843) ^ 1937) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 849148880393 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 8322323141843) ^ 7750 = 244921511618 := by
        calc
          (2 : ZMod 8322323141843) ^ 7750 = (2 : ZMod 8322323141843) ^ (3875 + 3875) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 3875 * (2 : ZMod 8322323141843) ^ 3875 := by rw [pow_add]
          _ = 244921511618 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 8322323141843) ^ 15501 = 3786838275226 := by
        calc
          (2 : ZMod 8322323141843) ^ 15501 = (2 : ZMod 8322323141843) ^ (7750 + 7750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 7750 * (2 : ZMod 8322323141843) ^ 7750) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3786838275226 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 8322323141843) ^ 31003 = 5459142544377 := by
        calc
          (2 : ZMod 8322323141843) ^ 31003 = (2 : ZMod 8322323141843) ^ (15501 + 15501 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 15501 * (2 : ZMod 8322323141843) ^ 15501) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 5459142544377 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 8322323141843) ^ 62006 = 4894208172933 := by
        calc
          (2 : ZMod 8322323141843) ^ 62006 = (2 : ZMod 8322323141843) ^ (31003 + 31003) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 31003 * (2 : ZMod 8322323141843) ^ 31003 := by rw [pow_add]
          _ = 4894208172933 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 8322323141843) ^ 124012 = 5794385884656 := by
        calc
          (2 : ZMod 8322323141843) ^ 124012 = (2 : ZMod 8322323141843) ^ (62006 + 62006) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 62006 * (2 : ZMod 8322323141843) ^ 62006 := by rw [pow_add]
          _ = 5794385884656 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 8322323141843) ^ 248024 = 7581397593861 := by
        calc
          (2 : ZMod 8322323141843) ^ 248024 = (2 : ZMod 8322323141843) ^ (124012 + 124012) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 124012 * (2 : ZMod 8322323141843) ^ 124012 := by rw [pow_add]
          _ = 7581397593861 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 8322323141843) ^ 496049 = 3253405157295 := by
        calc
          (2 : ZMod 8322323141843) ^ 496049 = (2 : ZMod 8322323141843) ^ (248024 + 248024 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 248024 * (2 : ZMod 8322323141843) ^ 248024) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3253405157295 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 8322323141843) ^ 992098 = 2609969674279 := by
        calc
          (2 : ZMod 8322323141843) ^ 992098 = (2 : ZMod 8322323141843) ^ (496049 + 496049) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 496049 * (2 : ZMod 8322323141843) ^ 496049 := by rw [pow_add]
          _ = 2609969674279 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 8322323141843) ^ 1984196 = 7278139764531 := by
        calc
          (2 : ZMod 8322323141843) ^ 1984196 = (2 : ZMod 8322323141843) ^ (992098 + 992098) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 992098 * (2 : ZMod 8322323141843) ^ 992098 := by rw [pow_add]
          _ = 7278139764531 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 8322323141843) ^ 3968392 = 1536242807618 := by
        calc
          (2 : ZMod 8322323141843) ^ 3968392 = (2 : ZMod 8322323141843) ^ (1984196 + 1984196) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 1984196 * (2 : ZMod 8322323141843) ^ 1984196 := by rw [pow_add]
          _ = 1536242807618 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 8322323141843) ^ 7936785 = 1858912801962 := by
        calc
          (2 : ZMod 8322323141843) ^ 7936785 = (2 : ZMod 8322323141843) ^ (3968392 + 3968392 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 3968392 * (2 : ZMod 8322323141843) ^ 3968392) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 1858912801962 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 8322323141843) ^ 15873571 = 460558354238 := by
        calc
          (2 : ZMod 8322323141843) ^ 15873571 = (2 : ZMod 8322323141843) ^ (7936785 + 7936785 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 7936785 * (2 : ZMod 8322323141843) ^ 7936785) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 460558354238 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 8322323141843) ^ 31747143 = 745360391146 := by
        calc
          (2 : ZMod 8322323141843) ^ 31747143 = (2 : ZMod 8322323141843) ^ (15873571 + 15873571 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 15873571 * (2 : ZMod 8322323141843) ^ 15873571) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 745360391146 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 8322323141843) ^ 63494286 = 7770528047284 := by
        calc
          (2 : ZMod 8322323141843) ^ 63494286 = (2 : ZMod 8322323141843) ^ (31747143 + 31747143) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 31747143 * (2 : ZMod 8322323141843) ^ 31747143 := by rw [pow_add]
          _ = 7770528047284 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 8322323141843) ^ 126988573 = 2953521677747 := by
        calc
          (2 : ZMod 8322323141843) ^ 126988573 = (2 : ZMod 8322323141843) ^ (63494286 + 63494286 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 63494286 * (2 : ZMod 8322323141843) ^ 63494286) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 2953521677747 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 8322323141843) ^ 253977146 = 2485138776061 := by
        calc
          (2 : ZMod 8322323141843) ^ 253977146 = (2 : ZMod 8322323141843) ^ (126988573 + 126988573) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 126988573 * (2 : ZMod 8322323141843) ^ 126988573 := by rw [pow_add]
          _ = 2485138776061 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 8322323141843) ^ 507954293 = 3715973191135 := by
        calc
          (2 : ZMod 8322323141843) ^ 507954293 = (2 : ZMod 8322323141843) ^ (253977146 + 253977146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 253977146 * (2 : ZMod 8322323141843) ^ 253977146) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3715973191135 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 8322323141843) ^ 1015908586 = 2082193624243 := by
        calc
          (2 : ZMod 8322323141843) ^ 1015908586 = (2 : ZMod 8322323141843) ^ (507954293 + 507954293) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 507954293 * (2 : ZMod 8322323141843) ^ 507954293 := by rw [pow_add]
          _ = 2082193624243 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 8322323141843) ^ 2031817173 = 2500143542264 := by
        calc
          (2 : ZMod 8322323141843) ^ 2031817173 = (2 : ZMod 8322323141843) ^ (1015908586 + 1015908586 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1015908586 * (2 : ZMod 8322323141843) ^ 1015908586) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 2500143542264 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 8322323141843) ^ 4063634346 = 2951767142044 := by
        calc
          (2 : ZMod 8322323141843) ^ 4063634346 = (2 : ZMod 8322323141843) ^ (2031817173 + 2031817173) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 2031817173 * (2 : ZMod 8322323141843) ^ 2031817173 := by rw [pow_add]
          _ = 2951767142044 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 8322323141843) ^ 8127268693 = 3875050317002 := by
        calc
          (2 : ZMod 8322323141843) ^ 8127268693 = (2 : ZMod 8322323141843) ^ (4063634346 + 4063634346 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 4063634346 * (2 : ZMod 8322323141843) ^ 4063634346) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3875050317002 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 8322323141843) ^ 16254537386 = 7300596777783 := by
        calc
          (2 : ZMod 8322323141843) ^ 16254537386 = (2 : ZMod 8322323141843) ^ (8127268693 + 8127268693) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 8127268693 * (2 : ZMod 8322323141843) ^ 8127268693 := by rw [pow_add]
          _ = 7300596777783 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 8322323141843) ^ 32509074772 = 1084899017598 := by
        calc
          (2 : ZMod 8322323141843) ^ 32509074772 = (2 : ZMod 8322323141843) ^ (16254537386 + 16254537386) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 16254537386 * (2 : ZMod 8322323141843) ^ 16254537386 := by rw [pow_add]
          _ = 1084899017598 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 8322323141843) ^ 65018149545 = 7687991657179 := by
        calc
          (2 : ZMod 8322323141843) ^ 65018149545 = (2 : ZMod 8322323141843) ^ (32509074772 + 32509074772 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 32509074772 * (2 : ZMod 8322323141843) ^ 32509074772) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 7687991657179 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 8322323141843) ^ 130036299091 = 474090819729 := by
        calc
          (2 : ZMod 8322323141843) ^ 130036299091 = (2 : ZMod 8322323141843) ^ (65018149545 + 65018149545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 65018149545 * (2 : ZMod 8322323141843) ^ 65018149545) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 474090819729 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 8322323141843) ^ 260072598182 = 5250366204414 := by
        calc
          (2 : ZMod 8322323141843) ^ 260072598182 = (2 : ZMod 8322323141843) ^ (130036299091 + 130036299091) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 130036299091 * (2 : ZMod 8322323141843) ^ 130036299091 := by rw [pow_add]
          _ = 5250366204414 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 8322323141843) ^ 520145196365 = 4875143961812 := by
        calc
          (2 : ZMod 8322323141843) ^ 520145196365 = (2 : ZMod 8322323141843) ^ (260072598182 + 260072598182 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 260072598182 * (2 : ZMod 8322323141843) ^ 260072598182) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 4875143961812 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 8322323141843) ^ 1040290392730 = 2690579545625 := by
        calc
          (2 : ZMod 8322323141843) ^ 1040290392730 = (2 : ZMod 8322323141843) ^ (520145196365 + 520145196365) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 520145196365 * (2 : ZMod 8322323141843) ^ 520145196365 := by rw [pow_add]
          _ = 2690579545625 := by rw [factor_0_38]; decide
      have factor_0_40 : (2 : ZMod 8322323141843) ^ 2080580785460 = 7136894251369 := by
        calc
          (2 : ZMod 8322323141843) ^ 2080580785460 = (2 : ZMod 8322323141843) ^ (1040290392730 + 1040290392730) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 1040290392730 * (2 : ZMod 8322323141843) ^ 1040290392730 := by rw [pow_add]
          _ = 7136894251369 := by rw [factor_0_39]; decide
      have factor_0_41 : (2 : ZMod 8322323141843) ^ 4161161570921 = 8322323141842 := by
        calc
          (2 : ZMod 8322323141843) ^ 4161161570921 = (2 : ZMod 8322323141843) ^ (2080580785460 + 2080580785460 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 2080580785460 * (2 : ZMod 8322323141843) ^ 2080580785460) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 8322323141842 := by rw [factor_0_40]; decide
      change (2 : ZMod 8322323141843) ^ 4161161570921 ≠ 1
      rw [factor_0_41]
      decide
    ·
      have factor_1_0 : (2 : ZMod 8322323141843) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 8322323141843) ^ 2 = 4 := by
        calc
          (2 : ZMod 8322323141843) ^ 2 = (2 : ZMod 8322323141843) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 1 * (2 : ZMod 8322323141843) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 8322323141843) ^ 4 = 16 := by
        calc
          (2 : ZMod 8322323141843) ^ 4 = (2 : ZMod 8322323141843) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 2 * (2 : ZMod 8322323141843) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 8322323141843) ^ 8 = 256 := by
        calc
          (2 : ZMod 8322323141843) ^ 8 = (2 : ZMod 8322323141843) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 4 * (2 : ZMod 8322323141843) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 8322323141843) ^ 16 = 65536 := by
        calc
          (2 : ZMod 8322323141843) ^ 16 = (2 : ZMod 8322323141843) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 8 * (2 : ZMod 8322323141843) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 8322323141843) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 8322323141843) ^ 32 = (2 : ZMod 8322323141843) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 16 * (2 : ZMod 8322323141843) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 8322323141843) ^ 65 = 5485393446007 := by
        calc
          (2 : ZMod 8322323141843) ^ 65 = (2 : ZMod 8322323141843) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 32 * (2 : ZMod 8322323141843) ^ 32) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 5485393446007 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 8322323141843) ^ 131 = 7488959495480 := by
        calc
          (2 : ZMod 8322323141843) ^ 131 = (2 : ZMod 8322323141843) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 65 * (2 : ZMod 8322323141843) ^ 65) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 7488959495480 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 8322323141843) ^ 262 = 7192726704191 := by
        calc
          (2 : ZMod 8322323141843) ^ 262 = (2 : ZMod 8322323141843) ^ (131 + 131) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 131 * (2 : ZMod 8322323141843) ^ 131 := by rw [pow_add]
          _ = 7192726704191 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 8322323141843) ^ 525 = 7563463494364 := by
        calc
          (2 : ZMod 8322323141843) ^ 525 = (2 : ZMod 8322323141843) ^ (262 + 262 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 262 * (2 : ZMod 8322323141843) ^ 262) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 7563463494364 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 8322323141843) ^ 1050 = 262253631750 := by
        calc
          (2 : ZMod 8322323141843) ^ 1050 = (2 : ZMod 8322323141843) ^ (525 + 525) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 525 * (2 : ZMod 8322323141843) ^ 525 := by rw [pow_add]
          _ = 262253631750 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 8322323141843) ^ 2101 = 4154926255750 := by
        calc
          (2 : ZMod 8322323141843) ^ 2101 = (2 : ZMod 8322323141843) ^ (1050 + 1050 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1050 * (2 : ZMod 8322323141843) ^ 1050) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 4154926255750 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 8322323141843) ^ 4203 = 3388284060440 := by
        calc
          (2 : ZMod 8322323141843) ^ 4203 = (2 : ZMod 8322323141843) ^ (2101 + 2101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 2101 * (2 : ZMod 8322323141843) ^ 2101) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3388284060440 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 8322323141843) ^ 8407 = 6023461162791 := by
        calc
          (2 : ZMod 8322323141843) ^ 8407 = (2 : ZMod 8322323141843) ^ (4203 + 4203 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 4203 * (2 : ZMod 8322323141843) ^ 4203) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 6023461162791 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 8322323141843) ^ 16815 = 7384254025660 := by
        calc
          (2 : ZMod 8322323141843) ^ 16815 = (2 : ZMod 8322323141843) ^ (8407 + 8407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 8407 * (2 : ZMod 8322323141843) ^ 8407) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 7384254025660 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 8322323141843) ^ 33630 = 6411900561781 := by
        calc
          (2 : ZMod 8322323141843) ^ 33630 = (2 : ZMod 8322323141843) ^ (16815 + 16815) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 16815 * (2 : ZMod 8322323141843) ^ 16815 := by rw [pow_add]
          _ = 6411900561781 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 8322323141843) ^ 67260 = 1335276216636 := by
        calc
          (2 : ZMod 8322323141843) ^ 67260 = (2 : ZMod 8322323141843) ^ (33630 + 33630) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 33630 * (2 : ZMod 8322323141843) ^ 33630 := by rw [pow_add]
          _ = 1335276216636 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 8322323141843) ^ 134521 = 5772756653783 := by
        calc
          (2 : ZMod 8322323141843) ^ 134521 = (2 : ZMod 8322323141843) ^ (67260 + 67260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 67260 * (2 : ZMod 8322323141843) ^ 67260) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 5772756653783 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 8322323141843) ^ 269043 = 1851426661647 := by
        calc
          (2 : ZMod 8322323141843) ^ 269043 = (2 : ZMod 8322323141843) ^ (134521 + 134521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 134521 * (2 : ZMod 8322323141843) ^ 134521) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 1851426661647 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 8322323141843) ^ 538087 = 7556448128457 := by
        calc
          (2 : ZMod 8322323141843) ^ 538087 = (2 : ZMod 8322323141843) ^ (269043 + 269043 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 269043 * (2 : ZMod 8322323141843) ^ 269043) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 7556448128457 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 8322323141843) ^ 1076174 = 2076804125014 := by
        calc
          (2 : ZMod 8322323141843) ^ 1076174 = (2 : ZMod 8322323141843) ^ (538087 + 538087) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 538087 * (2 : ZMod 8322323141843) ^ 538087 := by rw [pow_add]
          _ = 2076804125014 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 8322323141843) ^ 2152348 = 7309224687841 := by
        calc
          (2 : ZMod 8322323141843) ^ 2152348 = (2 : ZMod 8322323141843) ^ (1076174 + 1076174) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 1076174 * (2 : ZMod 8322323141843) ^ 1076174 := by rw [pow_add]
          _ = 7309224687841 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 8322323141843) ^ 4304697 = 5440849254943 := by
        calc
          (2 : ZMod 8322323141843) ^ 4304697 = (2 : ZMod 8322323141843) ^ (2152348 + 2152348 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 2152348 * (2 : ZMod 8322323141843) ^ 2152348) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 5440849254943 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 8322323141843) ^ 8609394 = 17280436039 := by
        calc
          (2 : ZMod 8322323141843) ^ 8609394 = (2 : ZMod 8322323141843) ^ (4304697 + 4304697) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 4304697 * (2 : ZMod 8322323141843) ^ 4304697 := by rw [pow_add]
          _ = 17280436039 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 8322323141843) ^ 17218789 = 3264138128264 := by
        calc
          (2 : ZMod 8322323141843) ^ 17218789 = (2 : ZMod 8322323141843) ^ (8609394 + 8609394 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 8609394 * (2 : ZMod 8322323141843) ^ 8609394) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3264138128264 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 8322323141843) ^ 34437579 = 3304544019564 := by
        calc
          (2 : ZMod 8322323141843) ^ 34437579 = (2 : ZMod 8322323141843) ^ (17218789 + 17218789 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 17218789 * (2 : ZMod 8322323141843) ^ 17218789) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 3304544019564 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 8322323141843) ^ 68875158 = 2475015091134 := by
        calc
          (2 : ZMod 8322323141843) ^ 68875158 = (2 : ZMod 8322323141843) ^ (34437579 + 34437579) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 34437579 * (2 : ZMod 8322323141843) ^ 34437579 := by rw [pow_add]
          _ = 2475015091134 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 8322323141843) ^ 137750316 = 875666192232 := by
        calc
          (2 : ZMod 8322323141843) ^ 137750316 = (2 : ZMod 8322323141843) ^ (68875158 + 68875158) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 68875158 * (2 : ZMod 8322323141843) ^ 68875158 := by rw [pow_add]
          _ = 875666192232 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 8322323141843) ^ 275500633 = 6288000603967 := by
        calc
          (2 : ZMod 8322323141843) ^ 275500633 = (2 : ZMod 8322323141843) ^ (137750316 + 137750316 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 137750316 * (2 : ZMod 8322323141843) ^ 137750316) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 6288000603967 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 8322323141843) ^ 551001267 = 6490710703512 := by
        calc
          (2 : ZMod 8322323141843) ^ 551001267 = (2 : ZMod 8322323141843) ^ (275500633 + 275500633 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 275500633 * (2 : ZMod 8322323141843) ^ 275500633) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 6490710703512 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 8322323141843) ^ 1102002534 = 533039984646 := by
        calc
          (2 : ZMod 8322323141843) ^ 1102002534 = (2 : ZMod 8322323141843) ^ (551001267 + 551001267) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 551001267 * (2 : ZMod 8322323141843) ^ 551001267 := by rw [pow_add]
          _ = 533039984646 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 8322323141843) ^ 2204005069 = 516329429354 := by
        calc
          (2 : ZMod 8322323141843) ^ 2204005069 = (2 : ZMod 8322323141843) ^ (1102002534 + 1102002534 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1102002534 * (2 : ZMod 8322323141843) ^ 1102002534) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 516329429354 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 8322323141843) ^ 4408010138 = 2321715629785 := by
        calc
          (2 : ZMod 8322323141843) ^ 4408010138 = (2 : ZMod 8322323141843) ^ (2204005069 + 2204005069) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 2204005069 * (2 : ZMod 8322323141843) ^ 2204005069 := by rw [pow_add]
          _ = 2321715629785 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 8322323141843) ^ 8816020277 = 1931252545632 := by
        calc
          (2 : ZMod 8322323141843) ^ 8816020277 = (2 : ZMod 8322323141843) ^ (4408010138 + 4408010138 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 4408010138 * (2 : ZMod 8322323141843) ^ 4408010138) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 1931252545632 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 8322323141843) ^ 17632040554 = 2373032221019 := by
        calc
          (2 : ZMod 8322323141843) ^ 17632040554 = (2 : ZMod 8322323141843) ^ (8816020277 + 8816020277) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 8816020277 * (2 : ZMod 8322323141843) ^ 8816020277 := by rw [pow_add]
          _ = 2373032221019 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 8322323141843) ^ 35264081109 = 4483861834492 := by
        calc
          (2 : ZMod 8322323141843) ^ 35264081109 = (2 : ZMod 8322323141843) ^ (17632040554 + 17632040554 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 17632040554 * (2 : ZMod 8322323141843) ^ 17632040554) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 4483861834492 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 8322323141843) ^ 70528162219 = 39402308049 := by
        calc
          (2 : ZMod 8322323141843) ^ 70528162219 = (2 : ZMod 8322323141843) ^ (35264081109 + 35264081109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 35264081109 * (2 : ZMod 8322323141843) ^ 35264081109) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 39402308049 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 8322323141843) ^ 141056324438 = 5670442630058 := by
        calc
          (2 : ZMod 8322323141843) ^ 141056324438 = (2 : ZMod 8322323141843) ^ (70528162219 + 70528162219) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 70528162219 * (2 : ZMod 8322323141843) ^ 70528162219 := by rw [pow_add]
          _ = 5670442630058 := by rw [factor_1_36]; decide
      change (2 : ZMod 8322323141843) ^ 141056324438 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (2 : ZMod 8322323141843) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 8322323141843) ^ 3 = 8 := by
        calc
          (2 : ZMod 8322323141843) ^ 3 = (2 : ZMod 8322323141843) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 1 * (2 : ZMod 8322323141843) ^ 1) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 8322323141843) ^ 7 = 128 := by
        calc
          (2 : ZMod 8322323141843) ^ 7 = (2 : ZMod 8322323141843) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 3 * (2 : ZMod 8322323141843) ^ 3) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 8322323141843) ^ 14 = 16384 := by
        calc
          (2 : ZMod 8322323141843) ^ 14 = (2 : ZMod 8322323141843) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 7 * (2 : ZMod 8322323141843) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 8322323141843) ^ 29 = 536870912 := by
        calc
          (2 : ZMod 8322323141843) ^ 29 = (2 : ZMod 8322323141843) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 14 * (2 : ZMod 8322323141843) ^ 14) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 536870912 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 8322323141843) ^ 59 = 6717560526250 := by
        calc
          (2 : ZMod 8322323141843) ^ 59 = (2 : ZMod 8322323141843) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = ((2 : ZMod 8322323141843) ^ 29 * (2 : ZMod 8322323141843) ^ 29) * (2 : ZMod 8322323141843) := by rw [pow_succ, pow_add]
          _ = 6717560526250 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 8322323141843) ^ 118 = 5486820547540 := by
        calc
          (2 : ZMod 8322323141843) ^ 118 = (2 : ZMod 8322323141843) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (2 : ZMod 8322323141843) ^ n) (by norm_num)
          _ = (2 : ZMod 8322323141843) ^ 59 * (2 : ZMod 8322323141843) ^ 59 := by rw [pow_add]
          _ = 5486820547540 := by rw [factor_2_5]; decide
      change (2 : ZMod 8322323141843) ^ 118 ≠ 1
      rw [factor_2_6]
      decide

#print axioms prime_lucas_8322323141843

end TotientTailPeriodKiller
end Erdos249257
