import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime18317784469

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_219813413629 : Nat.Prime 219813413629 := by
  apply lucas_primality 219813413629 (2 : ZMod 219813413629)
  ·
      have fermat_0 : (2 : ZMod 219813413629) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 219813413629) ^ 3 = 8 := by
        calc
          (2 : ZMod 219813413629) ^ 3 = (2 : ZMod 219813413629) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1 * (2 : ZMod 219813413629) ^ 1) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 219813413629) ^ 6 = 64 := by
        calc
          (2 : ZMod 219813413629) ^ 6 = (2 : ZMod 219813413629) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 3 * (2 : ZMod 219813413629) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 219813413629) ^ 12 = 4096 := by
        calc
          (2 : ZMod 219813413629) ^ 12 = (2 : ZMod 219813413629) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 6 * (2 : ZMod 219813413629) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 219813413629) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 219813413629) ^ 25 = (2 : ZMod 219813413629) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 12 * (2 : ZMod 219813413629) ^ 12) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 219813413629) ^ 51 = 31204469772 := by
        calc
          (2 : ZMod 219813413629) ^ 51 = (2 : ZMod 219813413629) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 25 * (2 : ZMod 219813413629) ^ 25) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 31204469772 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 219813413629) ^ 102 = 43042570278 := by
        calc
          (2 : ZMod 219813413629) ^ 102 = (2 : ZMod 219813413629) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 51 * (2 : ZMod 219813413629) ^ 51 := by rw [pow_add]
          _ = 43042570278 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 219813413629) ^ 204 = 178878636979 := by
        calc
          (2 : ZMod 219813413629) ^ 204 = (2 : ZMod 219813413629) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 102 * (2 : ZMod 219813413629) ^ 102 := by rw [pow_add]
          _ = 178878636979 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 219813413629) ^ 409 = 48956129319 := by
        calc
          (2 : ZMod 219813413629) ^ 409 = (2 : ZMod 219813413629) ^ (204 + 204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 204 * (2 : ZMod 219813413629) ^ 204) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 48956129319 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 219813413629) ^ 818 = 119022367876 := by
        calc
          (2 : ZMod 219813413629) ^ 818 = (2 : ZMod 219813413629) ^ (409 + 409) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 409 * (2 : ZMod 219813413629) ^ 409 := by rw [pow_add]
          _ = 119022367876 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 219813413629) ^ 1637 = 59848713938 := by
        calc
          (2 : ZMod 219813413629) ^ 1637 = (2 : ZMod 219813413629) ^ (818 + 818 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 818 * (2 : ZMod 219813413629) ^ 818) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 59848713938 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 219813413629) ^ 3275 = 149436764938 := by
        calc
          (2 : ZMod 219813413629) ^ 3275 = (2 : ZMod 219813413629) ^ (1637 + 1637 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1637 * (2 : ZMod 219813413629) ^ 1637) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 149436764938 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 219813413629) ^ 6550 = 183224934130 := by
        calc
          (2 : ZMod 219813413629) ^ 6550 = (2 : ZMod 219813413629) ^ (3275 + 3275) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 3275 * (2 : ZMod 219813413629) ^ 3275 := by rw [pow_add]
          _ = 183224934130 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 219813413629) ^ 13101 = 156001378890 := by
        calc
          (2 : ZMod 219813413629) ^ 13101 = (2 : ZMod 219813413629) ^ (6550 + 6550 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 6550 * (2 : ZMod 219813413629) ^ 6550) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 156001378890 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 219813413629) ^ 26203 = 118343187014 := by
        calc
          (2 : ZMod 219813413629) ^ 26203 = (2 : ZMod 219813413629) ^ (13101 + 13101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 13101 * (2 : ZMod 219813413629) ^ 13101) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 118343187014 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 219813413629) ^ 52407 = 65329392702 := by
        calc
          (2 : ZMod 219813413629) ^ 52407 = (2 : ZMod 219813413629) ^ (26203 + 26203 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 26203 * (2 : ZMod 219813413629) ^ 26203) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 65329392702 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 219813413629) ^ 104815 = 197834104640 := by
        calc
          (2 : ZMod 219813413629) ^ 104815 = (2 : ZMod 219813413629) ^ (52407 + 52407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 52407 * (2 : ZMod 219813413629) ^ 52407) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 197834104640 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 219813413629) ^ 209630 = 66193651401 := by
        calc
          (2 : ZMod 219813413629) ^ 209630 = (2 : ZMod 219813413629) ^ (104815 + 104815) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 104815 * (2 : ZMod 219813413629) ^ 104815 := by rw [pow_add]
          _ = 66193651401 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 219813413629) ^ 419260 = 207098784159 := by
        calc
          (2 : ZMod 219813413629) ^ 419260 = (2 : ZMod 219813413629) ^ (209630 + 209630) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 209630 * (2 : ZMod 219813413629) ^ 209630 := by rw [pow_add]
          _ = 207098784159 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 219813413629) ^ 838521 = 58535454550 := by
        calc
          (2 : ZMod 219813413629) ^ 838521 = (2 : ZMod 219813413629) ^ (419260 + 419260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 419260 * (2 : ZMod 219813413629) ^ 419260) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 58535454550 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 219813413629) ^ 1677043 = 184289167545 := by
        calc
          (2 : ZMod 219813413629) ^ 1677043 = (2 : ZMod 219813413629) ^ (838521 + 838521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 838521 * (2 : ZMod 219813413629) ^ 838521) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 184289167545 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 219813413629) ^ 3354086 = 109793245807 := by
        calc
          (2 : ZMod 219813413629) ^ 3354086 = (2 : ZMod 219813413629) ^ (1677043 + 1677043) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 1677043 * (2 : ZMod 219813413629) ^ 1677043 := by rw [pow_add]
          _ = 109793245807 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 219813413629) ^ 6708173 = 165214172157 := by
        calc
          (2 : ZMod 219813413629) ^ 6708173 = (2 : ZMod 219813413629) ^ (3354086 + 3354086 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 3354086 * (2 : ZMod 219813413629) ^ 3354086) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 165214172157 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 219813413629) ^ 13416346 = 104335888650 := by
        calc
          (2 : ZMod 219813413629) ^ 13416346 = (2 : ZMod 219813413629) ^ (6708173 + 6708173) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 6708173 * (2 : ZMod 219813413629) ^ 6708173 := by rw [pow_add]
          _ = 104335888650 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 219813413629) ^ 26832692 = 193431037377 := by
        calc
          (2 : ZMod 219813413629) ^ 26832692 = (2 : ZMod 219813413629) ^ (13416346 + 13416346) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 13416346 * (2 : ZMod 219813413629) ^ 13416346 := by rw [pow_add]
          _ = 193431037377 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 219813413629) ^ 53665384 = 128737948141 := by
        calc
          (2 : ZMod 219813413629) ^ 53665384 = (2 : ZMod 219813413629) ^ (26832692 + 26832692) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 26832692 * (2 : ZMod 219813413629) ^ 26832692 := by rw [pow_add]
          _ = 128737948141 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 219813413629) ^ 107330768 = 54230736358 := by
        calc
          (2 : ZMod 219813413629) ^ 107330768 = (2 : ZMod 219813413629) ^ (53665384 + 53665384) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 53665384 * (2 : ZMod 219813413629) ^ 53665384 := by rw [pow_add]
          _ = 54230736358 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 219813413629) ^ 214661536 = 104282970950 := by
        calc
          (2 : ZMod 219813413629) ^ 214661536 = (2 : ZMod 219813413629) ^ (107330768 + 107330768) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 107330768 * (2 : ZMod 219813413629) ^ 107330768 := by rw [pow_add]
          _ = 104282970950 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 219813413629) ^ 429323073 = 39127649981 := by
        calc
          (2 : ZMod 219813413629) ^ 429323073 = (2 : ZMod 219813413629) ^ (214661536 + 214661536 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 214661536 * (2 : ZMod 219813413629) ^ 214661536) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 39127649981 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 219813413629) ^ 858646146 = 43498613190 := by
        calc
          (2 : ZMod 219813413629) ^ 858646146 = (2 : ZMod 219813413629) ^ (429323073 + 429323073) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 429323073 * (2 : ZMod 219813413629) ^ 429323073 := by rw [pow_add]
          _ = 43498613190 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 219813413629) ^ 1717292293 = 130783555166 := by
        calc
          (2 : ZMod 219813413629) ^ 1717292293 = (2 : ZMod 219813413629) ^ (858646146 + 858646146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 858646146 * (2 : ZMod 219813413629) ^ 858646146) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 130783555166 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 219813413629) ^ 3434584587 = 206167556694 := by
        calc
          (2 : ZMod 219813413629) ^ 3434584587 = (2 : ZMod 219813413629) ^ (1717292293 + 1717292293 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1717292293 * (2 : ZMod 219813413629) ^ 1717292293) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 206167556694 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 219813413629) ^ 6869169175 = 134888036668 := by
        calc
          (2 : ZMod 219813413629) ^ 6869169175 = (2 : ZMod 219813413629) ^ (3434584587 + 3434584587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 3434584587 * (2 : ZMod 219813413629) ^ 3434584587) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 134888036668 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 219813413629) ^ 13738338351 = 76713647422 := by
        calc
          (2 : ZMod 219813413629) ^ 13738338351 = (2 : ZMod 219813413629) ^ (6869169175 + 6869169175 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 6869169175 * (2 : ZMod 219813413629) ^ 6869169175) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 76713647422 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 219813413629) ^ 27476676703 = 25027677156 := by
        calc
          (2 : ZMod 219813413629) ^ 27476676703 = (2 : ZMod 219813413629) ^ (13738338351 + 13738338351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 13738338351 * (2 : ZMod 219813413629) ^ 13738338351) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 25027677156 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 219813413629) ^ 54953353407 = 50055354311 := by
        calc
          (2 : ZMod 219813413629) ^ 54953353407 = (2 : ZMod 219813413629) ^ (27476676703 + 27476676703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 27476676703 * (2 : ZMod 219813413629) ^ 27476676703) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 50055354311 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 219813413629) ^ 109906706814 = 219813413628 := by
        calc
          (2 : ZMod 219813413629) ^ 109906706814 = (2 : ZMod 219813413629) ^ (54953353407 + 54953353407) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 54953353407 * (2 : ZMod 219813413629) ^ 54953353407 := by rw [pow_add]
          _ = 219813413628 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 219813413629) ^ 219813413628 = 1 := by
        calc
          (2 : ZMod 219813413629) ^ 219813413628 = (2 : ZMod 219813413629) ^ (109906706814 + 109906706814) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 109906706814 * (2 : ZMod 219813413629) ^ 109906706814 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (18317784469, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (18317784469, 1)] : List FactorBlock).map factorBlockValue).prod = 219813413629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_18317784469) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 219813413629) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 219813413629) ^ 3 = 8 := by
        calc
          (2 : ZMod 219813413629) ^ 3 = (2 : ZMod 219813413629) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1 * (2 : ZMod 219813413629) ^ 1) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 219813413629) ^ 6 = 64 := by
        calc
          (2 : ZMod 219813413629) ^ 6 = (2 : ZMod 219813413629) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 3 * (2 : ZMod 219813413629) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 219813413629) ^ 12 = 4096 := by
        calc
          (2 : ZMod 219813413629) ^ 12 = (2 : ZMod 219813413629) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 6 * (2 : ZMod 219813413629) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 219813413629) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 219813413629) ^ 25 = (2 : ZMod 219813413629) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 12 * (2 : ZMod 219813413629) ^ 12) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 219813413629) ^ 51 = 31204469772 := by
        calc
          (2 : ZMod 219813413629) ^ 51 = (2 : ZMod 219813413629) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 25 * (2 : ZMod 219813413629) ^ 25) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 31204469772 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 219813413629) ^ 102 = 43042570278 := by
        calc
          (2 : ZMod 219813413629) ^ 102 = (2 : ZMod 219813413629) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 51 * (2 : ZMod 219813413629) ^ 51 := by rw [pow_add]
          _ = 43042570278 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 219813413629) ^ 204 = 178878636979 := by
        calc
          (2 : ZMod 219813413629) ^ 204 = (2 : ZMod 219813413629) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 102 * (2 : ZMod 219813413629) ^ 102 := by rw [pow_add]
          _ = 178878636979 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 219813413629) ^ 409 = 48956129319 := by
        calc
          (2 : ZMod 219813413629) ^ 409 = (2 : ZMod 219813413629) ^ (204 + 204 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 204 * (2 : ZMod 219813413629) ^ 204) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 48956129319 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 219813413629) ^ 818 = 119022367876 := by
        calc
          (2 : ZMod 219813413629) ^ 818 = (2 : ZMod 219813413629) ^ (409 + 409) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 409 * (2 : ZMod 219813413629) ^ 409 := by rw [pow_add]
          _ = 119022367876 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 219813413629) ^ 1637 = 59848713938 := by
        calc
          (2 : ZMod 219813413629) ^ 1637 = (2 : ZMod 219813413629) ^ (818 + 818 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 818 * (2 : ZMod 219813413629) ^ 818) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 59848713938 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 219813413629) ^ 3275 = 149436764938 := by
        calc
          (2 : ZMod 219813413629) ^ 3275 = (2 : ZMod 219813413629) ^ (1637 + 1637 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1637 * (2 : ZMod 219813413629) ^ 1637) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 149436764938 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 219813413629) ^ 6550 = 183224934130 := by
        calc
          (2 : ZMod 219813413629) ^ 6550 = (2 : ZMod 219813413629) ^ (3275 + 3275) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 3275 * (2 : ZMod 219813413629) ^ 3275 := by rw [pow_add]
          _ = 183224934130 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 219813413629) ^ 13101 = 156001378890 := by
        calc
          (2 : ZMod 219813413629) ^ 13101 = (2 : ZMod 219813413629) ^ (6550 + 6550 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 6550 * (2 : ZMod 219813413629) ^ 6550) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 156001378890 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 219813413629) ^ 26203 = 118343187014 := by
        calc
          (2 : ZMod 219813413629) ^ 26203 = (2 : ZMod 219813413629) ^ (13101 + 13101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 13101 * (2 : ZMod 219813413629) ^ 13101) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 118343187014 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 219813413629) ^ 52407 = 65329392702 := by
        calc
          (2 : ZMod 219813413629) ^ 52407 = (2 : ZMod 219813413629) ^ (26203 + 26203 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 26203 * (2 : ZMod 219813413629) ^ 26203) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 65329392702 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 219813413629) ^ 104815 = 197834104640 := by
        calc
          (2 : ZMod 219813413629) ^ 104815 = (2 : ZMod 219813413629) ^ (52407 + 52407 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 52407 * (2 : ZMod 219813413629) ^ 52407) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 197834104640 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 219813413629) ^ 209630 = 66193651401 := by
        calc
          (2 : ZMod 219813413629) ^ 209630 = (2 : ZMod 219813413629) ^ (104815 + 104815) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 104815 * (2 : ZMod 219813413629) ^ 104815 := by rw [pow_add]
          _ = 66193651401 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 219813413629) ^ 419260 = 207098784159 := by
        calc
          (2 : ZMod 219813413629) ^ 419260 = (2 : ZMod 219813413629) ^ (209630 + 209630) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 209630 * (2 : ZMod 219813413629) ^ 209630 := by rw [pow_add]
          _ = 207098784159 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 219813413629) ^ 838521 = 58535454550 := by
        calc
          (2 : ZMod 219813413629) ^ 838521 = (2 : ZMod 219813413629) ^ (419260 + 419260 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 419260 * (2 : ZMod 219813413629) ^ 419260) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 58535454550 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 219813413629) ^ 1677043 = 184289167545 := by
        calc
          (2 : ZMod 219813413629) ^ 1677043 = (2 : ZMod 219813413629) ^ (838521 + 838521 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 838521 * (2 : ZMod 219813413629) ^ 838521) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 184289167545 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 219813413629) ^ 3354086 = 109793245807 := by
        calc
          (2 : ZMod 219813413629) ^ 3354086 = (2 : ZMod 219813413629) ^ (1677043 + 1677043) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 1677043 * (2 : ZMod 219813413629) ^ 1677043 := by rw [pow_add]
          _ = 109793245807 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 219813413629) ^ 6708173 = 165214172157 := by
        calc
          (2 : ZMod 219813413629) ^ 6708173 = (2 : ZMod 219813413629) ^ (3354086 + 3354086 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 3354086 * (2 : ZMod 219813413629) ^ 3354086) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 165214172157 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 219813413629) ^ 13416346 = 104335888650 := by
        calc
          (2 : ZMod 219813413629) ^ 13416346 = (2 : ZMod 219813413629) ^ (6708173 + 6708173) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 6708173 * (2 : ZMod 219813413629) ^ 6708173 := by rw [pow_add]
          _ = 104335888650 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 219813413629) ^ 26832692 = 193431037377 := by
        calc
          (2 : ZMod 219813413629) ^ 26832692 = (2 : ZMod 219813413629) ^ (13416346 + 13416346) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 13416346 * (2 : ZMod 219813413629) ^ 13416346 := by rw [pow_add]
          _ = 193431037377 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 219813413629) ^ 53665384 = 128737948141 := by
        calc
          (2 : ZMod 219813413629) ^ 53665384 = (2 : ZMod 219813413629) ^ (26832692 + 26832692) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 26832692 * (2 : ZMod 219813413629) ^ 26832692 := by rw [pow_add]
          _ = 128737948141 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 219813413629) ^ 107330768 = 54230736358 := by
        calc
          (2 : ZMod 219813413629) ^ 107330768 = (2 : ZMod 219813413629) ^ (53665384 + 53665384) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 53665384 * (2 : ZMod 219813413629) ^ 53665384 := by rw [pow_add]
          _ = 54230736358 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 219813413629) ^ 214661536 = 104282970950 := by
        calc
          (2 : ZMod 219813413629) ^ 214661536 = (2 : ZMod 219813413629) ^ (107330768 + 107330768) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 107330768 * (2 : ZMod 219813413629) ^ 107330768 := by rw [pow_add]
          _ = 104282970950 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 219813413629) ^ 429323073 = 39127649981 := by
        calc
          (2 : ZMod 219813413629) ^ 429323073 = (2 : ZMod 219813413629) ^ (214661536 + 214661536 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 214661536 * (2 : ZMod 219813413629) ^ 214661536) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 39127649981 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 219813413629) ^ 858646146 = 43498613190 := by
        calc
          (2 : ZMod 219813413629) ^ 858646146 = (2 : ZMod 219813413629) ^ (429323073 + 429323073) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 429323073 * (2 : ZMod 219813413629) ^ 429323073 := by rw [pow_add]
          _ = 43498613190 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 219813413629) ^ 1717292293 = 130783555166 := by
        calc
          (2 : ZMod 219813413629) ^ 1717292293 = (2 : ZMod 219813413629) ^ (858646146 + 858646146 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 858646146 * (2 : ZMod 219813413629) ^ 858646146) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 130783555166 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 219813413629) ^ 3434584587 = 206167556694 := by
        calc
          (2 : ZMod 219813413629) ^ 3434584587 = (2 : ZMod 219813413629) ^ (1717292293 + 1717292293 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1717292293 * (2 : ZMod 219813413629) ^ 1717292293) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 206167556694 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 219813413629) ^ 6869169175 = 134888036668 := by
        calc
          (2 : ZMod 219813413629) ^ 6869169175 = (2 : ZMod 219813413629) ^ (3434584587 + 3434584587 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 3434584587 * (2 : ZMod 219813413629) ^ 3434584587) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 134888036668 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 219813413629) ^ 13738338351 = 76713647422 := by
        calc
          (2 : ZMod 219813413629) ^ 13738338351 = (2 : ZMod 219813413629) ^ (6869169175 + 6869169175 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 6869169175 * (2 : ZMod 219813413629) ^ 6869169175) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 76713647422 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 219813413629) ^ 27476676703 = 25027677156 := by
        calc
          (2 : ZMod 219813413629) ^ 27476676703 = (2 : ZMod 219813413629) ^ (13738338351 + 13738338351 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 13738338351 * (2 : ZMod 219813413629) ^ 13738338351) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 25027677156 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 219813413629) ^ 54953353407 = 50055354311 := by
        calc
          (2 : ZMod 219813413629) ^ 54953353407 = (2 : ZMod 219813413629) ^ (27476676703 + 27476676703 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 27476676703 * (2 : ZMod 219813413629) ^ 27476676703) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 50055354311 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 219813413629) ^ 109906706814 = 219813413628 := by
        calc
          (2 : ZMod 219813413629) ^ 109906706814 = (2 : ZMod 219813413629) ^ (54953353407 + 54953353407) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 54953353407 * (2 : ZMod 219813413629) ^ 54953353407 := by rw [pow_add]
          _ = 219813413628 := by rw [factor_0_35]; decide
      change (2 : ZMod 219813413629) ^ 109906706814 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (2 : ZMod 219813413629) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 219813413629) ^ 2 = 4 := by
        calc
          (2 : ZMod 219813413629) ^ 2 = (2 : ZMod 219813413629) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 1 * (2 : ZMod 219813413629) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 219813413629) ^ 4 = 16 := by
        calc
          (2 : ZMod 219813413629) ^ 4 = (2 : ZMod 219813413629) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 2 * (2 : ZMod 219813413629) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 219813413629) ^ 8 = 256 := by
        calc
          (2 : ZMod 219813413629) ^ 8 = (2 : ZMod 219813413629) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 4 * (2 : ZMod 219813413629) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 219813413629) ^ 17 = 131072 := by
        calc
          (2 : ZMod 219813413629) ^ 17 = (2 : ZMod 219813413629) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 8 * (2 : ZMod 219813413629) ^ 8) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 219813413629) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 219813413629) ^ 34 = (2 : ZMod 219813413629) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 17 * (2 : ZMod 219813413629) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 219813413629) ^ 68 = 183887974410 := by
        calc
          (2 : ZMod 219813413629) ^ 68 = (2 : ZMod 219813413629) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 34 * (2 : ZMod 219813413629) ^ 34 := by rw [pow_add]
          _ = 183887974410 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 219813413629) ^ 136 = 148314484877 := by
        calc
          (2 : ZMod 219813413629) ^ 136 = (2 : ZMod 219813413629) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 68 * (2 : ZMod 219813413629) ^ 68 := by rw [pow_add]
          _ = 148314484877 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 219813413629) ^ 272 = 108324133811 := by
        calc
          (2 : ZMod 219813413629) ^ 272 = (2 : ZMod 219813413629) ^ (136 + 136) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 136 * (2 : ZMod 219813413629) ^ 136 := by rw [pow_add]
          _ = 108324133811 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 219813413629) ^ 545 = 74581948447 := by
        calc
          (2 : ZMod 219813413629) ^ 545 = (2 : ZMod 219813413629) ^ (272 + 272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 272 * (2 : ZMod 219813413629) ^ 272) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 74581948447 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 219813413629) ^ 1091 = 196337096236 := by
        calc
          (2 : ZMod 219813413629) ^ 1091 = (2 : ZMod 219813413629) ^ (545 + 545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 545 * (2 : ZMod 219813413629) ^ 545) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 196337096236 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 219813413629) ^ 2183 = 152032059146 := by
        calc
          (2 : ZMod 219813413629) ^ 2183 = (2 : ZMod 219813413629) ^ (1091 + 1091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1091 * (2 : ZMod 219813413629) ^ 1091) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 152032059146 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 219813413629) ^ 4367 = 116939339930 := by
        calc
          (2 : ZMod 219813413629) ^ 4367 = (2 : ZMod 219813413629) ^ (2183 + 2183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 2183 * (2 : ZMod 219813413629) ^ 2183) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 116939339930 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 219813413629) ^ 8734 = 99621643565 := by
        calc
          (2 : ZMod 219813413629) ^ 8734 = (2 : ZMod 219813413629) ^ (4367 + 4367) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 4367 * (2 : ZMod 219813413629) ^ 4367 := by rw [pow_add]
          _ = 99621643565 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 219813413629) ^ 17469 = 195822653077 := by
        calc
          (2 : ZMod 219813413629) ^ 17469 = (2 : ZMod 219813413629) ^ (8734 + 8734 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 8734 * (2 : ZMod 219813413629) ^ 8734) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 195822653077 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 219813413629) ^ 34938 = 157573685576 := by
        calc
          (2 : ZMod 219813413629) ^ 34938 = (2 : ZMod 219813413629) ^ (17469 + 17469) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 17469 * (2 : ZMod 219813413629) ^ 17469 := by rw [pow_add]
          _ = 157573685576 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 219813413629) ^ 69876 = 119319444177 := by
        calc
          (2 : ZMod 219813413629) ^ 69876 = (2 : ZMod 219813413629) ^ (34938 + 34938) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 34938 * (2 : ZMod 219813413629) ^ 34938 := by rw [pow_add]
          _ = 119319444177 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 219813413629) ^ 139753 = 153553194299 := by
        calc
          (2 : ZMod 219813413629) ^ 139753 = (2 : ZMod 219813413629) ^ (69876 + 69876 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 69876 * (2 : ZMod 219813413629) ^ 69876) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 153553194299 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 219813413629) ^ 279507 = 45839618878 := by
        calc
          (2 : ZMod 219813413629) ^ 279507 = (2 : ZMod 219813413629) ^ (139753 + 139753 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 139753 * (2 : ZMod 219813413629) ^ 139753) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 45839618878 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 219813413629) ^ 559014 = 196684643085 := by
        calc
          (2 : ZMod 219813413629) ^ 559014 = (2 : ZMod 219813413629) ^ (279507 + 279507) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 279507 * (2 : ZMod 219813413629) ^ 279507 := by rw [pow_add]
          _ = 196684643085 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 219813413629) ^ 1118028 = 74912640035 := by
        calc
          (2 : ZMod 219813413629) ^ 1118028 = (2 : ZMod 219813413629) ^ (559014 + 559014) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 559014 * (2 : ZMod 219813413629) ^ 559014 := by rw [pow_add]
          _ = 74912640035 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 219813413629) ^ 2236057 = 212157472089 := by
        calc
          (2 : ZMod 219813413629) ^ 2236057 = (2 : ZMod 219813413629) ^ (1118028 + 1118028 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1118028 * (2 : ZMod 219813413629) ^ 1118028) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 212157472089 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 219813413629) ^ 4472115 = 48960974386 := by
        calc
          (2 : ZMod 219813413629) ^ 4472115 = (2 : ZMod 219813413629) ^ (2236057 + 2236057 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 2236057 * (2 : ZMod 219813413629) ^ 2236057) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 48960974386 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 219813413629) ^ 8944230 = 109193288313 := by
        calc
          (2 : ZMod 219813413629) ^ 8944230 = (2 : ZMod 219813413629) ^ (4472115 + 4472115) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 4472115 * (2 : ZMod 219813413629) ^ 4472115 := by rw [pow_add]
          _ = 109193288313 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 219813413629) ^ 17888461 = 67617904380 := by
        calc
          (2 : ZMod 219813413629) ^ 17888461 = (2 : ZMod 219813413629) ^ (8944230 + 8944230 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 8944230 * (2 : ZMod 219813413629) ^ 8944230) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 67617904380 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 219813413629) ^ 35776922 = 118472497368 := by
        calc
          (2 : ZMod 219813413629) ^ 35776922 = (2 : ZMod 219813413629) ^ (17888461 + 17888461) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 17888461 * (2 : ZMod 219813413629) ^ 17888461 := by rw [pow_add]
          _ = 118472497368 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 219813413629) ^ 71553845 = 191753147728 := by
        calc
          (2 : ZMod 219813413629) ^ 71553845 = (2 : ZMod 219813413629) ^ (35776922 + 35776922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 35776922 * (2 : ZMod 219813413629) ^ 35776922) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 191753147728 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 219813413629) ^ 143107691 = 82654776023 := by
        calc
          (2 : ZMod 219813413629) ^ 143107691 = (2 : ZMod 219813413629) ^ (71553845 + 71553845 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 71553845 * (2 : ZMod 219813413629) ^ 71553845) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 82654776023 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 219813413629) ^ 286215382 = 168199641223 := by
        calc
          (2 : ZMod 219813413629) ^ 286215382 = (2 : ZMod 219813413629) ^ (143107691 + 143107691) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 143107691 * (2 : ZMod 219813413629) ^ 143107691 := by rw [pow_add]
          _ = 168199641223 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 219813413629) ^ 572430764 = 206423662479 := by
        calc
          (2 : ZMod 219813413629) ^ 572430764 = (2 : ZMod 219813413629) ^ (286215382 + 286215382) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 286215382 * (2 : ZMod 219813413629) ^ 286215382 := by rw [pow_add]
          _ = 206423662479 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 219813413629) ^ 1144861529 = 39858471245 := by
        calc
          (2 : ZMod 219813413629) ^ 1144861529 = (2 : ZMod 219813413629) ^ (572430764 + 572430764 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 572430764 * (2 : ZMod 219813413629) ^ 572430764) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 39858471245 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 219813413629) ^ 2289723058 = 29718816415 := by
        calc
          (2 : ZMod 219813413629) ^ 2289723058 = (2 : ZMod 219813413629) ^ (1144861529 + 1144861529) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 1144861529 * (2 : ZMod 219813413629) ^ 1144861529 := by rw [pow_add]
          _ = 29718816415 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 219813413629) ^ 4579446117 = 159731135726 := by
        calc
          (2 : ZMod 219813413629) ^ 4579446117 = (2 : ZMod 219813413629) ^ (2289723058 + 2289723058 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 2289723058 * (2 : ZMod 219813413629) ^ 2289723058) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 159731135726 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 219813413629) ^ 9158892234 = 140313173916 := by
        calc
          (2 : ZMod 219813413629) ^ 9158892234 = (2 : ZMod 219813413629) ^ (4579446117 + 4579446117) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 4579446117 * (2 : ZMod 219813413629) ^ 4579446117 := by rw [pow_add]
          _ = 140313173916 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 219813413629) ^ 18317784469 = 210634482451 := by
        calc
          (2 : ZMod 219813413629) ^ 18317784469 = (2 : ZMod 219813413629) ^ (9158892234 + 9158892234 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 9158892234 * (2 : ZMod 219813413629) ^ 9158892234) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 210634482451 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 219813413629) ^ 36635568938 = 120047219692 := by
        calc
          (2 : ZMod 219813413629) ^ 36635568938 = (2 : ZMod 219813413629) ^ (18317784469 + 18317784469) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 18317784469 * (2 : ZMod 219813413629) ^ 18317784469 := by rw [pow_add]
          _ = 120047219692 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 219813413629) ^ 73271137876 = 120047219691 := by
        calc
          (2 : ZMod 219813413629) ^ 73271137876 = (2 : ZMod 219813413629) ^ (36635568938 + 36635568938) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 36635568938 * (2 : ZMod 219813413629) ^ 36635568938 := by rw [pow_add]
          _ = 120047219691 := by rw [factor_1_35]; decide
      change (2 : ZMod 219813413629) ^ 73271137876 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (2 : ZMod 219813413629) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 219813413629) ^ 3 = 8 := by
        calc
          (2 : ZMod 219813413629) ^ 3 = (2 : ZMod 219813413629) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = ((2 : ZMod 219813413629) ^ 1 * (2 : ZMod 219813413629) ^ 1) * (2 : ZMod 219813413629) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 219813413629) ^ 6 = 64 := by
        calc
          (2 : ZMod 219813413629) ^ 6 = (2 : ZMod 219813413629) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 3 * (2 : ZMod 219813413629) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 219813413629) ^ 12 = 4096 := by
        calc
          (2 : ZMod 219813413629) ^ 12 = (2 : ZMod 219813413629) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 219813413629) ^ n) (by norm_num)
          _ = (2 : ZMod 219813413629) ^ 6 * (2 : ZMod 219813413629) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      change (2 : ZMod 219813413629) ^ 12 ≠ 1
      rw [factor_2_3]
      decide

#print axioms prime_lucas_219813413629

end TotientTailPeriodKiller
end Erdos249257
