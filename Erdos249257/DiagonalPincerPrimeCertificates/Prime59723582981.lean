import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime175657597

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_59723582981 : Nat.Prime 59723582981 := by
  apply lucas_primality 59723582981 (2 : ZMod 59723582981)
  ·
      have fermat_0 : (2 : ZMod 59723582981) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 59723582981) ^ 3 = 8 := by
        calc
          (2 : ZMod 59723582981) ^ 3 = (2 : ZMod 59723582981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 1 * (2 : ZMod 59723582981) ^ 1) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 59723582981) ^ 6 = 64 := by
        calc
          (2 : ZMod 59723582981) ^ 6 = (2 : ZMod 59723582981) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3 * (2 : ZMod 59723582981) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 59723582981) ^ 13 = 8192 := by
        calc
          (2 : ZMod 59723582981) ^ 13 = (2 : ZMod 59723582981) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 6 * (2 : ZMod 59723582981) ^ 6) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 59723582981) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 59723582981) ^ 27 = (2 : ZMod 59723582981) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 13 * (2 : ZMod 59723582981) ^ 13) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 59723582981) ^ 55 = 8073428889 := by
        calc
          (2 : ZMod 59723582981) ^ 55 = (2 : ZMod 59723582981) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 27 * (2 : ZMod 59723582981) ^ 27) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8073428889 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 59723582981) ^ 111 = 50738557096 := by
        calc
          (2 : ZMod 59723582981) ^ 111 = (2 : ZMod 59723582981) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 55 * (2 : ZMod 59723582981) ^ 55) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 50738557096 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 59723582981) ^ 222 = 30218704249 := by
        calc
          (2 : ZMod 59723582981) ^ 222 = (2 : ZMod 59723582981) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 111 * (2 : ZMod 59723582981) ^ 111 := by rw [pow_add]
          _ = 30218704249 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 59723582981) ^ 444 = 2612855399 := by
        calc
          (2 : ZMod 59723582981) ^ 444 = (2 : ZMod 59723582981) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 222 * (2 : ZMod 59723582981) ^ 222 := by rw [pow_add]
          _ = 2612855399 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 59723582981) ^ 889 = 48625886109 := by
        calc
          (2 : ZMod 59723582981) ^ 889 = (2 : ZMod 59723582981) ^ (444 + 444 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 444 * (2 : ZMod 59723582981) ^ 444) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 48625886109 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 59723582981) ^ 1779 = 11551728278 := by
        calc
          (2 : ZMod 59723582981) ^ 1779 = (2 : ZMod 59723582981) ^ (889 + 889 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 889 * (2 : ZMod 59723582981) ^ 889) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 11551728278 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 59723582981) ^ 3559 = 10772646844 := by
        calc
          (2 : ZMod 59723582981) ^ 3559 = (2 : ZMod 59723582981) ^ (1779 + 1779 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 1779 * (2 : ZMod 59723582981) ^ 1779) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 10772646844 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 59723582981) ^ 7119 = 6907225436 := by
        calc
          (2 : ZMod 59723582981) ^ 7119 = (2 : ZMod 59723582981) ^ (3559 + 3559 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 3559 * (2 : ZMod 59723582981) ^ 3559) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 6907225436 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 59723582981) ^ 14239 = 21227112292 := by
        calc
          (2 : ZMod 59723582981) ^ 14239 = (2 : ZMod 59723582981) ^ (7119 + 7119 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 7119 * (2 : ZMod 59723582981) ^ 7119) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 21227112292 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 59723582981) ^ 28478 = 11317847395 := by
        calc
          (2 : ZMod 59723582981) ^ 28478 = (2 : ZMod 59723582981) ^ (14239 + 14239) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 14239 * (2 : ZMod 59723582981) ^ 14239 := by rw [pow_add]
          _ = 11317847395 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 59723582981) ^ 56956 = 49879056998 := by
        calc
          (2 : ZMod 59723582981) ^ 56956 = (2 : ZMod 59723582981) ^ (28478 + 28478) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 28478 * (2 : ZMod 59723582981) ^ 28478 := by rw [pow_add]
          _ = 49879056998 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 59723582981) ^ 113913 = 33279555544 := by
        calc
          (2 : ZMod 59723582981) ^ 113913 = (2 : ZMod 59723582981) ^ (56956 + 56956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 56956 * (2 : ZMod 59723582981) ^ 56956) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 33279555544 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 59723582981) ^ 227827 = 32320981392 := by
        calc
          (2 : ZMod 59723582981) ^ 227827 = (2 : ZMod 59723582981) ^ (113913 + 113913 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 113913 * (2 : ZMod 59723582981) ^ 113913) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 32320981392 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 59723582981) ^ 455654 = 46718819515 := by
        calc
          (2 : ZMod 59723582981) ^ 455654 = (2 : ZMod 59723582981) ^ (227827 + 227827) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 227827 * (2 : ZMod 59723582981) ^ 227827 := by rw [pow_add]
          _ = 46718819515 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 59723582981) ^ 911309 = 25264157953 := by
        calc
          (2 : ZMod 59723582981) ^ 911309 = (2 : ZMod 59723582981) ^ (455654 + 455654 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 455654 * (2 : ZMod 59723582981) ^ 455654) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 25264157953 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 59723582981) ^ 1822619 = 17413302821 := by
        calc
          (2 : ZMod 59723582981) ^ 1822619 = (2 : ZMod 59723582981) ^ (911309 + 911309 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 911309 * (2 : ZMod 59723582981) ^ 911309) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 17413302821 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 59723582981) ^ 3645238 = 32458144909 := by
        calc
          (2 : ZMod 59723582981) ^ 3645238 = (2 : ZMod 59723582981) ^ (1822619 + 1822619) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1822619 * (2 : ZMod 59723582981) ^ 1822619 := by rw [pow_add]
          _ = 32458144909 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 59723582981) ^ 7290476 = 20226983376 := by
        calc
          (2 : ZMod 59723582981) ^ 7290476 = (2 : ZMod 59723582981) ^ (3645238 + 3645238) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3645238 * (2 : ZMod 59723582981) ^ 3645238 := by rw [pow_add]
          _ = 20226983376 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 59723582981) ^ 14580952 = 20563873143 := by
        calc
          (2 : ZMod 59723582981) ^ 14580952 = (2 : ZMod 59723582981) ^ (7290476 + 7290476) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 7290476 * (2 : ZMod 59723582981) ^ 7290476 := by rw [pow_add]
          _ = 20563873143 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 59723582981) ^ 29161905 = 25493312286 := by
        calc
          (2 : ZMod 59723582981) ^ 29161905 = (2 : ZMod 59723582981) ^ (14580952 + 14580952 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 14580952 * (2 : ZMod 59723582981) ^ 14580952) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 25493312286 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 59723582981) ^ 58323811 = 51434252441 := by
        calc
          (2 : ZMod 59723582981) ^ 58323811 = (2 : ZMod 59723582981) ^ (29161905 + 29161905 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 29161905 * (2 : ZMod 59723582981) ^ 29161905) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 51434252441 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 59723582981) ^ 116647623 = 51780484271 := by
        calc
          (2 : ZMod 59723582981) ^ 116647623 = (2 : ZMod 59723582981) ^ (58323811 + 58323811 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 58323811 * (2 : ZMod 59723582981) ^ 58323811) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 51780484271 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 59723582981) ^ 233295246 = 49400875243 := by
        calc
          (2 : ZMod 59723582981) ^ 233295246 = (2 : ZMod 59723582981) ^ (116647623 + 116647623) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 116647623 * (2 : ZMod 59723582981) ^ 116647623 := by rw [pow_add]
          _ = 49400875243 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 59723582981) ^ 466590492 = 34685798660 := by
        calc
          (2 : ZMod 59723582981) ^ 466590492 = (2 : ZMod 59723582981) ^ (233295246 + 233295246) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 233295246 * (2 : ZMod 59723582981) ^ 233295246 := by rw [pow_add]
          _ = 34685798660 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 59723582981) ^ 933180984 = 35527303774 := by
        calc
          (2 : ZMod 59723582981) ^ 933180984 = (2 : ZMod 59723582981) ^ (466590492 + 466590492) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 466590492 * (2 : ZMod 59723582981) ^ 466590492 := by rw [pow_add]
          _ = 35527303774 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 59723582981) ^ 1866361968 = 47435118097 := by
        calc
          (2 : ZMod 59723582981) ^ 1866361968 = (2 : ZMod 59723582981) ^ (933180984 + 933180984) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 933180984 * (2 : ZMod 59723582981) ^ 933180984 := by rw [pow_add]
          _ = 47435118097 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 59723582981) ^ 3732723936 = 36832344926 := by
        calc
          (2 : ZMod 59723582981) ^ 3732723936 = (2 : ZMod 59723582981) ^ (1866361968 + 1866361968) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1866361968 * (2 : ZMod 59723582981) ^ 1866361968 := by rw [pow_add]
          _ = 36832344926 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 59723582981) ^ 7465447872 = 35388239140 := by
        calc
          (2 : ZMod 59723582981) ^ 7465447872 = (2 : ZMod 59723582981) ^ (3732723936 + 3732723936) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3732723936 * (2 : ZMod 59723582981) ^ 3732723936 := by rw [pow_add]
          _ = 35388239140 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 59723582981) ^ 14930895745 = 11052895298 := by
        calc
          (2 : ZMod 59723582981) ^ 14930895745 = (2 : ZMod 59723582981) ^ (7465447872 + 7465447872 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 7465447872 * (2 : ZMod 59723582981) ^ 7465447872) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 11052895298 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 59723582981) ^ 29861791490 = 59723582980 := by
        calc
          (2 : ZMod 59723582981) ^ 29861791490 = (2 : ZMod 59723582981) ^ (14930895745 + 14930895745) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 14930895745 * (2 : ZMod 59723582981) ^ 14930895745 := by rw [pow_add]
          _ = 59723582980 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 59723582981) ^ 59723582980 = 1 := by
        calc
          (2 : ZMod 59723582981) ^ 59723582980 = (2 : ZMod 59723582981) ^ (29861791490 + 29861791490) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 29861791490 * (2 : ZMod 59723582981) ^ 29861791490 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (17, 1), (175657597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (17, 1), (175657597, 1)] : List FactorBlock).map factorBlockValue).prod = 59723582981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_175657597) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 59723582981) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 59723582981) ^ 3 = 8 := by
        calc
          (2 : ZMod 59723582981) ^ 3 = (2 : ZMod 59723582981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 1 * (2 : ZMod 59723582981) ^ 1) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 59723582981) ^ 6 = 64 := by
        calc
          (2 : ZMod 59723582981) ^ 6 = (2 : ZMod 59723582981) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3 * (2 : ZMod 59723582981) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 59723582981) ^ 13 = 8192 := by
        calc
          (2 : ZMod 59723582981) ^ 13 = (2 : ZMod 59723582981) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 6 * (2 : ZMod 59723582981) ^ 6) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 59723582981) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 59723582981) ^ 27 = (2 : ZMod 59723582981) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 13 * (2 : ZMod 59723582981) ^ 13) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 59723582981) ^ 55 = 8073428889 := by
        calc
          (2 : ZMod 59723582981) ^ 55 = (2 : ZMod 59723582981) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 27 * (2 : ZMod 59723582981) ^ 27) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8073428889 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 59723582981) ^ 111 = 50738557096 := by
        calc
          (2 : ZMod 59723582981) ^ 111 = (2 : ZMod 59723582981) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 55 * (2 : ZMod 59723582981) ^ 55) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 50738557096 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 59723582981) ^ 222 = 30218704249 := by
        calc
          (2 : ZMod 59723582981) ^ 222 = (2 : ZMod 59723582981) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 111 * (2 : ZMod 59723582981) ^ 111 := by rw [pow_add]
          _ = 30218704249 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 59723582981) ^ 444 = 2612855399 := by
        calc
          (2 : ZMod 59723582981) ^ 444 = (2 : ZMod 59723582981) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 222 * (2 : ZMod 59723582981) ^ 222 := by rw [pow_add]
          _ = 2612855399 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 59723582981) ^ 889 = 48625886109 := by
        calc
          (2 : ZMod 59723582981) ^ 889 = (2 : ZMod 59723582981) ^ (444 + 444 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 444 * (2 : ZMod 59723582981) ^ 444) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 48625886109 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 59723582981) ^ 1779 = 11551728278 := by
        calc
          (2 : ZMod 59723582981) ^ 1779 = (2 : ZMod 59723582981) ^ (889 + 889 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 889 * (2 : ZMod 59723582981) ^ 889) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 11551728278 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 59723582981) ^ 3559 = 10772646844 := by
        calc
          (2 : ZMod 59723582981) ^ 3559 = (2 : ZMod 59723582981) ^ (1779 + 1779 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 1779 * (2 : ZMod 59723582981) ^ 1779) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 10772646844 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 59723582981) ^ 7119 = 6907225436 := by
        calc
          (2 : ZMod 59723582981) ^ 7119 = (2 : ZMod 59723582981) ^ (3559 + 3559 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 3559 * (2 : ZMod 59723582981) ^ 3559) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 6907225436 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 59723582981) ^ 14239 = 21227112292 := by
        calc
          (2 : ZMod 59723582981) ^ 14239 = (2 : ZMod 59723582981) ^ (7119 + 7119 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 7119 * (2 : ZMod 59723582981) ^ 7119) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 21227112292 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 59723582981) ^ 28478 = 11317847395 := by
        calc
          (2 : ZMod 59723582981) ^ 28478 = (2 : ZMod 59723582981) ^ (14239 + 14239) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 14239 * (2 : ZMod 59723582981) ^ 14239 := by rw [pow_add]
          _ = 11317847395 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 59723582981) ^ 56956 = 49879056998 := by
        calc
          (2 : ZMod 59723582981) ^ 56956 = (2 : ZMod 59723582981) ^ (28478 + 28478) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 28478 * (2 : ZMod 59723582981) ^ 28478 := by rw [pow_add]
          _ = 49879056998 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 59723582981) ^ 113913 = 33279555544 := by
        calc
          (2 : ZMod 59723582981) ^ 113913 = (2 : ZMod 59723582981) ^ (56956 + 56956 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 56956 * (2 : ZMod 59723582981) ^ 56956) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 33279555544 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 59723582981) ^ 227827 = 32320981392 := by
        calc
          (2 : ZMod 59723582981) ^ 227827 = (2 : ZMod 59723582981) ^ (113913 + 113913 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 113913 * (2 : ZMod 59723582981) ^ 113913) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 32320981392 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 59723582981) ^ 455654 = 46718819515 := by
        calc
          (2 : ZMod 59723582981) ^ 455654 = (2 : ZMod 59723582981) ^ (227827 + 227827) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 227827 * (2 : ZMod 59723582981) ^ 227827 := by rw [pow_add]
          _ = 46718819515 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 59723582981) ^ 911309 = 25264157953 := by
        calc
          (2 : ZMod 59723582981) ^ 911309 = (2 : ZMod 59723582981) ^ (455654 + 455654 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 455654 * (2 : ZMod 59723582981) ^ 455654) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 25264157953 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 59723582981) ^ 1822619 = 17413302821 := by
        calc
          (2 : ZMod 59723582981) ^ 1822619 = (2 : ZMod 59723582981) ^ (911309 + 911309 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 911309 * (2 : ZMod 59723582981) ^ 911309) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 17413302821 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 59723582981) ^ 3645238 = 32458144909 := by
        calc
          (2 : ZMod 59723582981) ^ 3645238 = (2 : ZMod 59723582981) ^ (1822619 + 1822619) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1822619 * (2 : ZMod 59723582981) ^ 1822619 := by rw [pow_add]
          _ = 32458144909 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 59723582981) ^ 7290476 = 20226983376 := by
        calc
          (2 : ZMod 59723582981) ^ 7290476 = (2 : ZMod 59723582981) ^ (3645238 + 3645238) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3645238 * (2 : ZMod 59723582981) ^ 3645238 := by rw [pow_add]
          _ = 20226983376 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 59723582981) ^ 14580952 = 20563873143 := by
        calc
          (2 : ZMod 59723582981) ^ 14580952 = (2 : ZMod 59723582981) ^ (7290476 + 7290476) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 7290476 * (2 : ZMod 59723582981) ^ 7290476 := by rw [pow_add]
          _ = 20563873143 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 59723582981) ^ 29161905 = 25493312286 := by
        calc
          (2 : ZMod 59723582981) ^ 29161905 = (2 : ZMod 59723582981) ^ (14580952 + 14580952 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 14580952 * (2 : ZMod 59723582981) ^ 14580952) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 25493312286 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 59723582981) ^ 58323811 = 51434252441 := by
        calc
          (2 : ZMod 59723582981) ^ 58323811 = (2 : ZMod 59723582981) ^ (29161905 + 29161905 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 29161905 * (2 : ZMod 59723582981) ^ 29161905) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 51434252441 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 59723582981) ^ 116647623 = 51780484271 := by
        calc
          (2 : ZMod 59723582981) ^ 116647623 = (2 : ZMod 59723582981) ^ (58323811 + 58323811 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 58323811 * (2 : ZMod 59723582981) ^ 58323811) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 51780484271 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 59723582981) ^ 233295246 = 49400875243 := by
        calc
          (2 : ZMod 59723582981) ^ 233295246 = (2 : ZMod 59723582981) ^ (116647623 + 116647623) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 116647623 * (2 : ZMod 59723582981) ^ 116647623 := by rw [pow_add]
          _ = 49400875243 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 59723582981) ^ 466590492 = 34685798660 := by
        calc
          (2 : ZMod 59723582981) ^ 466590492 = (2 : ZMod 59723582981) ^ (233295246 + 233295246) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 233295246 * (2 : ZMod 59723582981) ^ 233295246 := by rw [pow_add]
          _ = 34685798660 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 59723582981) ^ 933180984 = 35527303774 := by
        calc
          (2 : ZMod 59723582981) ^ 933180984 = (2 : ZMod 59723582981) ^ (466590492 + 466590492) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 466590492 * (2 : ZMod 59723582981) ^ 466590492 := by rw [pow_add]
          _ = 35527303774 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 59723582981) ^ 1866361968 = 47435118097 := by
        calc
          (2 : ZMod 59723582981) ^ 1866361968 = (2 : ZMod 59723582981) ^ (933180984 + 933180984) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 933180984 * (2 : ZMod 59723582981) ^ 933180984 := by rw [pow_add]
          _ = 47435118097 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 59723582981) ^ 3732723936 = 36832344926 := by
        calc
          (2 : ZMod 59723582981) ^ 3732723936 = (2 : ZMod 59723582981) ^ (1866361968 + 1866361968) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1866361968 * (2 : ZMod 59723582981) ^ 1866361968 := by rw [pow_add]
          _ = 36832344926 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 59723582981) ^ 7465447872 = 35388239140 := by
        calc
          (2 : ZMod 59723582981) ^ 7465447872 = (2 : ZMod 59723582981) ^ (3732723936 + 3732723936) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3732723936 * (2 : ZMod 59723582981) ^ 3732723936 := by rw [pow_add]
          _ = 35388239140 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 59723582981) ^ 14930895745 = 11052895298 := by
        calc
          (2 : ZMod 59723582981) ^ 14930895745 = (2 : ZMod 59723582981) ^ (7465447872 + 7465447872 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 7465447872 * (2 : ZMod 59723582981) ^ 7465447872) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 11052895298 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 59723582981) ^ 29861791490 = 59723582980 := by
        calc
          (2 : ZMod 59723582981) ^ 29861791490 = (2 : ZMod 59723582981) ^ (14930895745 + 14930895745) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 14930895745 * (2 : ZMod 59723582981) ^ 14930895745 := by rw [pow_add]
          _ = 59723582980 := by rw [factor_0_33]; decide
      change (2 : ZMod 59723582981) ^ 29861791490 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (2 : ZMod 59723582981) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 59723582981) ^ 2 = 4 := by
        calc
          (2 : ZMod 59723582981) ^ 2 = (2 : ZMod 59723582981) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1 * (2 : ZMod 59723582981) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 59723582981) ^ 5 = 32 := by
        calc
          (2 : ZMod 59723582981) ^ 5 = (2 : ZMod 59723582981) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 2 * (2 : ZMod 59723582981) ^ 2) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 59723582981) ^ 11 = 2048 := by
        calc
          (2 : ZMod 59723582981) ^ 11 = (2 : ZMod 59723582981) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 5 * (2 : ZMod 59723582981) ^ 5) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 59723582981) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 59723582981) ^ 22 = (2 : ZMod 59723582981) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 11 * (2 : ZMod 59723582981) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 59723582981) ^ 44 = 33452648002 := by
        calc
          (2 : ZMod 59723582981) ^ 44 = (2 : ZMod 59723582981) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 22 * (2 : ZMod 59723582981) ^ 22 := by rw [pow_add]
          _ = 33452648002 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 59723582981) ^ 88 = 36440484258 := by
        calc
          (2 : ZMod 59723582981) ^ 88 = (2 : ZMod 59723582981) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 44 * (2 : ZMod 59723582981) ^ 44 := by rw [pow_add]
          _ = 36440484258 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 59723582981) ^ 177 = 20284224361 := by
        calc
          (2 : ZMod 59723582981) ^ 177 = (2 : ZMod 59723582981) ^ (88 + 88 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 88 * (2 : ZMod 59723582981) ^ 88) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 20284224361 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 59723582981) ^ 355 = 25666088011 := by
        calc
          (2 : ZMod 59723582981) ^ 355 = (2 : ZMod 59723582981) ^ (177 + 177 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 177 * (2 : ZMod 59723582981) ^ 177) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 25666088011 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 59723582981) ^ 711 = 15871593862 := by
        calc
          (2 : ZMod 59723582981) ^ 711 = (2 : ZMod 59723582981) ^ (355 + 355 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 355 * (2 : ZMod 59723582981) ^ 355) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 15871593862 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 59723582981) ^ 1423 = 12736498640 := by
        calc
          (2 : ZMod 59723582981) ^ 1423 = (2 : ZMod 59723582981) ^ (711 + 711 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 711 * (2 : ZMod 59723582981) ^ 711) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 12736498640 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 59723582981) ^ 2847 = 23038363615 := by
        calc
          (2 : ZMod 59723582981) ^ 2847 = (2 : ZMod 59723582981) ^ (1423 + 1423 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 1423 * (2 : ZMod 59723582981) ^ 1423) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 23038363615 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 59723582981) ^ 5695 = 51127699595 := by
        calc
          (2 : ZMod 59723582981) ^ 5695 = (2 : ZMod 59723582981) ^ (2847 + 2847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 2847 * (2 : ZMod 59723582981) ^ 2847) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 51127699595 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 59723582981) ^ 11391 = 45227660353 := by
        calc
          (2 : ZMod 59723582981) ^ 11391 = (2 : ZMod 59723582981) ^ (5695 + 5695 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 5695 * (2 : ZMod 59723582981) ^ 5695) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 45227660353 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 59723582981) ^ 22782 = 30467571692 := by
        calc
          (2 : ZMod 59723582981) ^ 22782 = (2 : ZMod 59723582981) ^ (11391 + 11391) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 11391 * (2 : ZMod 59723582981) ^ 11391 := by rw [pow_add]
          _ = 30467571692 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 59723582981) ^ 45565 = 45976354479 := by
        calc
          (2 : ZMod 59723582981) ^ 45565 = (2 : ZMod 59723582981) ^ (22782 + 22782 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 22782 * (2 : ZMod 59723582981) ^ 22782) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 45976354479 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 59723582981) ^ 91130 = 48975729979 := by
        calc
          (2 : ZMod 59723582981) ^ 91130 = (2 : ZMod 59723582981) ^ (45565 + 45565) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 45565 * (2 : ZMod 59723582981) ^ 45565 := by rw [pow_add]
          _ = 48975729979 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 59723582981) ^ 182261 = 51694756333 := by
        calc
          (2 : ZMod 59723582981) ^ 182261 = (2 : ZMod 59723582981) ^ (91130 + 91130 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 91130 * (2 : ZMod 59723582981) ^ 91130) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 51694756333 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 59723582981) ^ 364523 = 6770564171 := by
        calc
          (2 : ZMod 59723582981) ^ 364523 = (2 : ZMod 59723582981) ^ (182261 + 182261 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 182261 * (2 : ZMod 59723582981) ^ 182261) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 6770564171 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 59723582981) ^ 729047 = 44433897546 := by
        calc
          (2 : ZMod 59723582981) ^ 729047 = (2 : ZMod 59723582981) ^ (364523 + 364523 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 364523 * (2 : ZMod 59723582981) ^ 364523) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 44433897546 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 59723582981) ^ 1458095 = 40685089487 := by
        calc
          (2 : ZMod 59723582981) ^ 1458095 = (2 : ZMod 59723582981) ^ (729047 + 729047 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 729047 * (2 : ZMod 59723582981) ^ 729047) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 40685089487 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 59723582981) ^ 2916190 = 23721335660 := by
        calc
          (2 : ZMod 59723582981) ^ 2916190 = (2 : ZMod 59723582981) ^ (1458095 + 1458095) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1458095 * (2 : ZMod 59723582981) ^ 1458095 := by rw [pow_add]
          _ = 23721335660 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 59723582981) ^ 5832381 = 5732887526 := by
        calc
          (2 : ZMod 59723582981) ^ 5832381 = (2 : ZMod 59723582981) ^ (2916190 + 2916190 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 2916190 * (2 : ZMod 59723582981) ^ 2916190) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 5732887526 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 59723582981) ^ 11664762 = 47945509187 := by
        calc
          (2 : ZMod 59723582981) ^ 11664762 = (2 : ZMod 59723582981) ^ (5832381 + 5832381) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 5832381 * (2 : ZMod 59723582981) ^ 5832381 := by rw [pow_add]
          _ = 47945509187 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 59723582981) ^ 23329524 = 51199716666 := by
        calc
          (2 : ZMod 59723582981) ^ 23329524 = (2 : ZMod 59723582981) ^ (11664762 + 11664762) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 11664762 * (2 : ZMod 59723582981) ^ 11664762 := by rw [pow_add]
          _ = 51199716666 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 59723582981) ^ 46659049 = 59579959161 := by
        calc
          (2 : ZMod 59723582981) ^ 46659049 = (2 : ZMod 59723582981) ^ (23329524 + 23329524 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 23329524 * (2 : ZMod 59723582981) ^ 23329524) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 59579959161 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 59723582981) ^ 93318098 = 52516333753 := by
        calc
          (2 : ZMod 59723582981) ^ 93318098 = (2 : ZMod 59723582981) ^ (46659049 + 46659049) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 46659049 * (2 : ZMod 59723582981) ^ 46659049 := by rw [pow_add]
          _ = 52516333753 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 59723582981) ^ 186636196 = 26194157890 := by
        calc
          (2 : ZMod 59723582981) ^ 186636196 = (2 : ZMod 59723582981) ^ (93318098 + 93318098) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 93318098 * (2 : ZMod 59723582981) ^ 93318098 := by rw [pow_add]
          _ = 26194157890 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 59723582981) ^ 373272393 = 16396893644 := by
        calc
          (2 : ZMod 59723582981) ^ 373272393 = (2 : ZMod 59723582981) ^ (186636196 + 186636196 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 186636196 * (2 : ZMod 59723582981) ^ 186636196) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 16396893644 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 59723582981) ^ 746544787 = 3126732031 := by
        calc
          (2 : ZMod 59723582981) ^ 746544787 = (2 : ZMod 59723582981) ^ (373272393 + 373272393 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 373272393 * (2 : ZMod 59723582981) ^ 373272393) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 3126732031 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 59723582981) ^ 1493089574 = 23411347360 := by
        calc
          (2 : ZMod 59723582981) ^ 1493089574 = (2 : ZMod 59723582981) ^ (746544787 + 746544787) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 746544787 * (2 : ZMod 59723582981) ^ 746544787 := by rw [pow_add]
          _ = 23411347360 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 59723582981) ^ 2986179149 = 3135143907 := by
        calc
          (2 : ZMod 59723582981) ^ 2986179149 = (2 : ZMod 59723582981) ^ (1493089574 + 1493089574 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 1493089574 * (2 : ZMod 59723582981) ^ 1493089574) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 3135143907 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 59723582981) ^ 5972358298 = 37465349383 := by
        calc
          (2 : ZMod 59723582981) ^ 5972358298 = (2 : ZMod 59723582981) ^ (2986179149 + 2986179149) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 2986179149 * (2 : ZMod 59723582981) ^ 2986179149 := by rw [pow_add]
          _ = 37465349383 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 59723582981) ^ 11944716596 = 26696797265 := by
        calc
          (2 : ZMod 59723582981) ^ 11944716596 = (2 : ZMod 59723582981) ^ (5972358298 + 5972358298) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 5972358298 * (2 : ZMod 59723582981) ^ 5972358298 := by rw [pow_add]
          _ = 26696797265 := by rw [factor_1_32]; decide
      change (2 : ZMod 59723582981) ^ 11944716596 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (2 : ZMod 59723582981) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 59723582981) ^ 3 = 8 := by
        calc
          (2 : ZMod 59723582981) ^ 3 = (2 : ZMod 59723582981) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 1 * (2 : ZMod 59723582981) ^ 1) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 59723582981) ^ 6 = 64 := by
        calc
          (2 : ZMod 59723582981) ^ 6 = (2 : ZMod 59723582981) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3 * (2 : ZMod 59723582981) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 59723582981) ^ 13 = 8192 := by
        calc
          (2 : ZMod 59723582981) ^ 13 = (2 : ZMod 59723582981) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 6 * (2 : ZMod 59723582981) ^ 6) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 59723582981) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 59723582981) ^ 26 = (2 : ZMod 59723582981) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 13 * (2 : ZMod 59723582981) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 59723582981) ^ 52 = 23405522229 := by
        calc
          (2 : ZMod 59723582981) ^ 52 = (2 : ZMod 59723582981) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 26 * (2 : ZMod 59723582981) ^ 26 := by rw [pow_add]
          _ = 23405522229 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 59723582981) ^ 104 = 56387254022 := by
        calc
          (2 : ZMod 59723582981) ^ 104 = (2 : ZMod 59723582981) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 52 * (2 : ZMod 59723582981) ^ 52 := by rw [pow_add]
          _ = 56387254022 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 59723582981) ^ 209 = 30062323161 := by
        calc
          (2 : ZMod 59723582981) ^ 209 = (2 : ZMod 59723582981) ^ (104 + 104 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 104 * (2 : ZMod 59723582981) ^ 104) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 30062323161 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 59723582981) ^ 418 = 32220606848 := by
        calc
          (2 : ZMod 59723582981) ^ 418 = (2 : ZMod 59723582981) ^ (209 + 209) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 209 * (2 : ZMod 59723582981) ^ 209 := by rw [pow_add]
          _ = 32220606848 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 59723582981) ^ 837 = 39732475475 := by
        calc
          (2 : ZMod 59723582981) ^ 837 = (2 : ZMod 59723582981) ^ (418 + 418 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 418 * (2 : ZMod 59723582981) ^ 418) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 39732475475 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 59723582981) ^ 1675 = 24540139265 := by
        calc
          (2 : ZMod 59723582981) ^ 1675 = (2 : ZMod 59723582981) ^ (837 + 837 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 837 * (2 : ZMod 59723582981) ^ 837) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 24540139265 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 59723582981) ^ 3350 = 50803540836 := by
        calc
          (2 : ZMod 59723582981) ^ 3350 = (2 : ZMod 59723582981) ^ (1675 + 1675) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1675 * (2 : ZMod 59723582981) ^ 1675 := by rw [pow_add]
          _ = 50803540836 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 59723582981) ^ 6700 = 52278526947 := by
        calc
          (2 : ZMod 59723582981) ^ 6700 = (2 : ZMod 59723582981) ^ (3350 + 3350) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3350 * (2 : ZMod 59723582981) ^ 3350 := by rw [pow_add]
          _ = 52278526947 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 59723582981) ^ 13401 = 53663778799 := by
        calc
          (2 : ZMod 59723582981) ^ 13401 = (2 : ZMod 59723582981) ^ (6700 + 6700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 6700 * (2 : ZMod 59723582981) ^ 6700) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 53663778799 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 59723582981) ^ 26803 = 38631238863 := by
        calc
          (2 : ZMod 59723582981) ^ 26803 = (2 : ZMod 59723582981) ^ (13401 + 13401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 13401 * (2 : ZMod 59723582981) ^ 13401) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 38631238863 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 59723582981) ^ 53606 = 6098241141 := by
        calc
          (2 : ZMod 59723582981) ^ 53606 = (2 : ZMod 59723582981) ^ (26803 + 26803) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 26803 * (2 : ZMod 59723582981) ^ 26803 := by rw [pow_add]
          _ = 6098241141 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 59723582981) ^ 107212 = 55156434713 := by
        calc
          (2 : ZMod 59723582981) ^ 107212 = (2 : ZMod 59723582981) ^ (53606 + 53606) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 53606 * (2 : ZMod 59723582981) ^ 53606 := by rw [pow_add]
          _ = 55156434713 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 59723582981) ^ 214425 = 26935972658 := by
        calc
          (2 : ZMod 59723582981) ^ 214425 = (2 : ZMod 59723582981) ^ (107212 + 107212 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 107212 * (2 : ZMod 59723582981) ^ 107212) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 26935972658 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 59723582981) ^ 428851 = 46113009924 := by
        calc
          (2 : ZMod 59723582981) ^ 428851 = (2 : ZMod 59723582981) ^ (214425 + 214425 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 214425 * (2 : ZMod 59723582981) ^ 214425) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 46113009924 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 59723582981) ^ 857703 = 55188123473 := by
        calc
          (2 : ZMod 59723582981) ^ 857703 = (2 : ZMod 59723582981) ^ (428851 + 428851 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 428851 * (2 : ZMod 59723582981) ^ 428851) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 55188123473 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 59723582981) ^ 1715406 = 53247754186 := by
        calc
          (2 : ZMod 59723582981) ^ 1715406 = (2 : ZMod 59723582981) ^ (857703 + 857703) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 857703 * (2 : ZMod 59723582981) ^ 857703 := by rw [pow_add]
          _ = 53247754186 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 59723582981) ^ 3430812 = 18846108654 := by
        calc
          (2 : ZMod 59723582981) ^ 3430812 = (2 : ZMod 59723582981) ^ (1715406 + 1715406) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1715406 * (2 : ZMod 59723582981) ^ 1715406 := by rw [pow_add]
          _ = 18846108654 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 59723582981) ^ 6861624 = 12480372632 := by
        calc
          (2 : ZMod 59723582981) ^ 6861624 = (2 : ZMod 59723582981) ^ (3430812 + 3430812) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 3430812 * (2 : ZMod 59723582981) ^ 3430812 := by rw [pow_add]
          _ = 12480372632 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 59723582981) ^ 13723249 = 20788837449 := by
        calc
          (2 : ZMod 59723582981) ^ 13723249 = (2 : ZMod 59723582981) ^ (6861624 + 6861624 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 6861624 * (2 : ZMod 59723582981) ^ 6861624) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 20788837449 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 59723582981) ^ 27446499 = 48088194993 := by
        calc
          (2 : ZMod 59723582981) ^ 27446499 = (2 : ZMod 59723582981) ^ (13723249 + 13723249 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 13723249 * (2 : ZMod 59723582981) ^ 13723249) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 48088194993 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 59723582981) ^ 54892999 = 35734470022 := by
        calc
          (2 : ZMod 59723582981) ^ 54892999 = (2 : ZMod 59723582981) ^ (27446499 + 27446499 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 27446499 * (2 : ZMod 59723582981) ^ 27446499) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 35734470022 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 59723582981) ^ 109785998 = 36873290364 := by
        calc
          (2 : ZMod 59723582981) ^ 109785998 = (2 : ZMod 59723582981) ^ (54892999 + 54892999) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 54892999 * (2 : ZMod 59723582981) ^ 54892999 := by rw [pow_add]
          _ = 36873290364 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 59723582981) ^ 219571996 = 43124319613 := by
        calc
          (2 : ZMod 59723582981) ^ 219571996 = (2 : ZMod 59723582981) ^ (109785998 + 109785998) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 109785998 * (2 : ZMod 59723582981) ^ 109785998 := by rw [pow_add]
          _ = 43124319613 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 59723582981) ^ 439143992 = 13453139105 := by
        calc
          (2 : ZMod 59723582981) ^ 439143992 = (2 : ZMod 59723582981) ^ (219571996 + 219571996) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 219571996 * (2 : ZMod 59723582981) ^ 219571996 := by rw [pow_add]
          _ = 13453139105 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 59723582981) ^ 878287985 = 34216917560 := by
        calc
          (2 : ZMod 59723582981) ^ 878287985 = (2 : ZMod 59723582981) ^ (439143992 + 439143992 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 439143992 * (2 : ZMod 59723582981) ^ 439143992) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 34216917560 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 59723582981) ^ 1756575970 = 21028694304 := by
        calc
          (2 : ZMod 59723582981) ^ 1756575970 = (2 : ZMod 59723582981) ^ (878287985 + 878287985) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 878287985 * (2 : ZMod 59723582981) ^ 878287985 := by rw [pow_add]
          _ = 21028694304 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 59723582981) ^ 3513151940 = 43507650151 := by
        calc
          (2 : ZMod 59723582981) ^ 3513151940 = (2 : ZMod 59723582981) ^ (1756575970 + 1756575970) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1756575970 * (2 : ZMod 59723582981) ^ 1756575970 := by rw [pow_add]
          _ = 43507650151 := by rw [factor_2_30]; decide
      change (2 : ZMod 59723582981) ^ 3513151940 ≠ 1
      rw [factor_2_31]
      decide
    ·
      have factor_3_0 : (2 : ZMod 59723582981) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 59723582981) ^ 2 = 4 := by
        calc
          (2 : ZMod 59723582981) ^ 2 = (2 : ZMod 59723582981) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 1 * (2 : ZMod 59723582981) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 59723582981) ^ 5 = 32 := by
        calc
          (2 : ZMod 59723582981) ^ 5 = (2 : ZMod 59723582981) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 2 * (2 : ZMod 59723582981) ^ 2) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 59723582981) ^ 10 = 1024 := by
        calc
          (2 : ZMod 59723582981) ^ 10 = (2 : ZMod 59723582981) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 5 * (2 : ZMod 59723582981) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 59723582981) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 59723582981) ^ 21 = (2 : ZMod 59723582981) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 10 * (2 : ZMod 59723582981) ^ 10) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 59723582981) ^ 42 = 38224953491 := by
        calc
          (2 : ZMod 59723582981) ^ 42 = (2 : ZMod 59723582981) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 21 * (2 : ZMod 59723582981) ^ 21 := by rw [pow_add]
          _ = 38224953491 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 59723582981) ^ 85 = 49347747768 := by
        calc
          (2 : ZMod 59723582981) ^ 85 = (2 : ZMod 59723582981) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = ((2 : ZMod 59723582981) ^ 42 * (2 : ZMod 59723582981) ^ 42) * (2 : ZMod 59723582981) := by rw [pow_succ, pow_add]
          _ = 49347747768 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 59723582981) ^ 170 = 50083653151 := by
        calc
          (2 : ZMod 59723582981) ^ 170 = (2 : ZMod 59723582981) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 85 * (2 : ZMod 59723582981) ^ 85 := by rw [pow_add]
          _ = 50083653151 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 59723582981) ^ 340 = 21436606614 := by
        calc
          (2 : ZMod 59723582981) ^ 340 = (2 : ZMod 59723582981) ^ (170 + 170) :=
            congrArg (fun n : ℕ => (2 : ZMod 59723582981) ^ n) (by norm_num)
          _ = (2 : ZMod 59723582981) ^ 170 * (2 : ZMod 59723582981) ^ 170 := by rw [pow_add]
          _ = 21436606614 := by rw [factor_3_7]; decide
      change (2 : ZMod 59723582981) ^ 340 ≠ 1
      rw [factor_3_8]
      decide

#print axioms prime_lucas_59723582981

end TotientTailPeriodKiller
end Erdos249257
