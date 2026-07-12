import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime271504657

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_48327828947 : Nat.Prime 48327828947 := by
  apply lucas_primality 48327828947 (2 : ZMod 48327828947)
  ·
      have fermat_0 : (2 : ZMod 48327828947) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 48327828947) ^ 2 = 4 := by
        calc
          (2 : ZMod 48327828947) ^ 2 = (2 : ZMod 48327828947) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1 * (2 : ZMod 48327828947) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 48327828947) ^ 5 = 32 := by
        calc
          (2 : ZMod 48327828947) ^ 5 = (2 : ZMod 48327828947) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 2 * (2 : ZMod 48327828947) ^ 2) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 48327828947) ^ 11 = 2048 := by
        calc
          (2 : ZMod 48327828947) ^ 11 = (2 : ZMod 48327828947) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 5 * (2 : ZMod 48327828947) ^ 5) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 48327828947) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 48327828947) ^ 22 = (2 : ZMod 48327828947) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 11 * (2 : ZMod 48327828947) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 48327828947) ^ 45 = 1712615416 := by
        calc
          (2 : ZMod 48327828947) ^ 45 = (2 : ZMod 48327828947) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 22 * (2 : ZMod 48327828947) ^ 22) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 1712615416 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 48327828947) ^ 90 = 6717489117 := by
        calc
          (2 : ZMod 48327828947) ^ 90 = (2 : ZMod 48327828947) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 45 * (2 : ZMod 48327828947) ^ 45 := by rw [pow_add]
          _ = 6717489117 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 48327828947) ^ 180 = 27571060212 := by
        calc
          (2 : ZMod 48327828947) ^ 180 = (2 : ZMod 48327828947) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 90 * (2 : ZMod 48327828947) ^ 90 := by rw [pow_add]
          _ = 27571060212 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 48327828947) ^ 360 = 27948440940 := by
        calc
          (2 : ZMod 48327828947) ^ 360 = (2 : ZMod 48327828947) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 180 * (2 : ZMod 48327828947) ^ 180 := by rw [pow_add]
          _ = 27948440940 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 48327828947) ^ 720 = 1026303897 := by
        calc
          (2 : ZMod 48327828947) ^ 720 = (2 : ZMod 48327828947) ^ (360 + 360) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 360 * (2 : ZMod 48327828947) ^ 360 := by rw [pow_add]
          _ = 1026303897 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 48327828947) ^ 1440 = 21486534726 := by
        calc
          (2 : ZMod 48327828947) ^ 1440 = (2 : ZMod 48327828947) ^ (720 + 720) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 720 * (2 : ZMod 48327828947) ^ 720 := by rw [pow_add]
          _ = 21486534726 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 48327828947) ^ 2880 = 38118452301 := by
        calc
          (2 : ZMod 48327828947) ^ 2880 = (2 : ZMod 48327828947) ^ (1440 + 1440) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1440 * (2 : ZMod 48327828947) ^ 1440 := by rw [pow_add]
          _ = 38118452301 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 48327828947) ^ 5761 = 24582502556 := by
        calc
          (2 : ZMod 48327828947) ^ 5761 = (2 : ZMod 48327828947) ^ (2880 + 2880 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 2880 * (2 : ZMod 48327828947) ^ 2880) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 24582502556 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 48327828947) ^ 11522 = 19769780306 := by
        calc
          (2 : ZMod 48327828947) ^ 11522 = (2 : ZMod 48327828947) ^ (5761 + 5761) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 5761 * (2 : ZMod 48327828947) ^ 5761 := by rw [pow_add]
          _ = 19769780306 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 48327828947) ^ 23044 = 11269412643 := by
        calc
          (2 : ZMod 48327828947) ^ 23044 = (2 : ZMod 48327828947) ^ (11522 + 11522) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 11522 * (2 : ZMod 48327828947) ^ 11522 := by rw [pow_add]
          _ = 11269412643 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 48327828947) ^ 46089 = 11449203983 := by
        calc
          (2 : ZMod 48327828947) ^ 46089 = (2 : ZMod 48327828947) ^ (23044 + 23044 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 23044 * (2 : ZMod 48327828947) ^ 23044) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 11449203983 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 48327828947) ^ 92178 = 11867171182 := by
        calc
          (2 : ZMod 48327828947) ^ 92178 = (2 : ZMod 48327828947) ^ (46089 + 46089) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 46089 * (2 : ZMod 48327828947) ^ 46089 := by rw [pow_add]
          _ = 11867171182 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 48327828947) ^ 184356 = 19658230075 := by
        calc
          (2 : ZMod 48327828947) ^ 184356 = (2 : ZMod 48327828947) ^ (92178 + 92178) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 92178 * (2 : ZMod 48327828947) ^ 92178 := by rw [pow_add]
          _ = 19658230075 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 48327828947) ^ 368712 = 33957435486 := by
        calc
          (2 : ZMod 48327828947) ^ 368712 = (2 : ZMod 48327828947) ^ (184356 + 184356) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 184356 * (2 : ZMod 48327828947) ^ 184356 := by rw [pow_add]
          _ = 33957435486 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 48327828947) ^ 737424 = 6781373877 := by
        calc
          (2 : ZMod 48327828947) ^ 737424 = (2 : ZMod 48327828947) ^ (368712 + 368712) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 368712 * (2 : ZMod 48327828947) ^ 368712 := by rw [pow_add]
          _ = 6781373877 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 48327828947) ^ 1474848 = 11608258464 := by
        calc
          (2 : ZMod 48327828947) ^ 1474848 = (2 : ZMod 48327828947) ^ (737424 + 737424) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 737424 * (2 : ZMod 48327828947) ^ 737424 := by rw [pow_add]
          _ = 11608258464 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 48327828947) ^ 2949696 = 10610033038 := by
        calc
          (2 : ZMod 48327828947) ^ 2949696 = (2 : ZMod 48327828947) ^ (1474848 + 1474848) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1474848 * (2 : ZMod 48327828947) ^ 1474848 := by rw [pow_add]
          _ = 10610033038 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 48327828947) ^ 5899393 = 11080440360 := by
        calc
          (2 : ZMod 48327828947) ^ 5899393 = (2 : ZMod 48327828947) ^ (2949696 + 2949696 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 2949696 * (2 : ZMod 48327828947) ^ 2949696) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 11080440360 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 48327828947) ^ 11798786 = 26306055912 := by
        calc
          (2 : ZMod 48327828947) ^ 11798786 = (2 : ZMod 48327828947) ^ (5899393 + 5899393) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 5899393 * (2 : ZMod 48327828947) ^ 5899393 := by rw [pow_add]
          _ = 26306055912 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 48327828947) ^ 23597572 = 19285854212 := by
        calc
          (2 : ZMod 48327828947) ^ 23597572 = (2 : ZMod 48327828947) ^ (11798786 + 11798786) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 11798786 * (2 : ZMod 48327828947) ^ 11798786 := by rw [pow_add]
          _ = 19285854212 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 48327828947) ^ 47195145 = 2941101583 := by
        calc
          (2 : ZMod 48327828947) ^ 47195145 = (2 : ZMod 48327828947) ^ (23597572 + 23597572 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 23597572 * (2 : ZMod 48327828947) ^ 23597572) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 2941101583 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 48327828947) ^ 94390290 = 29678219714 := by
        calc
          (2 : ZMod 48327828947) ^ 94390290 = (2 : ZMod 48327828947) ^ (47195145 + 47195145) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 47195145 * (2 : ZMod 48327828947) ^ 47195145 := by rw [pow_add]
          _ = 29678219714 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 48327828947) ^ 188780581 = 6316622305 := by
        calc
          (2 : ZMod 48327828947) ^ 188780581 = (2 : ZMod 48327828947) ^ (94390290 + 94390290 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 94390290 * (2 : ZMod 48327828947) ^ 94390290) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 6316622305 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 48327828947) ^ 377561163 = 43717472146 := by
        calc
          (2 : ZMod 48327828947) ^ 377561163 = (2 : ZMod 48327828947) ^ (188780581 + 188780581 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 188780581 * (2 : ZMod 48327828947) ^ 188780581) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 43717472146 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 48327828947) ^ 755122327 = 21267193246 := by
        calc
          (2 : ZMod 48327828947) ^ 755122327 = (2 : ZMod 48327828947) ^ (377561163 + 377561163 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 377561163 * (2 : ZMod 48327828947) ^ 377561163) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 21267193246 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 48327828947) ^ 1510244654 = 11168123772 := by
        calc
          (2 : ZMod 48327828947) ^ 1510244654 = (2 : ZMod 48327828947) ^ (755122327 + 755122327) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 755122327 * (2 : ZMod 48327828947) ^ 755122327 := by rw [pow_add]
          _ = 11168123772 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 48327828947) ^ 3020489309 = 44696472927 := by
        calc
          (2 : ZMod 48327828947) ^ 3020489309 = (2 : ZMod 48327828947) ^ (1510244654 + 1510244654 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 1510244654 * (2 : ZMod 48327828947) ^ 1510244654) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 44696472927 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 48327828947) ^ 6040978618 = 10901359989 := by
        calc
          (2 : ZMod 48327828947) ^ 6040978618 = (2 : ZMod 48327828947) ^ (3020489309 + 3020489309) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 3020489309 * (2 : ZMod 48327828947) ^ 3020489309 := by rw [pow_add]
          _ = 10901359989 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 48327828947) ^ 12081957236 = 10350710116 := by
        calc
          (2 : ZMod 48327828947) ^ 12081957236 = (2 : ZMod 48327828947) ^ (6040978618 + 6040978618) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 6040978618 * (2 : ZMod 48327828947) ^ 6040978618 := by rw [pow_add]
          _ = 10350710116 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 48327828947) ^ 24163914473 = 48327828946 := by
        calc
          (2 : ZMod 48327828947) ^ 24163914473 = (2 : ZMod 48327828947) ^ (12081957236 + 12081957236 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 12081957236 * (2 : ZMod 48327828947) ^ 12081957236) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 48327828946 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 48327828947) ^ 48327828946 = 1 := by
        calc
          (2 : ZMod 48327828947) ^ 48327828946 = (2 : ZMod 48327828947) ^ (24163914473 + 24163914473) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 24163914473 * (2 : ZMod 48327828947) ^ 24163914473 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (271504657, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (271504657, 1)] : List FactorBlock).map factorBlockValue).prod = 48327828947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_271504657) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 48327828947) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 48327828947) ^ 2 = 4 := by
        calc
          (2 : ZMod 48327828947) ^ 2 = (2 : ZMod 48327828947) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1 * (2 : ZMod 48327828947) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 48327828947) ^ 5 = 32 := by
        calc
          (2 : ZMod 48327828947) ^ 5 = (2 : ZMod 48327828947) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 2 * (2 : ZMod 48327828947) ^ 2) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 48327828947) ^ 11 = 2048 := by
        calc
          (2 : ZMod 48327828947) ^ 11 = (2 : ZMod 48327828947) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 5 * (2 : ZMod 48327828947) ^ 5) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 48327828947) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 48327828947) ^ 22 = (2 : ZMod 48327828947) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 11 * (2 : ZMod 48327828947) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 48327828947) ^ 45 = 1712615416 := by
        calc
          (2 : ZMod 48327828947) ^ 45 = (2 : ZMod 48327828947) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 22 * (2 : ZMod 48327828947) ^ 22) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 1712615416 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 48327828947) ^ 90 = 6717489117 := by
        calc
          (2 : ZMod 48327828947) ^ 90 = (2 : ZMod 48327828947) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 45 * (2 : ZMod 48327828947) ^ 45 := by rw [pow_add]
          _ = 6717489117 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 48327828947) ^ 180 = 27571060212 := by
        calc
          (2 : ZMod 48327828947) ^ 180 = (2 : ZMod 48327828947) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 90 * (2 : ZMod 48327828947) ^ 90 := by rw [pow_add]
          _ = 27571060212 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 48327828947) ^ 360 = 27948440940 := by
        calc
          (2 : ZMod 48327828947) ^ 360 = (2 : ZMod 48327828947) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 180 * (2 : ZMod 48327828947) ^ 180 := by rw [pow_add]
          _ = 27948440940 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 48327828947) ^ 720 = 1026303897 := by
        calc
          (2 : ZMod 48327828947) ^ 720 = (2 : ZMod 48327828947) ^ (360 + 360) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 360 * (2 : ZMod 48327828947) ^ 360 := by rw [pow_add]
          _ = 1026303897 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 48327828947) ^ 1440 = 21486534726 := by
        calc
          (2 : ZMod 48327828947) ^ 1440 = (2 : ZMod 48327828947) ^ (720 + 720) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 720 * (2 : ZMod 48327828947) ^ 720 := by rw [pow_add]
          _ = 21486534726 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 48327828947) ^ 2880 = 38118452301 := by
        calc
          (2 : ZMod 48327828947) ^ 2880 = (2 : ZMod 48327828947) ^ (1440 + 1440) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1440 * (2 : ZMod 48327828947) ^ 1440 := by rw [pow_add]
          _ = 38118452301 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 48327828947) ^ 5761 = 24582502556 := by
        calc
          (2 : ZMod 48327828947) ^ 5761 = (2 : ZMod 48327828947) ^ (2880 + 2880 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 2880 * (2 : ZMod 48327828947) ^ 2880) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 24582502556 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 48327828947) ^ 11522 = 19769780306 := by
        calc
          (2 : ZMod 48327828947) ^ 11522 = (2 : ZMod 48327828947) ^ (5761 + 5761) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 5761 * (2 : ZMod 48327828947) ^ 5761 := by rw [pow_add]
          _ = 19769780306 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 48327828947) ^ 23044 = 11269412643 := by
        calc
          (2 : ZMod 48327828947) ^ 23044 = (2 : ZMod 48327828947) ^ (11522 + 11522) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 11522 * (2 : ZMod 48327828947) ^ 11522 := by rw [pow_add]
          _ = 11269412643 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 48327828947) ^ 46089 = 11449203983 := by
        calc
          (2 : ZMod 48327828947) ^ 46089 = (2 : ZMod 48327828947) ^ (23044 + 23044 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 23044 * (2 : ZMod 48327828947) ^ 23044) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 11449203983 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 48327828947) ^ 92178 = 11867171182 := by
        calc
          (2 : ZMod 48327828947) ^ 92178 = (2 : ZMod 48327828947) ^ (46089 + 46089) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 46089 * (2 : ZMod 48327828947) ^ 46089 := by rw [pow_add]
          _ = 11867171182 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 48327828947) ^ 184356 = 19658230075 := by
        calc
          (2 : ZMod 48327828947) ^ 184356 = (2 : ZMod 48327828947) ^ (92178 + 92178) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 92178 * (2 : ZMod 48327828947) ^ 92178 := by rw [pow_add]
          _ = 19658230075 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 48327828947) ^ 368712 = 33957435486 := by
        calc
          (2 : ZMod 48327828947) ^ 368712 = (2 : ZMod 48327828947) ^ (184356 + 184356) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 184356 * (2 : ZMod 48327828947) ^ 184356 := by rw [pow_add]
          _ = 33957435486 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 48327828947) ^ 737424 = 6781373877 := by
        calc
          (2 : ZMod 48327828947) ^ 737424 = (2 : ZMod 48327828947) ^ (368712 + 368712) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 368712 * (2 : ZMod 48327828947) ^ 368712 := by rw [pow_add]
          _ = 6781373877 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 48327828947) ^ 1474848 = 11608258464 := by
        calc
          (2 : ZMod 48327828947) ^ 1474848 = (2 : ZMod 48327828947) ^ (737424 + 737424) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 737424 * (2 : ZMod 48327828947) ^ 737424 := by rw [pow_add]
          _ = 11608258464 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 48327828947) ^ 2949696 = 10610033038 := by
        calc
          (2 : ZMod 48327828947) ^ 2949696 = (2 : ZMod 48327828947) ^ (1474848 + 1474848) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1474848 * (2 : ZMod 48327828947) ^ 1474848 := by rw [pow_add]
          _ = 10610033038 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 48327828947) ^ 5899393 = 11080440360 := by
        calc
          (2 : ZMod 48327828947) ^ 5899393 = (2 : ZMod 48327828947) ^ (2949696 + 2949696 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 2949696 * (2 : ZMod 48327828947) ^ 2949696) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 11080440360 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 48327828947) ^ 11798786 = 26306055912 := by
        calc
          (2 : ZMod 48327828947) ^ 11798786 = (2 : ZMod 48327828947) ^ (5899393 + 5899393) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 5899393 * (2 : ZMod 48327828947) ^ 5899393 := by rw [pow_add]
          _ = 26306055912 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 48327828947) ^ 23597572 = 19285854212 := by
        calc
          (2 : ZMod 48327828947) ^ 23597572 = (2 : ZMod 48327828947) ^ (11798786 + 11798786) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 11798786 * (2 : ZMod 48327828947) ^ 11798786 := by rw [pow_add]
          _ = 19285854212 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 48327828947) ^ 47195145 = 2941101583 := by
        calc
          (2 : ZMod 48327828947) ^ 47195145 = (2 : ZMod 48327828947) ^ (23597572 + 23597572 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 23597572 * (2 : ZMod 48327828947) ^ 23597572) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 2941101583 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 48327828947) ^ 94390290 = 29678219714 := by
        calc
          (2 : ZMod 48327828947) ^ 94390290 = (2 : ZMod 48327828947) ^ (47195145 + 47195145) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 47195145 * (2 : ZMod 48327828947) ^ 47195145 := by rw [pow_add]
          _ = 29678219714 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 48327828947) ^ 188780581 = 6316622305 := by
        calc
          (2 : ZMod 48327828947) ^ 188780581 = (2 : ZMod 48327828947) ^ (94390290 + 94390290 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 94390290 * (2 : ZMod 48327828947) ^ 94390290) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 6316622305 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 48327828947) ^ 377561163 = 43717472146 := by
        calc
          (2 : ZMod 48327828947) ^ 377561163 = (2 : ZMod 48327828947) ^ (188780581 + 188780581 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 188780581 * (2 : ZMod 48327828947) ^ 188780581) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 43717472146 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 48327828947) ^ 755122327 = 21267193246 := by
        calc
          (2 : ZMod 48327828947) ^ 755122327 = (2 : ZMod 48327828947) ^ (377561163 + 377561163 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 377561163 * (2 : ZMod 48327828947) ^ 377561163) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 21267193246 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 48327828947) ^ 1510244654 = 11168123772 := by
        calc
          (2 : ZMod 48327828947) ^ 1510244654 = (2 : ZMod 48327828947) ^ (755122327 + 755122327) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 755122327 * (2 : ZMod 48327828947) ^ 755122327 := by rw [pow_add]
          _ = 11168123772 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 48327828947) ^ 3020489309 = 44696472927 := by
        calc
          (2 : ZMod 48327828947) ^ 3020489309 = (2 : ZMod 48327828947) ^ (1510244654 + 1510244654 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 1510244654 * (2 : ZMod 48327828947) ^ 1510244654) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 44696472927 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 48327828947) ^ 6040978618 = 10901359989 := by
        calc
          (2 : ZMod 48327828947) ^ 6040978618 = (2 : ZMod 48327828947) ^ (3020489309 + 3020489309) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 3020489309 * (2 : ZMod 48327828947) ^ 3020489309 := by rw [pow_add]
          _ = 10901359989 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 48327828947) ^ 12081957236 = 10350710116 := by
        calc
          (2 : ZMod 48327828947) ^ 12081957236 = (2 : ZMod 48327828947) ^ (6040978618 + 6040978618) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 6040978618 * (2 : ZMod 48327828947) ^ 6040978618 := by rw [pow_add]
          _ = 10350710116 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 48327828947) ^ 24163914473 = 48327828946 := by
        calc
          (2 : ZMod 48327828947) ^ 24163914473 = (2 : ZMod 48327828947) ^ (12081957236 + 12081957236 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 12081957236 * (2 : ZMod 48327828947) ^ 12081957236) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 48327828946 := by rw [factor_0_33]; decide
      change (2 : ZMod 48327828947) ^ 24163914473 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (2 : ZMod 48327828947) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 48327828947) ^ 2 = 4 := by
        calc
          (2 : ZMod 48327828947) ^ 2 = (2 : ZMod 48327828947) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1 * (2 : ZMod 48327828947) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 48327828947) ^ 4 = 16 := by
        calc
          (2 : ZMod 48327828947) ^ 4 = (2 : ZMod 48327828947) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 2 * (2 : ZMod 48327828947) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 48327828947) ^ 8 = 256 := by
        calc
          (2 : ZMod 48327828947) ^ 8 = (2 : ZMod 48327828947) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 4 * (2 : ZMod 48327828947) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 48327828947) ^ 16 = 65536 := by
        calc
          (2 : ZMod 48327828947) ^ 16 = (2 : ZMod 48327828947) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 8 * (2 : ZMod 48327828947) ^ 8 := by rw [pow_add]
          _ = 65536 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 48327828947) ^ 32 = 4294967296 := by
        calc
          (2 : ZMod 48327828947) ^ 32 = (2 : ZMod 48327828947) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 16 * (2 : ZMod 48327828947) ^ 16 := by rw [pow_add]
          _ = 4294967296 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 48327828947) ^ 64 = 20977217495 := by
        calc
          (2 : ZMod 48327828947) ^ 64 = (2 : ZMod 48327828947) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 32 * (2 : ZMod 48327828947) ^ 32 := by rw [pow_add]
          _ = 20977217495 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 48327828947) ^ 129 = 32837252040 := by
        calc
          (2 : ZMod 48327828947) ^ 129 = (2 : ZMod 48327828947) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 64 * (2 : ZMod 48327828947) ^ 64) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 32837252040 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 48327828947) ^ 258 = 1546567818 := by
        calc
          (2 : ZMod 48327828947) ^ 258 = (2 : ZMod 48327828947) ^ (129 + 129) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 129 * (2 : ZMod 48327828947) ^ 129 := by rw [pow_add]
          _ = 1546567818 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 48327828947) ^ 517 = 12940859459 := by
        calc
          (2 : ZMod 48327828947) ^ 517 = (2 : ZMod 48327828947) ^ (258 + 258 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 258 * (2 : ZMod 48327828947) ^ 258) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 12940859459 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 48327828947) ^ 1035 = 36321078131 := by
        calc
          (2 : ZMod 48327828947) ^ 1035 = (2 : ZMod 48327828947) ^ (517 + 517 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 517 * (2 : ZMod 48327828947) ^ 517) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 36321078131 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 48327828947) ^ 2071 = 43382978757 := by
        calc
          (2 : ZMod 48327828947) ^ 2071 = (2 : ZMod 48327828947) ^ (1035 + 1035 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 1035 * (2 : ZMod 48327828947) ^ 1035) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 43382978757 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 48327828947) ^ 4142 = 6397663013 := by
        calc
          (2 : ZMod 48327828947) ^ 4142 = (2 : ZMod 48327828947) ^ (2071 + 2071) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 2071 * (2 : ZMod 48327828947) ^ 2071 := by rw [pow_add]
          _ = 6397663013 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 48327828947) ^ 8285 = 40966448084 := by
        calc
          (2 : ZMod 48327828947) ^ 8285 = (2 : ZMod 48327828947) ^ (4142 + 4142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 4142 * (2 : ZMod 48327828947) ^ 4142) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 40966448084 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 48327828947) ^ 16571 = 28616995894 := by
        calc
          (2 : ZMod 48327828947) ^ 16571 = (2 : ZMod 48327828947) ^ (8285 + 8285 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 8285 * (2 : ZMod 48327828947) ^ 8285) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 28616995894 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 48327828947) ^ 33142 = 29577268141 := by
        calc
          (2 : ZMod 48327828947) ^ 33142 = (2 : ZMod 48327828947) ^ (16571 + 16571) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 16571 * (2 : ZMod 48327828947) ^ 16571 := by rw [pow_add]
          _ = 29577268141 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 48327828947) ^ 66285 = 33868888597 := by
        calc
          (2 : ZMod 48327828947) ^ 66285 = (2 : ZMod 48327828947) ^ (33142 + 33142 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 33142 * (2 : ZMod 48327828947) ^ 33142) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 33868888597 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 48327828947) ^ 132570 = 39225753667 := by
        calc
          (2 : ZMod 48327828947) ^ 132570 = (2 : ZMod 48327828947) ^ (66285 + 66285) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 66285 * (2 : ZMod 48327828947) ^ 66285 := by rw [pow_add]
          _ = 39225753667 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 48327828947) ^ 265141 = 31025407831 := by
        calc
          (2 : ZMod 48327828947) ^ 265141 = (2 : ZMod 48327828947) ^ (132570 + 132570 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 132570 * (2 : ZMod 48327828947) ^ 132570) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 31025407831 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 48327828947) ^ 530282 = 3384989125 := by
        calc
          (2 : ZMod 48327828947) ^ 530282 = (2 : ZMod 48327828947) ^ (265141 + 265141) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 265141 * (2 : ZMod 48327828947) ^ 265141 := by rw [pow_add]
          _ = 3384989125 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 48327828947) ^ 1060565 = 35217217609 := by
        calc
          (2 : ZMod 48327828947) ^ 1060565 = (2 : ZMod 48327828947) ^ (530282 + 530282 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 530282 * (2 : ZMod 48327828947) ^ 530282) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 35217217609 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 48327828947) ^ 2121130 = 38515964890 := by
        calc
          (2 : ZMod 48327828947) ^ 2121130 = (2 : ZMod 48327828947) ^ (1060565 + 1060565) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1060565 * (2 : ZMod 48327828947) ^ 1060565 := by rw [pow_add]
          _ = 38515964890 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 48327828947) ^ 4242260 = 40319461216 := by
        calc
          (2 : ZMod 48327828947) ^ 4242260 = (2 : ZMod 48327828947) ^ (2121130 + 2121130) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 2121130 * (2 : ZMod 48327828947) ^ 2121130 := by rw [pow_add]
          _ = 40319461216 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 48327828947) ^ 8484520 = 47028702762 := by
        calc
          (2 : ZMod 48327828947) ^ 8484520 = (2 : ZMod 48327828947) ^ (4242260 + 4242260) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 4242260 * (2 : ZMod 48327828947) ^ 4242260 := by rw [pow_add]
          _ = 47028702762 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 48327828947) ^ 16969041 = 41351632927 := by
        calc
          (2 : ZMod 48327828947) ^ 16969041 = (2 : ZMod 48327828947) ^ (8484520 + 8484520 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 8484520 * (2 : ZMod 48327828947) ^ 8484520) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 41351632927 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 48327828947) ^ 33938082 = 35044586292 := by
        calc
          (2 : ZMod 48327828947) ^ 33938082 = (2 : ZMod 48327828947) ^ (16969041 + 16969041) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 16969041 * (2 : ZMod 48327828947) ^ 16969041 := by rw [pow_add]
          _ = 35044586292 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 48327828947) ^ 67876164 = 10859709377 := by
        calc
          (2 : ZMod 48327828947) ^ 67876164 = (2 : ZMod 48327828947) ^ (33938082 + 33938082) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 33938082 * (2 : ZMod 48327828947) ^ 33938082 := by rw [pow_add]
          _ = 10859709377 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 48327828947) ^ 135752328 = 5077422274 := by
        calc
          (2 : ZMod 48327828947) ^ 135752328 = (2 : ZMod 48327828947) ^ (67876164 + 67876164) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 67876164 * (2 : ZMod 48327828947) ^ 67876164 := by rw [pow_add]
          _ = 5077422274 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 48327828947) ^ 271504657 = 15131713399 := by
        calc
          (2 : ZMod 48327828947) ^ 271504657 = (2 : ZMod 48327828947) ^ (135752328 + 135752328 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 135752328 * (2 : ZMod 48327828947) ^ 135752328) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 15131713399 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 48327828947) ^ 543009314 = 23437699957 := by
        calc
          (2 : ZMod 48327828947) ^ 543009314 = (2 : ZMod 48327828947) ^ (271504657 + 271504657) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 271504657 * (2 : ZMod 48327828947) ^ 271504657 := by rw [pow_add]
          _ = 23437699957 := by rw [factor_1_28]; decide
      change (2 : ZMod 48327828947) ^ 543009314 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (2 : ZMod 48327828947) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 48327828947) ^ 2 = 4 := by
        calc
          (2 : ZMod 48327828947) ^ 2 = (2 : ZMod 48327828947) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 1 * (2 : ZMod 48327828947) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 48327828947) ^ 5 = 32 := by
        calc
          (2 : ZMod 48327828947) ^ 5 = (2 : ZMod 48327828947) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 2 * (2 : ZMod 48327828947) ^ 2) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 48327828947) ^ 11 = 2048 := by
        calc
          (2 : ZMod 48327828947) ^ 11 = (2 : ZMod 48327828947) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 5 * (2 : ZMod 48327828947) ^ 5) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 48327828947) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 48327828947) ^ 22 = (2 : ZMod 48327828947) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 11 * (2 : ZMod 48327828947) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 48327828947) ^ 44 = 856307708 := by
        calc
          (2 : ZMod 48327828947) ^ 44 = (2 : ZMod 48327828947) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 22 * (2 : ZMod 48327828947) ^ 22 := by rw [pow_add]
          _ = 856307708 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 48327828947) ^ 89 = 27522659032 := by
        calc
          (2 : ZMod 48327828947) ^ 89 = (2 : ZMod 48327828947) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = ((2 : ZMod 48327828947) ^ 44 * (2 : ZMod 48327828947) ^ 44) * (2 : ZMod 48327828947) := by rw [pow_succ, pow_add]
          _ = 27522659032 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 48327828947) ^ 178 = 6892765053 := by
        calc
          (2 : ZMod 48327828947) ^ 178 = (2 : ZMod 48327828947) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (2 : ZMod 48327828947) ^ n) (by norm_num)
          _ = (2 : ZMod 48327828947) ^ 89 * (2 : ZMod 48327828947) ^ 89 := by rw [pow_add]
          _ = 6892765053 := by rw [factor_2_6]; decide
      change (2 : ZMod 48327828947) ^ 178 ≠ 1
      rw [factor_2_7]
      decide

#print axioms prime_lucas_48327828947

end TotientTailPeriodKiller
end Erdos249257
