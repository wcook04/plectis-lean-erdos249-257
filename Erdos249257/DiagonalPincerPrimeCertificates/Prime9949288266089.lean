import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1243661033261

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_9949288266089 : Nat.Prime 9949288266089 := by
  apply lucas_primality 9949288266089 (3 : ZMod 9949288266089)
  ·
      have fermat_0 : (3 : ZMod 9949288266089) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 9949288266089) ^ 2 = 9 := by
        calc
          (3 : ZMod 9949288266089) ^ 2 = (3 : ZMod 9949288266089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 1 * (3 : ZMod 9949288266089) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 9949288266089) ^ 4 = 81 := by
        calc
          (3 : ZMod 9949288266089) ^ 4 = (3 : ZMod 9949288266089) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2 * (3 : ZMod 9949288266089) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 9949288266089) ^ 9 = 19683 := by
        calc
          (3 : ZMod 9949288266089) ^ 9 = (3 : ZMod 9949288266089) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 4 * (3 : ZMod 9949288266089) ^ 4) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 9949288266089) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 9949288266089) ^ 18 = (3 : ZMod 9949288266089) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 9 * (3 : ZMod 9949288266089) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 9949288266089) ^ 36 = 9621803046556 := by
        calc
          (3 : ZMod 9949288266089) ^ 36 = (3 : ZMod 9949288266089) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 18 * (3 : ZMod 9949288266089) ^ 18 := by rw [pow_add]
          _ = 9621803046556 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 9949288266089) ^ 72 = 5910497665344 := by
        calc
          (3 : ZMod 9949288266089) ^ 72 = (3 : ZMod 9949288266089) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 36 * (3 : ZMod 9949288266089) ^ 36 := by rw [pow_add]
          _ = 5910497665344 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 9949288266089) ^ 144 = 923861996951 := by
        calc
          (3 : ZMod 9949288266089) ^ 144 = (3 : ZMod 9949288266089) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 72 * (3 : ZMod 9949288266089) ^ 72 := by rw [pow_add]
          _ = 923861996951 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 9949288266089) ^ 289 = 2429758477157 := by
        calc
          (3 : ZMod 9949288266089) ^ 289 = (3 : ZMod 9949288266089) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 144 * (3 : ZMod 9949288266089) ^ 144) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 2429758477157 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 9949288266089) ^ 579 = 1640057992893 := by
        calc
          (3 : ZMod 9949288266089) ^ 579 = (3 : ZMod 9949288266089) ^ (289 + 289 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 289 * (3 : ZMod 9949288266089) ^ 289) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 1640057992893 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 9949288266089) ^ 1158 = 4927128215160 := by
        calc
          (3 : ZMod 9949288266089) ^ 1158 = (3 : ZMod 9949288266089) ^ (579 + 579) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 579 * (3 : ZMod 9949288266089) ^ 579 := by rw [pow_add]
          _ = 4927128215160 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 9949288266089) ^ 2316 = 3132510137059 := by
        calc
          (3 : ZMod 9949288266089) ^ 2316 = (3 : ZMod 9949288266089) ^ (1158 + 1158) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 1158 * (3 : ZMod 9949288266089) ^ 1158 := by rw [pow_add]
          _ = 3132510137059 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 9949288266089) ^ 4632 = 9675198271010 := by
        calc
          (3 : ZMod 9949288266089) ^ 4632 = (3 : ZMod 9949288266089) ^ (2316 + 2316) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2316 * (3 : ZMod 9949288266089) ^ 2316 := by rw [pow_add]
          _ = 9675198271010 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 9949288266089) ^ 9265 = 1626368109808 := by
        calc
          (3 : ZMod 9949288266089) ^ 9265 = (3 : ZMod 9949288266089) ^ (4632 + 4632 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 4632 * (3 : ZMod 9949288266089) ^ 4632) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 1626368109808 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 9949288266089) ^ 18531 = 9854881287733 := by
        calc
          (3 : ZMod 9949288266089) ^ 18531 = (3 : ZMod 9949288266089) ^ (9265 + 9265 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 9265 * (3 : ZMod 9949288266089) ^ 9265) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 9854881287733 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 9949288266089) ^ 37063 = 8205143766908 := by
        calc
          (3 : ZMod 9949288266089) ^ 37063 = (3 : ZMod 9949288266089) ^ (18531 + 18531 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 18531 * (3 : ZMod 9949288266089) ^ 18531) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8205143766908 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 9949288266089) ^ 74127 = 446608408257 := by
        calc
          (3 : ZMod 9949288266089) ^ 74127 = (3 : ZMod 9949288266089) ^ (37063 + 37063 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 37063 * (3 : ZMod 9949288266089) ^ 37063) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 446608408257 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 9949288266089) ^ 148255 = 9185211434321 := by
        calc
          (3 : ZMod 9949288266089) ^ 148255 = (3 : ZMod 9949288266089) ^ (74127 + 74127 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 74127 * (3 : ZMod 9949288266089) ^ 74127) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 9185211434321 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 9949288266089) ^ 296511 = 25412572688 := by
        calc
          (3 : ZMod 9949288266089) ^ 296511 = (3 : ZMod 9949288266089) ^ (148255 + 148255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 148255 * (3 : ZMod 9949288266089) ^ 148255) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 25412572688 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 9949288266089) ^ 593023 = 3284698019682 := by
        calc
          (3 : ZMod 9949288266089) ^ 593023 = (3 : ZMod 9949288266089) ^ (296511 + 296511 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 296511 * (3 : ZMod 9949288266089) ^ 296511) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 3284698019682 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 9949288266089) ^ 1186047 = 3468184915024 := by
        calc
          (3 : ZMod 9949288266089) ^ 1186047 = (3 : ZMod 9949288266089) ^ (593023 + 593023 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 593023 * (3 : ZMod 9949288266089) ^ 593023) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 3468184915024 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 9949288266089) ^ 2372095 = 836006153659 := by
        calc
          (3 : ZMod 9949288266089) ^ 2372095 = (3 : ZMod 9949288266089) ^ (1186047 + 1186047 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 1186047 * (3 : ZMod 9949288266089) ^ 1186047) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 836006153659 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 9949288266089) ^ 4744190 = 6044916366668 := by
        calc
          (3 : ZMod 9949288266089) ^ 4744190 = (3 : ZMod 9949288266089) ^ (2372095 + 2372095) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2372095 * (3 : ZMod 9949288266089) ^ 2372095 := by rw [pow_add]
          _ = 6044916366668 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 9949288266089) ^ 9488380 = 4797581795991 := by
        calc
          (3 : ZMod 9949288266089) ^ 9488380 = (3 : ZMod 9949288266089) ^ (4744190 + 4744190) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 4744190 * (3 : ZMod 9949288266089) ^ 4744190 := by rw [pow_add]
          _ = 4797581795991 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 9949288266089) ^ 18976761 = 1285018325033 := by
        calc
          (3 : ZMod 9949288266089) ^ 18976761 = (3 : ZMod 9949288266089) ^ (9488380 + 9488380 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 9488380 * (3 : ZMod 9949288266089) ^ 9488380) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 1285018325033 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 9949288266089) ^ 37953522 = 4350917379615 := by
        calc
          (3 : ZMod 9949288266089) ^ 37953522 = (3 : ZMod 9949288266089) ^ (18976761 + 18976761) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 18976761 * (3 : ZMod 9949288266089) ^ 18976761 := by rw [pow_add]
          _ = 4350917379615 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 9949288266089) ^ 75907045 = 5079533876613 := by
        calc
          (3 : ZMod 9949288266089) ^ 75907045 = (3 : ZMod 9949288266089) ^ (37953522 + 37953522 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 37953522 * (3 : ZMod 9949288266089) ^ 37953522) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 5079533876613 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 9949288266089) ^ 151814090 = 9110878426170 := by
        calc
          (3 : ZMod 9949288266089) ^ 151814090 = (3 : ZMod 9949288266089) ^ (75907045 + 75907045) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 75907045 * (3 : ZMod 9949288266089) ^ 75907045 := by rw [pow_add]
          _ = 9110878426170 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 9949288266089) ^ 303628181 = 5915580449653 := by
        calc
          (3 : ZMod 9949288266089) ^ 303628181 = (3 : ZMod 9949288266089) ^ (151814090 + 151814090 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 151814090 * (3 : ZMod 9949288266089) ^ 151814090) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 5915580449653 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 9949288266089) ^ 607256363 = 8863517563899 := by
        calc
          (3 : ZMod 9949288266089) ^ 607256363 = (3 : ZMod 9949288266089) ^ (303628181 + 303628181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 303628181 * (3 : ZMod 9949288266089) ^ 303628181) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8863517563899 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 9949288266089) ^ 1214512727 = 6190807466011 := by
        calc
          (3 : ZMod 9949288266089) ^ 1214512727 = (3 : ZMod 9949288266089) ^ (607256363 + 607256363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 607256363 * (3 : ZMod 9949288266089) ^ 607256363) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 6190807466011 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 9949288266089) ^ 2429025455 = 9476800981300 := by
        calc
          (3 : ZMod 9949288266089) ^ 2429025455 = (3 : ZMod 9949288266089) ^ (1214512727 + 1214512727 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 1214512727 * (3 : ZMod 9949288266089) ^ 1214512727) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 9476800981300 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 9949288266089) ^ 4858050911 = 3352929101822 := by
        calc
          (3 : ZMod 9949288266089) ^ 4858050911 = (3 : ZMod 9949288266089) ^ (2429025455 + 2429025455 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 2429025455 * (3 : ZMod 9949288266089) ^ 2429025455) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 3352929101822 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 9949288266089) ^ 9716101822 = 6796114461776 := by
        calc
          (3 : ZMod 9949288266089) ^ 9716101822 = (3 : ZMod 9949288266089) ^ (4858050911 + 4858050911) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 4858050911 * (3 : ZMod 9949288266089) ^ 4858050911 := by rw [pow_add]
          _ = 6796114461776 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 9949288266089) ^ 19432203644 = 112123281126 := by
        calc
          (3 : ZMod 9949288266089) ^ 19432203644 = (3 : ZMod 9949288266089) ^ (9716101822 + 9716101822) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 9716101822 * (3 : ZMod 9949288266089) ^ 9716101822 := by rw [pow_add]
          _ = 112123281126 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 9949288266089) ^ 38864407289 = 499840753049 := by
        calc
          (3 : ZMod 9949288266089) ^ 38864407289 = (3 : ZMod 9949288266089) ^ (19432203644 + 19432203644 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 19432203644 * (3 : ZMod 9949288266089) ^ 19432203644) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 499840753049 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 9949288266089) ^ 77728814578 = 186680497088 := by
        calc
          (3 : ZMod 9949288266089) ^ 77728814578 = (3 : ZMod 9949288266089) ^ (38864407289 + 38864407289) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 38864407289 * (3 : ZMod 9949288266089) ^ 38864407289 := by rw [pow_add]
          _ = 186680497088 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 9949288266089) ^ 155457629157 = 8571934976437 := by
        calc
          (3 : ZMod 9949288266089) ^ 155457629157 = (3 : ZMod 9949288266089) ^ (77728814578 + 77728814578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 77728814578 * (3 : ZMod 9949288266089) ^ 77728814578) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8571934976437 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 9949288266089) ^ 310915258315 = 2454807314439 := by
        calc
          (3 : ZMod 9949288266089) ^ 310915258315 = (3 : ZMod 9949288266089) ^ (155457629157 + 155457629157 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 155457629157 * (3 : ZMod 9949288266089) ^ 155457629157) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 2454807314439 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 9949288266089) ^ 621830516630 = 9645775492681 := by
        calc
          (3 : ZMod 9949288266089) ^ 621830516630 = (3 : ZMod 9949288266089) ^ (310915258315 + 310915258315) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 310915258315 * (3 : ZMod 9949288266089) ^ 310915258315 := by rw [pow_add]
          _ = 9645775492681 := by rw [fermat_38]; decide
      have fermat_40 : (3 : ZMod 9949288266089) ^ 1243661033261 = 8888476366373 := by
        calc
          (3 : ZMod 9949288266089) ^ 1243661033261 = (3 : ZMod 9949288266089) ^ (621830516630 + 621830516630 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 621830516630 * (3 : ZMod 9949288266089) ^ 621830516630) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8888476366373 := by rw [fermat_39]; decide
      have fermat_41 : (3 : ZMod 9949288266089) ^ 2487322066522 = 261545440743 := by
        calc
          (3 : ZMod 9949288266089) ^ 2487322066522 = (3 : ZMod 9949288266089) ^ (1243661033261 + 1243661033261) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 1243661033261 * (3 : ZMod 9949288266089) ^ 1243661033261 := by rw [pow_add]
          _ = 261545440743 := by rw [fermat_40]; decide
      have fermat_42 : (3 : ZMod 9949288266089) ^ 4974644133044 = 9949288266088 := by
        calc
          (3 : ZMod 9949288266089) ^ 4974644133044 = (3 : ZMod 9949288266089) ^ (2487322066522 + 2487322066522) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2487322066522 * (3 : ZMod 9949288266089) ^ 2487322066522 := by rw [pow_add]
          _ = 9949288266088 := by rw [fermat_41]; decide
      have fermat_43 : (3 : ZMod 9949288266089) ^ 9949288266088 = 1 := by
        calc
          (3 : ZMod 9949288266089) ^ 9949288266088 = (3 : ZMod 9949288266089) ^ (4974644133044 + 4974644133044) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 4974644133044 * (3 : ZMod 9949288266089) ^ 4974644133044 := by rw [pow_add]
          _ = 1 := by rw [fermat_42]; decide
      simpa using fermat_43
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (1243661033261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (1243661033261, 1)] : List FactorBlock).map factorBlockValue).prod = 9949288266089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_1243661033261) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 9949288266089) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 9949288266089) ^ 2 = 9 := by
        calc
          (3 : ZMod 9949288266089) ^ 2 = (3 : ZMod 9949288266089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 1 * (3 : ZMod 9949288266089) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 9949288266089) ^ 4 = 81 := by
        calc
          (3 : ZMod 9949288266089) ^ 4 = (3 : ZMod 9949288266089) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2 * (3 : ZMod 9949288266089) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 9949288266089) ^ 9 = 19683 := by
        calc
          (3 : ZMod 9949288266089) ^ 9 = (3 : ZMod 9949288266089) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 4 * (3 : ZMod 9949288266089) ^ 4) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 9949288266089) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 9949288266089) ^ 18 = (3 : ZMod 9949288266089) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 9 * (3 : ZMod 9949288266089) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 9949288266089) ^ 36 = 9621803046556 := by
        calc
          (3 : ZMod 9949288266089) ^ 36 = (3 : ZMod 9949288266089) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 18 * (3 : ZMod 9949288266089) ^ 18 := by rw [pow_add]
          _ = 9621803046556 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 9949288266089) ^ 72 = 5910497665344 := by
        calc
          (3 : ZMod 9949288266089) ^ 72 = (3 : ZMod 9949288266089) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 36 * (3 : ZMod 9949288266089) ^ 36 := by rw [pow_add]
          _ = 5910497665344 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 9949288266089) ^ 144 = 923861996951 := by
        calc
          (3 : ZMod 9949288266089) ^ 144 = (3 : ZMod 9949288266089) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 72 * (3 : ZMod 9949288266089) ^ 72 := by rw [pow_add]
          _ = 923861996951 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 9949288266089) ^ 289 = 2429758477157 := by
        calc
          (3 : ZMod 9949288266089) ^ 289 = (3 : ZMod 9949288266089) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 144 * (3 : ZMod 9949288266089) ^ 144) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 2429758477157 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 9949288266089) ^ 579 = 1640057992893 := by
        calc
          (3 : ZMod 9949288266089) ^ 579 = (3 : ZMod 9949288266089) ^ (289 + 289 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 289 * (3 : ZMod 9949288266089) ^ 289) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 1640057992893 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 9949288266089) ^ 1158 = 4927128215160 := by
        calc
          (3 : ZMod 9949288266089) ^ 1158 = (3 : ZMod 9949288266089) ^ (579 + 579) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 579 * (3 : ZMod 9949288266089) ^ 579 := by rw [pow_add]
          _ = 4927128215160 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 9949288266089) ^ 2316 = 3132510137059 := by
        calc
          (3 : ZMod 9949288266089) ^ 2316 = (3 : ZMod 9949288266089) ^ (1158 + 1158) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 1158 * (3 : ZMod 9949288266089) ^ 1158 := by rw [pow_add]
          _ = 3132510137059 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 9949288266089) ^ 4632 = 9675198271010 := by
        calc
          (3 : ZMod 9949288266089) ^ 4632 = (3 : ZMod 9949288266089) ^ (2316 + 2316) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2316 * (3 : ZMod 9949288266089) ^ 2316 := by rw [pow_add]
          _ = 9675198271010 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 9949288266089) ^ 9265 = 1626368109808 := by
        calc
          (3 : ZMod 9949288266089) ^ 9265 = (3 : ZMod 9949288266089) ^ (4632 + 4632 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 4632 * (3 : ZMod 9949288266089) ^ 4632) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 1626368109808 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 9949288266089) ^ 18531 = 9854881287733 := by
        calc
          (3 : ZMod 9949288266089) ^ 18531 = (3 : ZMod 9949288266089) ^ (9265 + 9265 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 9265 * (3 : ZMod 9949288266089) ^ 9265) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 9854881287733 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 9949288266089) ^ 37063 = 8205143766908 := by
        calc
          (3 : ZMod 9949288266089) ^ 37063 = (3 : ZMod 9949288266089) ^ (18531 + 18531 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 18531 * (3 : ZMod 9949288266089) ^ 18531) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8205143766908 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 9949288266089) ^ 74127 = 446608408257 := by
        calc
          (3 : ZMod 9949288266089) ^ 74127 = (3 : ZMod 9949288266089) ^ (37063 + 37063 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 37063 * (3 : ZMod 9949288266089) ^ 37063) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 446608408257 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 9949288266089) ^ 148255 = 9185211434321 := by
        calc
          (3 : ZMod 9949288266089) ^ 148255 = (3 : ZMod 9949288266089) ^ (74127 + 74127 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 74127 * (3 : ZMod 9949288266089) ^ 74127) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 9185211434321 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 9949288266089) ^ 296511 = 25412572688 := by
        calc
          (3 : ZMod 9949288266089) ^ 296511 = (3 : ZMod 9949288266089) ^ (148255 + 148255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 148255 * (3 : ZMod 9949288266089) ^ 148255) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 25412572688 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 9949288266089) ^ 593023 = 3284698019682 := by
        calc
          (3 : ZMod 9949288266089) ^ 593023 = (3 : ZMod 9949288266089) ^ (296511 + 296511 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 296511 * (3 : ZMod 9949288266089) ^ 296511) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 3284698019682 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 9949288266089) ^ 1186047 = 3468184915024 := by
        calc
          (3 : ZMod 9949288266089) ^ 1186047 = (3 : ZMod 9949288266089) ^ (593023 + 593023 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 593023 * (3 : ZMod 9949288266089) ^ 593023) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 3468184915024 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 9949288266089) ^ 2372095 = 836006153659 := by
        calc
          (3 : ZMod 9949288266089) ^ 2372095 = (3 : ZMod 9949288266089) ^ (1186047 + 1186047 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 1186047 * (3 : ZMod 9949288266089) ^ 1186047) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 836006153659 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 9949288266089) ^ 4744190 = 6044916366668 := by
        calc
          (3 : ZMod 9949288266089) ^ 4744190 = (3 : ZMod 9949288266089) ^ (2372095 + 2372095) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2372095 * (3 : ZMod 9949288266089) ^ 2372095 := by rw [pow_add]
          _ = 6044916366668 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 9949288266089) ^ 9488380 = 4797581795991 := by
        calc
          (3 : ZMod 9949288266089) ^ 9488380 = (3 : ZMod 9949288266089) ^ (4744190 + 4744190) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 4744190 * (3 : ZMod 9949288266089) ^ 4744190 := by rw [pow_add]
          _ = 4797581795991 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 9949288266089) ^ 18976761 = 1285018325033 := by
        calc
          (3 : ZMod 9949288266089) ^ 18976761 = (3 : ZMod 9949288266089) ^ (9488380 + 9488380 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 9488380 * (3 : ZMod 9949288266089) ^ 9488380) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 1285018325033 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 9949288266089) ^ 37953522 = 4350917379615 := by
        calc
          (3 : ZMod 9949288266089) ^ 37953522 = (3 : ZMod 9949288266089) ^ (18976761 + 18976761) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 18976761 * (3 : ZMod 9949288266089) ^ 18976761 := by rw [pow_add]
          _ = 4350917379615 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 9949288266089) ^ 75907045 = 5079533876613 := by
        calc
          (3 : ZMod 9949288266089) ^ 75907045 = (3 : ZMod 9949288266089) ^ (37953522 + 37953522 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 37953522 * (3 : ZMod 9949288266089) ^ 37953522) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 5079533876613 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 9949288266089) ^ 151814090 = 9110878426170 := by
        calc
          (3 : ZMod 9949288266089) ^ 151814090 = (3 : ZMod 9949288266089) ^ (75907045 + 75907045) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 75907045 * (3 : ZMod 9949288266089) ^ 75907045 := by rw [pow_add]
          _ = 9110878426170 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 9949288266089) ^ 303628181 = 5915580449653 := by
        calc
          (3 : ZMod 9949288266089) ^ 303628181 = (3 : ZMod 9949288266089) ^ (151814090 + 151814090 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 151814090 * (3 : ZMod 9949288266089) ^ 151814090) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 5915580449653 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 9949288266089) ^ 607256363 = 8863517563899 := by
        calc
          (3 : ZMod 9949288266089) ^ 607256363 = (3 : ZMod 9949288266089) ^ (303628181 + 303628181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 303628181 * (3 : ZMod 9949288266089) ^ 303628181) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8863517563899 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 9949288266089) ^ 1214512727 = 6190807466011 := by
        calc
          (3 : ZMod 9949288266089) ^ 1214512727 = (3 : ZMod 9949288266089) ^ (607256363 + 607256363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 607256363 * (3 : ZMod 9949288266089) ^ 607256363) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 6190807466011 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 9949288266089) ^ 2429025455 = 9476800981300 := by
        calc
          (3 : ZMod 9949288266089) ^ 2429025455 = (3 : ZMod 9949288266089) ^ (1214512727 + 1214512727 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 1214512727 * (3 : ZMod 9949288266089) ^ 1214512727) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 9476800981300 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 9949288266089) ^ 4858050911 = 3352929101822 := by
        calc
          (3 : ZMod 9949288266089) ^ 4858050911 = (3 : ZMod 9949288266089) ^ (2429025455 + 2429025455 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 2429025455 * (3 : ZMod 9949288266089) ^ 2429025455) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 3352929101822 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 9949288266089) ^ 9716101822 = 6796114461776 := by
        calc
          (3 : ZMod 9949288266089) ^ 9716101822 = (3 : ZMod 9949288266089) ^ (4858050911 + 4858050911) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 4858050911 * (3 : ZMod 9949288266089) ^ 4858050911 := by rw [pow_add]
          _ = 6796114461776 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 9949288266089) ^ 19432203644 = 112123281126 := by
        calc
          (3 : ZMod 9949288266089) ^ 19432203644 = (3 : ZMod 9949288266089) ^ (9716101822 + 9716101822) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 9716101822 * (3 : ZMod 9949288266089) ^ 9716101822 := by rw [pow_add]
          _ = 112123281126 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 9949288266089) ^ 38864407289 = 499840753049 := by
        calc
          (3 : ZMod 9949288266089) ^ 38864407289 = (3 : ZMod 9949288266089) ^ (19432203644 + 19432203644 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 19432203644 * (3 : ZMod 9949288266089) ^ 19432203644) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 499840753049 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 9949288266089) ^ 77728814578 = 186680497088 := by
        calc
          (3 : ZMod 9949288266089) ^ 77728814578 = (3 : ZMod 9949288266089) ^ (38864407289 + 38864407289) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 38864407289 * (3 : ZMod 9949288266089) ^ 38864407289 := by rw [pow_add]
          _ = 186680497088 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 9949288266089) ^ 155457629157 = 8571934976437 := by
        calc
          (3 : ZMod 9949288266089) ^ 155457629157 = (3 : ZMod 9949288266089) ^ (77728814578 + 77728814578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 77728814578 * (3 : ZMod 9949288266089) ^ 77728814578) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8571934976437 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 9949288266089) ^ 310915258315 = 2454807314439 := by
        calc
          (3 : ZMod 9949288266089) ^ 310915258315 = (3 : ZMod 9949288266089) ^ (155457629157 + 155457629157 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 155457629157 * (3 : ZMod 9949288266089) ^ 155457629157) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 2454807314439 := by rw [factor_0_37]; decide
      have factor_0_39 : (3 : ZMod 9949288266089) ^ 621830516630 = 9645775492681 := by
        calc
          (3 : ZMod 9949288266089) ^ 621830516630 = (3 : ZMod 9949288266089) ^ (310915258315 + 310915258315) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 310915258315 * (3 : ZMod 9949288266089) ^ 310915258315 := by rw [pow_add]
          _ = 9645775492681 := by rw [factor_0_38]; decide
      have factor_0_40 : (3 : ZMod 9949288266089) ^ 1243661033261 = 8888476366373 := by
        calc
          (3 : ZMod 9949288266089) ^ 1243661033261 = (3 : ZMod 9949288266089) ^ (621830516630 + 621830516630 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = ((3 : ZMod 9949288266089) ^ 621830516630 * (3 : ZMod 9949288266089) ^ 621830516630) * (3 : ZMod 9949288266089) := by rw [pow_succ, pow_add]
          _ = 8888476366373 := by rw [factor_0_39]; decide
      have factor_0_41 : (3 : ZMod 9949288266089) ^ 2487322066522 = 261545440743 := by
        calc
          (3 : ZMod 9949288266089) ^ 2487322066522 = (3 : ZMod 9949288266089) ^ (1243661033261 + 1243661033261) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 1243661033261 * (3 : ZMod 9949288266089) ^ 1243661033261 := by rw [pow_add]
          _ = 261545440743 := by rw [factor_0_40]; decide
      have factor_0_42 : (3 : ZMod 9949288266089) ^ 4974644133044 = 9949288266088 := by
        calc
          (3 : ZMod 9949288266089) ^ 4974644133044 = (3 : ZMod 9949288266089) ^ (2487322066522 + 2487322066522) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2487322066522 * (3 : ZMod 9949288266089) ^ 2487322066522 := by rw [pow_add]
          _ = 9949288266088 := by rw [factor_0_41]; decide
      change (3 : ZMod 9949288266089) ^ 4974644133044 ≠ 1
      rw [factor_0_42]
      decide
    ·
      have factor_1_0 : (3 : ZMod 9949288266089) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 9949288266089) ^ 2 = 9 := by
        calc
          (3 : ZMod 9949288266089) ^ 2 = (3 : ZMod 9949288266089) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 1 * (3 : ZMod 9949288266089) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 9949288266089) ^ 4 = 81 := by
        calc
          (3 : ZMod 9949288266089) ^ 4 = (3 : ZMod 9949288266089) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 2 * (3 : ZMod 9949288266089) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 9949288266089) ^ 8 = 6561 := by
        calc
          (3 : ZMod 9949288266089) ^ 8 = (3 : ZMod 9949288266089) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 9949288266089) ^ n) (by norm_num)
          _ = (3 : ZMod 9949288266089) ^ 4 * (3 : ZMod 9949288266089) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      change (3 : ZMod 9949288266089) ^ 8 ≠ 1
      rw [factor_1_3]
      decide

#print axioms prime_lucas_9949288266089

end TotientTailPeriodKiller
end Erdos249257
