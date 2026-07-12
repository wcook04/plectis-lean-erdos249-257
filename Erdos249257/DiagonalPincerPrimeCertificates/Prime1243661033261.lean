import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime51776063

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1243661033261 : Nat.Prime 1243661033261 := by
  apply lucas_primality 1243661033261 (2 : ZMod 1243661033261)
  ·
      have fermat_0 : (2 : ZMod 1243661033261) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1243661033261) ^ 2 = 4 := by
        calc
          (2 : ZMod 1243661033261) ^ 2 = (2 : ZMod 1243661033261) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1 * (2 : ZMod 1243661033261) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1243661033261) ^ 4 = 16 := by
        calc
          (2 : ZMod 1243661033261) ^ 4 = (2 : ZMod 1243661033261) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 2 * (2 : ZMod 1243661033261) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1243661033261) ^ 9 = 512 := by
        calc
          (2 : ZMod 1243661033261) ^ 9 = (2 : ZMod 1243661033261) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 4 * (2 : ZMod 1243661033261) ^ 4) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1243661033261) ^ 18 = 262144 := by
        calc
          (2 : ZMod 1243661033261) ^ 18 = (2 : ZMod 1243661033261) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 9 * (2 : ZMod 1243661033261) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1243661033261) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 1243661033261) ^ 36 = (2 : ZMod 1243661033261) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 18 * (2 : ZMod 1243661033261) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1243661033261) ^ 72 = 275398071628 := by
        calc
          (2 : ZMod 1243661033261) ^ 72 = (2 : ZMod 1243661033261) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 36 * (2 : ZMod 1243661033261) ^ 36 := by rw [pow_add]
          _ = 275398071628 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1243661033261) ^ 144 = 136175769975 := by
        calc
          (2 : ZMod 1243661033261) ^ 144 = (2 : ZMod 1243661033261) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 72 * (2 : ZMod 1243661033261) ^ 72 := by rw [pow_add]
          _ = 136175769975 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1243661033261) ^ 289 = 1217504312048 := by
        calc
          (2 : ZMod 1243661033261) ^ 289 = (2 : ZMod 1243661033261) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 144 * (2 : ZMod 1243661033261) ^ 144) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1217504312048 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1243661033261) ^ 579 = 1242101652116 := by
        calc
          (2 : ZMod 1243661033261) ^ 579 = (2 : ZMod 1243661033261) ^ (289 + 289 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 289 * (2 : ZMod 1243661033261) ^ 289) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1242101652116 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1243661033261) ^ 1158 = 76436907514 := by
        calc
          (2 : ZMod 1243661033261) ^ 1158 = (2 : ZMod 1243661033261) ^ (579 + 579) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 579 * (2 : ZMod 1243661033261) ^ 579 := by rw [pow_add]
          _ = 76436907514 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1243661033261) ^ 2316 = 1001914356124 := by
        calc
          (2 : ZMod 1243661033261) ^ 2316 = (2 : ZMod 1243661033261) ^ (1158 + 1158) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1158 * (2 : ZMod 1243661033261) ^ 1158 := by rw [pow_add]
          _ = 1001914356124 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1243661033261) ^ 4632 = 575147934169 := by
        calc
          (2 : ZMod 1243661033261) ^ 4632 = (2 : ZMod 1243661033261) ^ (2316 + 2316) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 2316 * (2 : ZMod 1243661033261) ^ 2316 := by rw [pow_add]
          _ = 575147934169 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1243661033261) ^ 9265 = 1047091881463 := by
        calc
          (2 : ZMod 1243661033261) ^ 9265 = (2 : ZMod 1243661033261) ^ (4632 + 4632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 4632 * (2 : ZMod 1243661033261) ^ 4632) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1047091881463 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1243661033261) ^ 18531 = 1208006114881 := by
        calc
          (2 : ZMod 1243661033261) ^ 18531 = (2 : ZMod 1243661033261) ^ (9265 + 9265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 9265 * (2 : ZMod 1243661033261) ^ 9265) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1208006114881 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1243661033261) ^ 37063 = 1240703352323 := by
        calc
          (2 : ZMod 1243661033261) ^ 37063 = (2 : ZMod 1243661033261) ^ (18531 + 18531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 18531 * (2 : ZMod 1243661033261) ^ 18531) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1240703352323 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1243661033261) ^ 74127 = 534780267565 := by
        calc
          (2 : ZMod 1243661033261) ^ 74127 = (2 : ZMod 1243661033261) ^ (37063 + 37063 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 37063 * (2 : ZMod 1243661033261) ^ 37063) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 534780267565 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1243661033261) ^ 148255 = 280545594080 := by
        calc
          (2 : ZMod 1243661033261) ^ 148255 = (2 : ZMod 1243661033261) ^ (74127 + 74127 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 74127 * (2 : ZMod 1243661033261) ^ 74127) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 280545594080 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1243661033261) ^ 296511 = 683692455882 := by
        calc
          (2 : ZMod 1243661033261) ^ 296511 = (2 : ZMod 1243661033261) ^ (148255 + 148255 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 148255 * (2 : ZMod 1243661033261) ^ 148255) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 683692455882 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1243661033261) ^ 593023 = 617457719069 := by
        calc
          (2 : ZMod 1243661033261) ^ 593023 = (2 : ZMod 1243661033261) ^ (296511 + 296511 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 296511 * (2 : ZMod 1243661033261) ^ 296511) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 617457719069 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1243661033261) ^ 1186047 = 343078700702 := by
        calc
          (2 : ZMod 1243661033261) ^ 1186047 = (2 : ZMod 1243661033261) ^ (593023 + 593023 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 593023 * (2 : ZMod 1243661033261) ^ 593023) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 343078700702 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1243661033261) ^ 2372095 = 51537298138 := by
        calc
          (2 : ZMod 1243661033261) ^ 2372095 = (2 : ZMod 1243661033261) ^ (1186047 + 1186047 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 1186047 * (2 : ZMod 1243661033261) ^ 1186047) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 51537298138 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1243661033261) ^ 4744190 = 1131464962695 := by
        calc
          (2 : ZMod 1243661033261) ^ 4744190 = (2 : ZMod 1243661033261) ^ (2372095 + 2372095) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 2372095 * (2 : ZMod 1243661033261) ^ 2372095 := by rw [pow_add]
          _ = 1131464962695 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1243661033261) ^ 9488380 = 146485432903 := by
        calc
          (2 : ZMod 1243661033261) ^ 9488380 = (2 : ZMod 1243661033261) ^ (4744190 + 4744190) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 4744190 * (2 : ZMod 1243661033261) ^ 4744190 := by rw [pow_add]
          _ = 146485432903 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1243661033261) ^ 18976761 = 1164331132929 := by
        calc
          (2 : ZMod 1243661033261) ^ 18976761 = (2 : ZMod 1243661033261) ^ (9488380 + 9488380 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 9488380 * (2 : ZMod 1243661033261) ^ 9488380) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1164331132929 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1243661033261) ^ 37953522 = 829706538981 := by
        calc
          (2 : ZMod 1243661033261) ^ 37953522 = (2 : ZMod 1243661033261) ^ (18976761 + 18976761) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 18976761 * (2 : ZMod 1243661033261) ^ 18976761 := by rw [pow_add]
          _ = 829706538981 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1243661033261) ^ 75907045 = 568775020335 := by
        calc
          (2 : ZMod 1243661033261) ^ 75907045 = (2 : ZMod 1243661033261) ^ (37953522 + 37953522 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 37953522 * (2 : ZMod 1243661033261) ^ 37953522) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 568775020335 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1243661033261) ^ 151814090 = 317323093930 := by
        calc
          (2 : ZMod 1243661033261) ^ 151814090 = (2 : ZMod 1243661033261) ^ (75907045 + 75907045) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 75907045 * (2 : ZMod 1243661033261) ^ 75907045 := by rw [pow_add]
          _ = 317323093930 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1243661033261) ^ 303628181 = 1023510581600 := by
        calc
          (2 : ZMod 1243661033261) ^ 303628181 = (2 : ZMod 1243661033261) ^ (151814090 + 151814090 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 151814090 * (2 : ZMod 1243661033261) ^ 151814090) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1023510581600 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1243661033261) ^ 607256363 = 430286531638 := by
        calc
          (2 : ZMod 1243661033261) ^ 607256363 = (2 : ZMod 1243661033261) ^ (303628181 + 303628181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 303628181 * (2 : ZMod 1243661033261) ^ 303628181) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 430286531638 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1243661033261) ^ 1214512727 = 644504955402 := by
        calc
          (2 : ZMod 1243661033261) ^ 1214512727 = (2 : ZMod 1243661033261) ^ (607256363 + 607256363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 607256363 * (2 : ZMod 1243661033261) ^ 607256363) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 644504955402 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 1243661033261) ^ 2429025455 = 189672990125 := by
        calc
          (2 : ZMod 1243661033261) ^ 2429025455 = (2 : ZMod 1243661033261) ^ (1214512727 + 1214512727 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 1214512727 * (2 : ZMod 1243661033261) ^ 1214512727) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 189672990125 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 1243661033261) ^ 4858050911 = 472077828357 := by
        calc
          (2 : ZMod 1243661033261) ^ 4858050911 = (2 : ZMod 1243661033261) ^ (2429025455 + 2429025455 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 2429025455 * (2 : ZMod 1243661033261) ^ 2429025455) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 472077828357 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 1243661033261) ^ 9716101822 = 457084983372 := by
        calc
          (2 : ZMod 1243661033261) ^ 9716101822 = (2 : ZMod 1243661033261) ^ (4858050911 + 4858050911) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 4858050911 * (2 : ZMod 1243661033261) ^ 4858050911 := by rw [pow_add]
          _ = 457084983372 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 1243661033261) ^ 19432203644 = 45216153391 := by
        calc
          (2 : ZMod 1243661033261) ^ 19432203644 = (2 : ZMod 1243661033261) ^ (9716101822 + 9716101822) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 9716101822 * (2 : ZMod 1243661033261) ^ 9716101822 := by rw [pow_add]
          _ = 45216153391 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 1243661033261) ^ 38864407289 = 304833033298 := by
        calc
          (2 : ZMod 1243661033261) ^ 38864407289 = (2 : ZMod 1243661033261) ^ (19432203644 + 19432203644 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 19432203644 * (2 : ZMod 1243661033261) ^ 19432203644) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 304833033298 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 1243661033261) ^ 77728814578 = 351425339280 := by
        calc
          (2 : ZMod 1243661033261) ^ 77728814578 = (2 : ZMod 1243661033261) ^ (38864407289 + 38864407289) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 38864407289 * (2 : ZMod 1243661033261) ^ 38864407289 := by rw [pow_add]
          _ = 351425339280 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 1243661033261) ^ 155457629157 = 845785041140 := by
        calc
          (2 : ZMod 1243661033261) ^ 155457629157 = (2 : ZMod 1243661033261) ^ (77728814578 + 77728814578 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 77728814578 * (2 : ZMod 1243661033261) ^ 77728814578) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 845785041140 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 1243661033261) ^ 310915258315 = 795751984241 := by
        calc
          (2 : ZMod 1243661033261) ^ 310915258315 = (2 : ZMod 1243661033261) ^ (155457629157 + 155457629157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 155457629157 * (2 : ZMod 1243661033261) ^ 155457629157) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 795751984241 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 1243661033261) ^ 621830516630 = 1243661033260 := by
        calc
          (2 : ZMod 1243661033261) ^ 621830516630 = (2 : ZMod 1243661033261) ^ (310915258315 + 310915258315) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 310915258315 * (2 : ZMod 1243661033261) ^ 310915258315 := by rw [pow_add]
          _ = 1243661033260 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 1243661033261) ^ 1243661033260 = 1 := by
        calc
          (2 : ZMod 1243661033261) ^ 1243661033260 = (2 : ZMod 1243661033261) ^ (621830516630 + 621830516630) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 621830516630 * (2 : ZMod 1243661033261) ^ 621830516630 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (1201, 1), (51776063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (1201, 1), (51776063, 1)] : List FactorBlock).map factorBlockValue).prod = 1243661033261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_51776063) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1243661033261) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1243661033261) ^ 2 = 4 := by
        calc
          (2 : ZMod 1243661033261) ^ 2 = (2 : ZMod 1243661033261) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1 * (2 : ZMod 1243661033261) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1243661033261) ^ 4 = 16 := by
        calc
          (2 : ZMod 1243661033261) ^ 4 = (2 : ZMod 1243661033261) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 2 * (2 : ZMod 1243661033261) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1243661033261) ^ 9 = 512 := by
        calc
          (2 : ZMod 1243661033261) ^ 9 = (2 : ZMod 1243661033261) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 4 * (2 : ZMod 1243661033261) ^ 4) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1243661033261) ^ 18 = 262144 := by
        calc
          (2 : ZMod 1243661033261) ^ 18 = (2 : ZMod 1243661033261) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 9 * (2 : ZMod 1243661033261) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1243661033261) ^ 36 = 68719476736 := by
        calc
          (2 : ZMod 1243661033261) ^ 36 = (2 : ZMod 1243661033261) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 18 * (2 : ZMod 1243661033261) ^ 18 := by rw [pow_add]
          _ = 68719476736 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1243661033261) ^ 72 = 275398071628 := by
        calc
          (2 : ZMod 1243661033261) ^ 72 = (2 : ZMod 1243661033261) ^ (36 + 36) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 36 * (2 : ZMod 1243661033261) ^ 36 := by rw [pow_add]
          _ = 275398071628 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1243661033261) ^ 144 = 136175769975 := by
        calc
          (2 : ZMod 1243661033261) ^ 144 = (2 : ZMod 1243661033261) ^ (72 + 72) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 72 * (2 : ZMod 1243661033261) ^ 72 := by rw [pow_add]
          _ = 136175769975 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1243661033261) ^ 289 = 1217504312048 := by
        calc
          (2 : ZMod 1243661033261) ^ 289 = (2 : ZMod 1243661033261) ^ (144 + 144 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 144 * (2 : ZMod 1243661033261) ^ 144) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1217504312048 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1243661033261) ^ 579 = 1242101652116 := by
        calc
          (2 : ZMod 1243661033261) ^ 579 = (2 : ZMod 1243661033261) ^ (289 + 289 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 289 * (2 : ZMod 1243661033261) ^ 289) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1242101652116 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1243661033261) ^ 1158 = 76436907514 := by
        calc
          (2 : ZMod 1243661033261) ^ 1158 = (2 : ZMod 1243661033261) ^ (579 + 579) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 579 * (2 : ZMod 1243661033261) ^ 579 := by rw [pow_add]
          _ = 76436907514 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1243661033261) ^ 2316 = 1001914356124 := by
        calc
          (2 : ZMod 1243661033261) ^ 2316 = (2 : ZMod 1243661033261) ^ (1158 + 1158) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1158 * (2 : ZMod 1243661033261) ^ 1158 := by rw [pow_add]
          _ = 1001914356124 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1243661033261) ^ 4632 = 575147934169 := by
        calc
          (2 : ZMod 1243661033261) ^ 4632 = (2 : ZMod 1243661033261) ^ (2316 + 2316) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 2316 * (2 : ZMod 1243661033261) ^ 2316 := by rw [pow_add]
          _ = 575147934169 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1243661033261) ^ 9265 = 1047091881463 := by
        calc
          (2 : ZMod 1243661033261) ^ 9265 = (2 : ZMod 1243661033261) ^ (4632 + 4632 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 4632 * (2 : ZMod 1243661033261) ^ 4632) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1047091881463 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1243661033261) ^ 18531 = 1208006114881 := by
        calc
          (2 : ZMod 1243661033261) ^ 18531 = (2 : ZMod 1243661033261) ^ (9265 + 9265 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 9265 * (2 : ZMod 1243661033261) ^ 9265) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1208006114881 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1243661033261) ^ 37063 = 1240703352323 := by
        calc
          (2 : ZMod 1243661033261) ^ 37063 = (2 : ZMod 1243661033261) ^ (18531 + 18531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 18531 * (2 : ZMod 1243661033261) ^ 18531) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1240703352323 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1243661033261) ^ 74127 = 534780267565 := by
        calc
          (2 : ZMod 1243661033261) ^ 74127 = (2 : ZMod 1243661033261) ^ (37063 + 37063 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 37063 * (2 : ZMod 1243661033261) ^ 37063) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 534780267565 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1243661033261) ^ 148255 = 280545594080 := by
        calc
          (2 : ZMod 1243661033261) ^ 148255 = (2 : ZMod 1243661033261) ^ (74127 + 74127 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 74127 * (2 : ZMod 1243661033261) ^ 74127) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 280545594080 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1243661033261) ^ 296511 = 683692455882 := by
        calc
          (2 : ZMod 1243661033261) ^ 296511 = (2 : ZMod 1243661033261) ^ (148255 + 148255 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 148255 * (2 : ZMod 1243661033261) ^ 148255) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 683692455882 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1243661033261) ^ 593023 = 617457719069 := by
        calc
          (2 : ZMod 1243661033261) ^ 593023 = (2 : ZMod 1243661033261) ^ (296511 + 296511 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 296511 * (2 : ZMod 1243661033261) ^ 296511) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 617457719069 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1243661033261) ^ 1186047 = 343078700702 := by
        calc
          (2 : ZMod 1243661033261) ^ 1186047 = (2 : ZMod 1243661033261) ^ (593023 + 593023 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 593023 * (2 : ZMod 1243661033261) ^ 593023) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 343078700702 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1243661033261) ^ 2372095 = 51537298138 := by
        calc
          (2 : ZMod 1243661033261) ^ 2372095 = (2 : ZMod 1243661033261) ^ (1186047 + 1186047 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 1186047 * (2 : ZMod 1243661033261) ^ 1186047) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 51537298138 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1243661033261) ^ 4744190 = 1131464962695 := by
        calc
          (2 : ZMod 1243661033261) ^ 4744190 = (2 : ZMod 1243661033261) ^ (2372095 + 2372095) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 2372095 * (2 : ZMod 1243661033261) ^ 2372095 := by rw [pow_add]
          _ = 1131464962695 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1243661033261) ^ 9488380 = 146485432903 := by
        calc
          (2 : ZMod 1243661033261) ^ 9488380 = (2 : ZMod 1243661033261) ^ (4744190 + 4744190) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 4744190 * (2 : ZMod 1243661033261) ^ 4744190 := by rw [pow_add]
          _ = 146485432903 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1243661033261) ^ 18976761 = 1164331132929 := by
        calc
          (2 : ZMod 1243661033261) ^ 18976761 = (2 : ZMod 1243661033261) ^ (9488380 + 9488380 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 9488380 * (2 : ZMod 1243661033261) ^ 9488380) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1164331132929 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1243661033261) ^ 37953522 = 829706538981 := by
        calc
          (2 : ZMod 1243661033261) ^ 37953522 = (2 : ZMod 1243661033261) ^ (18976761 + 18976761) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 18976761 * (2 : ZMod 1243661033261) ^ 18976761 := by rw [pow_add]
          _ = 829706538981 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1243661033261) ^ 75907045 = 568775020335 := by
        calc
          (2 : ZMod 1243661033261) ^ 75907045 = (2 : ZMod 1243661033261) ^ (37953522 + 37953522 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 37953522 * (2 : ZMod 1243661033261) ^ 37953522) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 568775020335 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1243661033261) ^ 151814090 = 317323093930 := by
        calc
          (2 : ZMod 1243661033261) ^ 151814090 = (2 : ZMod 1243661033261) ^ (75907045 + 75907045) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 75907045 * (2 : ZMod 1243661033261) ^ 75907045 := by rw [pow_add]
          _ = 317323093930 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1243661033261) ^ 303628181 = 1023510581600 := by
        calc
          (2 : ZMod 1243661033261) ^ 303628181 = (2 : ZMod 1243661033261) ^ (151814090 + 151814090 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 151814090 * (2 : ZMod 1243661033261) ^ 151814090) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1023510581600 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1243661033261) ^ 607256363 = 430286531638 := by
        calc
          (2 : ZMod 1243661033261) ^ 607256363 = (2 : ZMod 1243661033261) ^ (303628181 + 303628181 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 303628181 * (2 : ZMod 1243661033261) ^ 303628181) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 430286531638 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 1243661033261) ^ 1214512727 = 644504955402 := by
        calc
          (2 : ZMod 1243661033261) ^ 1214512727 = (2 : ZMod 1243661033261) ^ (607256363 + 607256363 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 607256363 * (2 : ZMod 1243661033261) ^ 607256363) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 644504955402 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 1243661033261) ^ 2429025455 = 189672990125 := by
        calc
          (2 : ZMod 1243661033261) ^ 2429025455 = (2 : ZMod 1243661033261) ^ (1214512727 + 1214512727 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 1214512727 * (2 : ZMod 1243661033261) ^ 1214512727) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 189672990125 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 1243661033261) ^ 4858050911 = 472077828357 := by
        calc
          (2 : ZMod 1243661033261) ^ 4858050911 = (2 : ZMod 1243661033261) ^ (2429025455 + 2429025455 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 2429025455 * (2 : ZMod 1243661033261) ^ 2429025455) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 472077828357 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 1243661033261) ^ 9716101822 = 457084983372 := by
        calc
          (2 : ZMod 1243661033261) ^ 9716101822 = (2 : ZMod 1243661033261) ^ (4858050911 + 4858050911) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 4858050911 * (2 : ZMod 1243661033261) ^ 4858050911 := by rw [pow_add]
          _ = 457084983372 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 1243661033261) ^ 19432203644 = 45216153391 := by
        calc
          (2 : ZMod 1243661033261) ^ 19432203644 = (2 : ZMod 1243661033261) ^ (9716101822 + 9716101822) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 9716101822 * (2 : ZMod 1243661033261) ^ 9716101822 := by rw [pow_add]
          _ = 45216153391 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 1243661033261) ^ 38864407289 = 304833033298 := by
        calc
          (2 : ZMod 1243661033261) ^ 38864407289 = (2 : ZMod 1243661033261) ^ (19432203644 + 19432203644 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 19432203644 * (2 : ZMod 1243661033261) ^ 19432203644) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 304833033298 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 1243661033261) ^ 77728814578 = 351425339280 := by
        calc
          (2 : ZMod 1243661033261) ^ 77728814578 = (2 : ZMod 1243661033261) ^ (38864407289 + 38864407289) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 38864407289 * (2 : ZMod 1243661033261) ^ 38864407289 := by rw [pow_add]
          _ = 351425339280 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 1243661033261) ^ 155457629157 = 845785041140 := by
        calc
          (2 : ZMod 1243661033261) ^ 155457629157 = (2 : ZMod 1243661033261) ^ (77728814578 + 77728814578 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 77728814578 * (2 : ZMod 1243661033261) ^ 77728814578) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 845785041140 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 1243661033261) ^ 310915258315 = 795751984241 := by
        calc
          (2 : ZMod 1243661033261) ^ 310915258315 = (2 : ZMod 1243661033261) ^ (155457629157 + 155457629157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 155457629157 * (2 : ZMod 1243661033261) ^ 155457629157) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 795751984241 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 1243661033261) ^ 621830516630 = 1243661033260 := by
        calc
          (2 : ZMod 1243661033261) ^ 621830516630 = (2 : ZMod 1243661033261) ^ (310915258315 + 310915258315) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 310915258315 * (2 : ZMod 1243661033261) ^ 310915258315 := by rw [pow_add]
          _ = 1243661033260 := by rw [factor_0_38]; decide
      change (2 : ZMod 1243661033261) ^ 621830516630 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1243661033261) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1243661033261) ^ 3 = 8 := by
        calc
          (2 : ZMod 1243661033261) ^ 3 = (2 : ZMod 1243661033261) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 1 * (2 : ZMod 1243661033261) ^ 1) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1243661033261) ^ 7 = 128 := by
        calc
          (2 : ZMod 1243661033261) ^ 7 = (2 : ZMod 1243661033261) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 3 * (2 : ZMod 1243661033261) ^ 3) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1243661033261) ^ 14 = 16384 := by
        calc
          (2 : ZMod 1243661033261) ^ 14 = (2 : ZMod 1243661033261) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 7 * (2 : ZMod 1243661033261) ^ 7 := by rw [pow_add]
          _ = 16384 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1243661033261) ^ 28 = 268435456 := by
        calc
          (2 : ZMod 1243661033261) ^ 28 = (2 : ZMod 1243661033261) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 14 * (2 : ZMod 1243661033261) ^ 14 := by rw [pow_add]
          _ = 268435456 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1243661033261) ^ 57 = 991202604453 := by
        calc
          (2 : ZMod 1243661033261) ^ 57 = (2 : ZMod 1243661033261) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 28 * (2 : ZMod 1243661033261) ^ 28) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 991202604453 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1243661033261) ^ 115 = 301330986399 := by
        calc
          (2 : ZMod 1243661033261) ^ 115 = (2 : ZMod 1243661033261) ^ (57 + 57 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 57 * (2 : ZMod 1243661033261) ^ 57) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 301330986399 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1243661033261) ^ 231 = 140561531846 := by
        calc
          (2 : ZMod 1243661033261) ^ 231 = (2 : ZMod 1243661033261) ^ (115 + 115 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 115 * (2 : ZMod 1243661033261) ^ 115) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 140561531846 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1243661033261) ^ 463 = 1192107936540 := by
        calc
          (2 : ZMod 1243661033261) ^ 463 = (2 : ZMod 1243661033261) ^ (231 + 231 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 231 * (2 : ZMod 1243661033261) ^ 231) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1192107936540 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1243661033261) ^ 926 = 969582474285 := by
        calc
          (2 : ZMod 1243661033261) ^ 926 = (2 : ZMod 1243661033261) ^ (463 + 463) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 463 * (2 : ZMod 1243661033261) ^ 463 := by rw [pow_add]
          _ = 969582474285 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1243661033261) ^ 1853 = 621312517082 := by
        calc
          (2 : ZMod 1243661033261) ^ 1853 = (2 : ZMod 1243661033261) ^ (926 + 926 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 926 * (2 : ZMod 1243661033261) ^ 926) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 621312517082 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1243661033261) ^ 3706 = 866082818265 := by
        calc
          (2 : ZMod 1243661033261) ^ 3706 = (2 : ZMod 1243661033261) ^ (1853 + 1853) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1853 * (2 : ZMod 1243661033261) ^ 1853 := by rw [pow_add]
          _ = 866082818265 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1243661033261) ^ 7412 = 271692794997 := by
        calc
          (2 : ZMod 1243661033261) ^ 7412 = (2 : ZMod 1243661033261) ^ (3706 + 3706) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 3706 * (2 : ZMod 1243661033261) ^ 3706 := by rw [pow_add]
          _ = 271692794997 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1243661033261) ^ 14825 = 863879633348 := by
        calc
          (2 : ZMod 1243661033261) ^ 14825 = (2 : ZMod 1243661033261) ^ (7412 + 7412 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 7412 * (2 : ZMod 1243661033261) ^ 7412) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 863879633348 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1243661033261) ^ 29651 = 241148199261 := by
        calc
          (2 : ZMod 1243661033261) ^ 29651 = (2 : ZMod 1243661033261) ^ (14825 + 14825 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 14825 * (2 : ZMod 1243661033261) ^ 14825) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 241148199261 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1243661033261) ^ 59302 = 536279179820 := by
        calc
          (2 : ZMod 1243661033261) ^ 59302 = (2 : ZMod 1243661033261) ^ (29651 + 29651) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 29651 * (2 : ZMod 1243661033261) ^ 29651 := by rw [pow_add]
          _ = 536279179820 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1243661033261) ^ 118604 = 104820726005 := by
        calc
          (2 : ZMod 1243661033261) ^ 118604 = (2 : ZMod 1243661033261) ^ (59302 + 59302) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 59302 * (2 : ZMod 1243661033261) ^ 59302 := by rw [pow_add]
          _ = 104820726005 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1243661033261) ^ 237209 = 193953137217 := by
        calc
          (2 : ZMod 1243661033261) ^ 237209 = (2 : ZMod 1243661033261) ^ (118604 + 118604 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 118604 * (2 : ZMod 1243661033261) ^ 118604) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 193953137217 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1243661033261) ^ 474419 = 464154253019 := by
        calc
          (2 : ZMod 1243661033261) ^ 474419 = (2 : ZMod 1243661033261) ^ (237209 + 237209 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 237209 * (2 : ZMod 1243661033261) ^ 237209) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 464154253019 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1243661033261) ^ 948838 = 505453092417 := by
        calc
          (2 : ZMod 1243661033261) ^ 948838 = (2 : ZMod 1243661033261) ^ (474419 + 474419) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 474419 * (2 : ZMod 1243661033261) ^ 474419 := by rw [pow_add]
          _ = 505453092417 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1243661033261) ^ 1897676 = 531039440493 := by
        calc
          (2 : ZMod 1243661033261) ^ 1897676 = (2 : ZMod 1243661033261) ^ (948838 + 948838) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 948838 * (2 : ZMod 1243661033261) ^ 948838 := by rw [pow_add]
          _ = 531039440493 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1243661033261) ^ 3795352 = 391643615050 := by
        calc
          (2 : ZMod 1243661033261) ^ 3795352 = (2 : ZMod 1243661033261) ^ (1897676 + 1897676) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1897676 * (2 : ZMod 1243661033261) ^ 1897676 := by rw [pow_add]
          _ = 391643615050 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1243661033261) ^ 7590704 = 900642963224 := by
        calc
          (2 : ZMod 1243661033261) ^ 7590704 = (2 : ZMod 1243661033261) ^ (3795352 + 3795352) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 3795352 * (2 : ZMod 1243661033261) ^ 3795352 := by rw [pow_add]
          _ = 900642963224 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1243661033261) ^ 15181409 = 1203249269640 := by
        calc
          (2 : ZMod 1243661033261) ^ 15181409 = (2 : ZMod 1243661033261) ^ (7590704 + 7590704 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 7590704 * (2 : ZMod 1243661033261) ^ 7590704) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1203249269640 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1243661033261) ^ 30362818 = 1116663049331 := by
        calc
          (2 : ZMod 1243661033261) ^ 30362818 = (2 : ZMod 1243661033261) ^ (15181409 + 15181409) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 15181409 * (2 : ZMod 1243661033261) ^ 15181409 := by rw [pow_add]
          _ = 1116663049331 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1243661033261) ^ 60725636 = 770818671926 := by
        calc
          (2 : ZMod 1243661033261) ^ 60725636 = (2 : ZMod 1243661033261) ^ (30362818 + 30362818) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 30362818 * (2 : ZMod 1243661033261) ^ 30362818 := by rw [pow_add]
          _ = 770818671926 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1243661033261) ^ 121451272 = 649175913468 := by
        calc
          (2 : ZMod 1243661033261) ^ 121451272 = (2 : ZMod 1243661033261) ^ (60725636 + 60725636) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 60725636 * (2 : ZMod 1243661033261) ^ 60725636 := by rw [pow_add]
          _ = 649175913468 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1243661033261) ^ 242902545 = 1133133291433 := by
        calc
          (2 : ZMod 1243661033261) ^ 242902545 = (2 : ZMod 1243661033261) ^ (121451272 + 121451272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 121451272 * (2 : ZMod 1243661033261) ^ 121451272) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1133133291433 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 1243661033261) ^ 485805091 = 809244425795 := by
        calc
          (2 : ZMod 1243661033261) ^ 485805091 = (2 : ZMod 1243661033261) ^ (242902545 + 242902545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 242902545 * (2 : ZMod 1243661033261) ^ 242902545) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 809244425795 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 1243661033261) ^ 971610182 = 989520186816 := by
        calc
          (2 : ZMod 1243661033261) ^ 971610182 = (2 : ZMod 1243661033261) ^ (485805091 + 485805091) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 485805091 * (2 : ZMod 1243661033261) ^ 485805091 := by rw [pow_add]
          _ = 989520186816 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 1243661033261) ^ 1943220364 = 229632829646 := by
        calc
          (2 : ZMod 1243661033261) ^ 1943220364 = (2 : ZMod 1243661033261) ^ (971610182 + 971610182) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 971610182 * (2 : ZMod 1243661033261) ^ 971610182 := by rw [pow_add]
          _ = 229632829646 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 1243661033261) ^ 3886440728 = 5597387888 := by
        calc
          (2 : ZMod 1243661033261) ^ 3886440728 = (2 : ZMod 1243661033261) ^ (1943220364 + 1943220364) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1943220364 * (2 : ZMod 1243661033261) ^ 1943220364 := by rw [pow_add]
          _ = 5597387888 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 1243661033261) ^ 7772881457 = 594641328517 := by
        calc
          (2 : ZMod 1243661033261) ^ 7772881457 = (2 : ZMod 1243661033261) ^ (3886440728 + 3886440728 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 3886440728 * (2 : ZMod 1243661033261) ^ 3886440728) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 594641328517 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 1243661033261) ^ 15545762915 = 742399301322 := by
        calc
          (2 : ZMod 1243661033261) ^ 15545762915 = (2 : ZMod 1243661033261) ^ (7772881457 + 7772881457 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 7772881457 * (2 : ZMod 1243661033261) ^ 7772881457) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 742399301322 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 1243661033261) ^ 31091525831 = 532171130382 := by
        calc
          (2 : ZMod 1243661033261) ^ 31091525831 = (2 : ZMod 1243661033261) ^ (15545762915 + 15545762915 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 15545762915 * (2 : ZMod 1243661033261) ^ 15545762915) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 532171130382 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 1243661033261) ^ 62183051663 = 1202290538847 := by
        calc
          (2 : ZMod 1243661033261) ^ 62183051663 = (2 : ZMod 1243661033261) ^ (31091525831 + 31091525831 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 31091525831 * (2 : ZMod 1243661033261) ^ 31091525831) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1202290538847 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 1243661033261) ^ 124366103326 = 726484508636 := by
        calc
          (2 : ZMod 1243661033261) ^ 124366103326 = (2 : ZMod 1243661033261) ^ (62183051663 + 62183051663) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 62183051663 * (2 : ZMod 1243661033261) ^ 62183051663 := by rw [pow_add]
          _ = 726484508636 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 1243661033261) ^ 248732206652 = 224200193972 := by
        calc
          (2 : ZMod 1243661033261) ^ 248732206652 = (2 : ZMod 1243661033261) ^ (124366103326 + 124366103326) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 124366103326 * (2 : ZMod 1243661033261) ^ 124366103326 := by rw [pow_add]
          _ = 224200193972 := by rw [factor_1_36]; decide
      change (2 : ZMod 1243661033261) ^ 248732206652 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1243661033261) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1243661033261) ^ 3 = 8 := by
        calc
          (2 : ZMod 1243661033261) ^ 3 = (2 : ZMod 1243661033261) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 1 * (2 : ZMod 1243661033261) ^ 1) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1243661033261) ^ 7 = 128 := by
        calc
          (2 : ZMod 1243661033261) ^ 7 = (2 : ZMod 1243661033261) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 3 * (2 : ZMod 1243661033261) ^ 3) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1243661033261) ^ 15 = 32768 := by
        calc
          (2 : ZMod 1243661033261) ^ 15 = (2 : ZMod 1243661033261) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 7 * (2 : ZMod 1243661033261) ^ 7) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1243661033261) ^ 30 = 1073741824 := by
        calc
          (2 : ZMod 1243661033261) ^ 30 = (2 : ZMod 1243661033261) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 15 * (2 : ZMod 1243661033261) ^ 15 := by rw [pow_add]
          _ = 1073741824 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1243661033261) ^ 61 = 935309272116 := by
        calc
          (2 : ZMod 1243661033261) ^ 61 = (2 : ZMod 1243661033261) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 30 * (2 : ZMod 1243661033261) ^ 30) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 935309272116 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1243661033261) ^ 123 = 33748455962 := by
        calc
          (2 : ZMod 1243661033261) ^ 123 = (2 : ZMod 1243661033261) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 61 * (2 : ZMod 1243661033261) ^ 61) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 33748455962 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1243661033261) ^ 246 = 643469364245 := by
        calc
          (2 : ZMod 1243661033261) ^ 246 = (2 : ZMod 1243661033261) ^ (123 + 123) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 123 * (2 : ZMod 1243661033261) ^ 123 := by rw [pow_add]
          _ = 643469364245 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1243661033261) ^ 493 = 973604154525 := by
        calc
          (2 : ZMod 1243661033261) ^ 493 = (2 : ZMod 1243661033261) ^ (246 + 246 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 246 * (2 : ZMod 1243661033261) ^ 246) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 973604154525 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1243661033261) ^ 987 = 726930301417 := by
        calc
          (2 : ZMod 1243661033261) ^ 987 = (2 : ZMod 1243661033261) ^ (493 + 493 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 493 * (2 : ZMod 1243661033261) ^ 493) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 726930301417 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1243661033261) ^ 1975 = 885031268528 := by
        calc
          (2 : ZMod 1243661033261) ^ 1975 = (2 : ZMod 1243661033261) ^ (987 + 987 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 987 * (2 : ZMod 1243661033261) ^ 987) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 885031268528 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1243661033261) ^ 3950 = 1220498173399 := by
        calc
          (2 : ZMod 1243661033261) ^ 3950 = (2 : ZMod 1243661033261) ^ (1975 + 1975) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1975 * (2 : ZMod 1243661033261) ^ 1975 := by rw [pow_add]
          _ = 1220498173399 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1243661033261) ^ 7900 = 1031446883108 := by
        calc
          (2 : ZMod 1243661033261) ^ 7900 = (2 : ZMod 1243661033261) ^ (3950 + 3950) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 3950 * (2 : ZMod 1243661033261) ^ 3950 := by rw [pow_add]
          _ = 1031446883108 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1243661033261) ^ 15800 = 682161505417 := by
        calc
          (2 : ZMod 1243661033261) ^ 15800 = (2 : ZMod 1243661033261) ^ (7900 + 7900) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 7900 * (2 : ZMod 1243661033261) ^ 7900 := by rw [pow_add]
          _ = 682161505417 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1243661033261) ^ 31601 = 126954437171 := by
        calc
          (2 : ZMod 1243661033261) ^ 31601 = (2 : ZMod 1243661033261) ^ (15800 + 15800 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 15800 * (2 : ZMod 1243661033261) ^ 15800) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 126954437171 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1243661033261) ^ 63203 = 361970558048 := by
        calc
          (2 : ZMod 1243661033261) ^ 63203 = (2 : ZMod 1243661033261) ^ (31601 + 31601 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 31601 * (2 : ZMod 1243661033261) ^ 31601) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 361970558048 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1243661033261) ^ 126406 = 312802966620 := by
        calc
          (2 : ZMod 1243661033261) ^ 126406 = (2 : ZMod 1243661033261) ^ (63203 + 63203) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 63203 * (2 : ZMod 1243661033261) ^ 63203 := by rw [pow_add]
          _ = 312802966620 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1243661033261) ^ 252812 = 816982351485 := by
        calc
          (2 : ZMod 1243661033261) ^ 252812 = (2 : ZMod 1243661033261) ^ (126406 + 126406) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 126406 * (2 : ZMod 1243661033261) ^ 126406 := by rw [pow_add]
          _ = 816982351485 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1243661033261) ^ 505625 = 1134783053617 := by
        calc
          (2 : ZMod 1243661033261) ^ 505625 = (2 : ZMod 1243661033261) ^ (252812 + 252812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 252812 * (2 : ZMod 1243661033261) ^ 252812) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1134783053617 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1243661033261) ^ 1011251 = 416539628866 := by
        calc
          (2 : ZMod 1243661033261) ^ 1011251 = (2 : ZMod 1243661033261) ^ (505625 + 505625 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 505625 * (2 : ZMod 1243661033261) ^ 505625) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 416539628866 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1243661033261) ^ 2022502 = 37112163833 := by
        calc
          (2 : ZMod 1243661033261) ^ 2022502 = (2 : ZMod 1243661033261) ^ (1011251 + 1011251) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1011251 * (2 : ZMod 1243661033261) ^ 1011251 := by rw [pow_add]
          _ = 37112163833 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1243661033261) ^ 4045004 = 265459082152 := by
        calc
          (2 : ZMod 1243661033261) ^ 4045004 = (2 : ZMod 1243661033261) ^ (2022502 + 2022502) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 2022502 * (2 : ZMod 1243661033261) ^ 2022502 := by rw [pow_add]
          _ = 265459082152 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1243661033261) ^ 8090009 = 851854762706 := by
        calc
          (2 : ZMod 1243661033261) ^ 8090009 = (2 : ZMod 1243661033261) ^ (4045004 + 4045004 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 4045004 * (2 : ZMod 1243661033261) ^ 4045004) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 851854762706 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1243661033261) ^ 16180019 = 808417256697 := by
        calc
          (2 : ZMod 1243661033261) ^ 16180019 = (2 : ZMod 1243661033261) ^ (8090009 + 8090009 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 8090009 * (2 : ZMod 1243661033261) ^ 8090009) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 808417256697 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1243661033261) ^ 32360039 = 492809218760 := by
        calc
          (2 : ZMod 1243661033261) ^ 32360039 = (2 : ZMod 1243661033261) ^ (16180019 + 16180019 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 16180019 * (2 : ZMod 1243661033261) ^ 16180019) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 492809218760 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1243661033261) ^ 64720078 = 755642115680 := by
        calc
          (2 : ZMod 1243661033261) ^ 64720078 = (2 : ZMod 1243661033261) ^ (32360039 + 32360039) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 32360039 * (2 : ZMod 1243661033261) ^ 32360039 := by rw [pow_add]
          _ = 755642115680 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1243661033261) ^ 129440157 = 1129221616005 := by
        calc
          (2 : ZMod 1243661033261) ^ 129440157 = (2 : ZMod 1243661033261) ^ (64720078 + 64720078 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 64720078 * (2 : ZMod 1243661033261) ^ 64720078) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1129221616005 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 1243661033261) ^ 258880315 = 879007702672 := by
        calc
          (2 : ZMod 1243661033261) ^ 258880315 = (2 : ZMod 1243661033261) ^ (129440157 + 129440157 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 129440157 * (2 : ZMod 1243661033261) ^ 129440157) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 879007702672 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 1243661033261) ^ 517760630 = 735455025794 := by
        calc
          (2 : ZMod 1243661033261) ^ 517760630 = (2 : ZMod 1243661033261) ^ (258880315 + 258880315) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 258880315 * (2 : ZMod 1243661033261) ^ 258880315 := by rw [pow_add]
          _ = 735455025794 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 1243661033261) ^ 1035521260 = 1166957490879 := by
        calc
          (2 : ZMod 1243661033261) ^ 1035521260 = (2 : ZMod 1243661033261) ^ (517760630 + 517760630) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 517760630 * (2 : ZMod 1243661033261) ^ 517760630 := by rw [pow_add]
          _ = 1166957490879 := by rw [factor_2_28]; decide
      change (2 : ZMod 1243661033261) ^ 1035521260 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1243661033261) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1243661033261) ^ 2 = 4 := by
        calc
          (2 : ZMod 1243661033261) ^ 2 = (2 : ZMod 1243661033261) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1 * (2 : ZMod 1243661033261) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1243661033261) ^ 5 = 32 := by
        calc
          (2 : ZMod 1243661033261) ^ 5 = (2 : ZMod 1243661033261) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 2 * (2 : ZMod 1243661033261) ^ 2) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1243661033261) ^ 11 = 2048 := by
        calc
          (2 : ZMod 1243661033261) ^ 11 = (2 : ZMod 1243661033261) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 5 * (2 : ZMod 1243661033261) ^ 5) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1243661033261) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 1243661033261) ^ 23 = (2 : ZMod 1243661033261) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 11 * (2 : ZMod 1243661033261) ^ 11) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1243661033261) ^ 46 = 723726315048 := by
        calc
          (2 : ZMod 1243661033261) ^ 46 = (2 : ZMod 1243661033261) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 23 * (2 : ZMod 1243661033261) ^ 23 := by rw [pow_add]
          _ = 723726315048 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1243661033261) ^ 93 = 407508528100 := by
        calc
          (2 : ZMod 1243661033261) ^ 93 = (2 : ZMod 1243661033261) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 46 * (2 : ZMod 1243661033261) ^ 46) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 407508528100 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1243661033261) ^ 187 = 861610783258 := by
        calc
          (2 : ZMod 1243661033261) ^ 187 = (2 : ZMod 1243661033261) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 93 * (2 : ZMod 1243661033261) ^ 93) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 861610783258 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1243661033261) ^ 375 = 1015207135176 := by
        calc
          (2 : ZMod 1243661033261) ^ 375 = (2 : ZMod 1243661033261) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 187 * (2 : ZMod 1243661033261) ^ 187) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 1015207135176 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1243661033261) ^ 750 = 383162221247 := by
        calc
          (2 : ZMod 1243661033261) ^ 750 = (2 : ZMod 1243661033261) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 375 * (2 : ZMod 1243661033261) ^ 375 := by rw [pow_add]
          _ = 383162221247 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 1243661033261) ^ 1501 = 497899906472 := by
        calc
          (2 : ZMod 1243661033261) ^ 1501 = (2 : ZMod 1243661033261) ^ (750 + 750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 750 * (2 : ZMod 1243661033261) ^ 750) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 497899906472 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 1243661033261) ^ 3002 = 767112346912 := by
        calc
          (2 : ZMod 1243661033261) ^ 3002 = (2 : ZMod 1243661033261) ^ (1501 + 1501) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 1501 * (2 : ZMod 1243661033261) ^ 1501 := by rw [pow_add]
          _ = 767112346912 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 1243661033261) ^ 6005 = 415046797422 := by
        calc
          (2 : ZMod 1243661033261) ^ 6005 = (2 : ZMod 1243661033261) ^ (3002 + 3002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = ((2 : ZMod 1243661033261) ^ 3002 * (2 : ZMod 1243661033261) ^ 3002) * (2 : ZMod 1243661033261) := by rw [pow_succ, pow_add]
          _ = 415046797422 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 1243661033261) ^ 12010 = 1151060734403 := by
        calc
          (2 : ZMod 1243661033261) ^ 12010 = (2 : ZMod 1243661033261) ^ (6005 + 6005) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 6005 * (2 : ZMod 1243661033261) ^ 6005 := by rw [pow_add]
          _ = 1151060734403 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 1243661033261) ^ 24020 = 1052253840413 := by
        calc
          (2 : ZMod 1243661033261) ^ 24020 = (2 : ZMod 1243661033261) ^ (12010 + 12010) :=
            congrArg (fun n : ℕ => (2 : ZMod 1243661033261) ^ n) (by norm_num)
          _ = (2 : ZMod 1243661033261) ^ 12010 * (2 : ZMod 1243661033261) ^ 12010 := by rw [pow_add]
          _ = 1052253840413 := by rw [factor_3_13]; decide
      change (2 : ZMod 1243661033261) ^ 24020 ≠ 1
      rw [factor_3_14]
      decide

#print axioms prime_lucas_1243661033261

end TotientTailPeriodKiller
end Erdos249257
