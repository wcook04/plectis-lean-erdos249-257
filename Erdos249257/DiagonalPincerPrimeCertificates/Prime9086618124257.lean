import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_9086618124257 : Nat.Prime 9086618124257 := by
  apply lucas_primality 9086618124257 (3 : ZMod 9086618124257)
  ·
      have fermat_0 : (3 : ZMod 9086618124257) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 9086618124257) ^ 2 = 9 := by
        calc
          (3 : ZMod 9086618124257) ^ 2 = (3 : ZMod 9086618124257) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1 * (3 : ZMod 9086618124257) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 9086618124257) ^ 4 = 81 := by
        calc
          (3 : ZMod 9086618124257) ^ 4 = (3 : ZMod 9086618124257) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 2 * (3 : ZMod 9086618124257) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 9086618124257) ^ 8 = 6561 := by
        calc
          (3 : ZMod 9086618124257) ^ 8 = (3 : ZMod 9086618124257) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4 * (3 : ZMod 9086618124257) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 9086618124257) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 9086618124257) ^ 16 = (3 : ZMod 9086618124257) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 8 * (3 : ZMod 9086618124257) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 9086618124257) ^ 33 = 7136892634496 := by
        calc
          (3 : ZMod 9086618124257) ^ 33 = (3 : ZMod 9086618124257) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 16 * (3 : ZMod 9086618124257) ^ 16) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7136892634496 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 9086618124257) ^ 66 = 3570957471845 := by
        calc
          (3 : ZMod 9086618124257) ^ 66 = (3 : ZMod 9086618124257) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 33 * (3 : ZMod 9086618124257) ^ 33 := by rw [pow_add]
          _ = 3570957471845 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 9086618124257) ^ 132 = 1906107114534 := by
        calc
          (3 : ZMod 9086618124257) ^ 132 = (3 : ZMod 9086618124257) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 66 * (3 : ZMod 9086618124257) ^ 66 := by rw [pow_add]
          _ = 1906107114534 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 9086618124257) ^ 264 = 2896958183354 := by
        calc
          (3 : ZMod 9086618124257) ^ 264 = (3 : ZMod 9086618124257) ^ (132 + 132) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 132 * (3 : ZMod 9086618124257) ^ 132 := by rw [pow_add]
          _ = 2896958183354 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 9086618124257) ^ 528 = 2585110262868 := by
        calc
          (3 : ZMod 9086618124257) ^ 528 = (3 : ZMod 9086618124257) ^ (264 + 264) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 264 * (3 : ZMod 9086618124257) ^ 264 := by rw [pow_add]
          _ = 2585110262868 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 9086618124257) ^ 1057 = 6671519345582 := by
        calc
          (3 : ZMod 9086618124257) ^ 1057 = (3 : ZMod 9086618124257) ^ (528 + 528 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 528 * (3 : ZMod 9086618124257) ^ 528) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6671519345582 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 9086618124257) ^ 2115 = 7285156873767 := by
        calc
          (3 : ZMod 9086618124257) ^ 2115 = (3 : ZMod 9086618124257) ^ (1057 + 1057 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 1057 * (3 : ZMod 9086618124257) ^ 1057) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7285156873767 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 9086618124257) ^ 4231 = 4172352918873 := by
        calc
          (3 : ZMod 9086618124257) ^ 4231 = (3 : ZMod 9086618124257) ^ (2115 + 2115 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 2115 * (3 : ZMod 9086618124257) ^ 2115) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4172352918873 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 9086618124257) ^ 8462 = 8050161599148 := by
        calc
          (3 : ZMod 9086618124257) ^ 8462 = (3 : ZMod 9086618124257) ^ (4231 + 4231) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4231 * (3 : ZMod 9086618124257) ^ 4231 := by rw [pow_add]
          _ = 8050161599148 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 9086618124257) ^ 16925 = 3477001932443 := by
        calc
          (3 : ZMod 9086618124257) ^ 16925 = (3 : ZMod 9086618124257) ^ (8462 + 8462 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 8462 * (3 : ZMod 9086618124257) ^ 8462) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 3477001932443 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 9086618124257) ^ 33850 = 801566376661 := by
        calc
          (3 : ZMod 9086618124257) ^ 33850 = (3 : ZMod 9086618124257) ^ (16925 + 16925) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 16925 * (3 : ZMod 9086618124257) ^ 16925 := by rw [pow_add]
          _ = 801566376661 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 9086618124257) ^ 67700 = 4896868915154 := by
        calc
          (3 : ZMod 9086618124257) ^ 67700 = (3 : ZMod 9086618124257) ^ (33850 + 33850) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 33850 * (3 : ZMod 9086618124257) ^ 33850 := by rw [pow_add]
          _ = 4896868915154 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 9086618124257) ^ 135401 = 4945701369152 := by
        calc
          (3 : ZMod 9086618124257) ^ 135401 = (3 : ZMod 9086618124257) ^ (67700 + 67700 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 67700 * (3 : ZMod 9086618124257) ^ 67700) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4945701369152 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 9086618124257) ^ 270802 = 2194967960675 := by
        calc
          (3 : ZMod 9086618124257) ^ 270802 = (3 : ZMod 9086618124257) ^ (135401 + 135401) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 135401 * (3 : ZMod 9086618124257) ^ 135401 := by rw [pow_add]
          _ = 2194967960675 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 9086618124257) ^ 541604 = 65838790848 := by
        calc
          (3 : ZMod 9086618124257) ^ 541604 = (3 : ZMod 9086618124257) ^ (270802 + 270802) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 270802 * (3 : ZMod 9086618124257) ^ 270802 := by rw [pow_add]
          _ = 65838790848 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 9086618124257) ^ 1083209 = 4592243419371 := by
        calc
          (3 : ZMod 9086618124257) ^ 1083209 = (3 : ZMod 9086618124257) ^ (541604 + 541604 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 541604 * (3 : ZMod 9086618124257) ^ 541604) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4592243419371 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 9086618124257) ^ 2166418 = 3025096530375 := by
        calc
          (3 : ZMod 9086618124257) ^ 2166418 = (3 : ZMod 9086618124257) ^ (1083209 + 1083209) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1083209 * (3 : ZMod 9086618124257) ^ 1083209 := by rw [pow_add]
          _ = 3025096530375 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 9086618124257) ^ 4332837 = 4074161018436 := by
        calc
          (3 : ZMod 9086618124257) ^ 4332837 = (3 : ZMod 9086618124257) ^ (2166418 + 2166418 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 2166418 * (3 : ZMod 9086618124257) ^ 2166418) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4074161018436 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 9086618124257) ^ 8665674 = 6750014329134 := by
        calc
          (3 : ZMod 9086618124257) ^ 8665674 = (3 : ZMod 9086618124257) ^ (4332837 + 4332837) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4332837 * (3 : ZMod 9086618124257) ^ 4332837 := by rw [pow_add]
          _ = 6750014329134 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 9086618124257) ^ 17331348 = 6232147534369 := by
        calc
          (3 : ZMod 9086618124257) ^ 17331348 = (3 : ZMod 9086618124257) ^ (8665674 + 8665674) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 8665674 * (3 : ZMod 9086618124257) ^ 8665674 := by rw [pow_add]
          _ = 6232147534369 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 9086618124257) ^ 34662697 = 1948549925863 := by
        calc
          (3 : ZMod 9086618124257) ^ 34662697 = (3 : ZMod 9086618124257) ^ (17331348 + 17331348 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 17331348 * (3 : ZMod 9086618124257) ^ 17331348) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 1948549925863 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 9086618124257) ^ 69325394 = 7100931164900 := by
        calc
          (3 : ZMod 9086618124257) ^ 69325394 = (3 : ZMod 9086618124257) ^ (34662697 + 34662697) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 34662697 * (3 : ZMod 9086618124257) ^ 34662697 := by rw [pow_add]
          _ = 7100931164900 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 9086618124257) ^ 138650789 = 7077852349770 := by
        calc
          (3 : ZMod 9086618124257) ^ 138650789 = (3 : ZMod 9086618124257) ^ (69325394 + 69325394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 69325394 * (3 : ZMod 9086618124257) ^ 69325394) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7077852349770 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 9086618124257) ^ 277301578 = 8633403933148 := by
        calc
          (3 : ZMod 9086618124257) ^ 277301578 = (3 : ZMod 9086618124257) ^ (138650789 + 138650789) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 138650789 * (3 : ZMod 9086618124257) ^ 138650789 := by rw [pow_add]
          _ = 8633403933148 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 9086618124257) ^ 554603156 = 7491597852601 := by
        calc
          (3 : ZMod 9086618124257) ^ 554603156 = (3 : ZMod 9086618124257) ^ (277301578 + 277301578) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 277301578 * (3 : ZMod 9086618124257) ^ 277301578 := by rw [pow_add]
          _ = 7491597852601 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 9086618124257) ^ 1109206313 = 7041882943031 := by
        calc
          (3 : ZMod 9086618124257) ^ 1109206313 = (3 : ZMod 9086618124257) ^ (554603156 + 554603156 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 554603156 * (3 : ZMod 9086618124257) ^ 554603156) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7041882943031 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 9086618124257) ^ 2218412627 = 515523402518 := by
        calc
          (3 : ZMod 9086618124257) ^ 2218412627 = (3 : ZMod 9086618124257) ^ (1109206313 + 1109206313 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 1109206313 * (3 : ZMod 9086618124257) ^ 1109206313) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 515523402518 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 9086618124257) ^ 4436825255 = 6813649709098 := by
        calc
          (3 : ZMod 9086618124257) ^ 4436825255 = (3 : ZMod 9086618124257) ^ (2218412627 + 2218412627 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 2218412627 * (3 : ZMod 9086618124257) ^ 2218412627) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6813649709098 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 9086618124257) ^ 8873650511 = 4516049588898 := by
        calc
          (3 : ZMod 9086618124257) ^ 8873650511 = (3 : ZMod 9086618124257) ^ (4436825255 + 4436825255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 4436825255 * (3 : ZMod 9086618124257) ^ 4436825255) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4516049588898 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 9086618124257) ^ 17747301023 = 836173773402 := by
        calc
          (3 : ZMod 9086618124257) ^ 17747301023 = (3 : ZMod 9086618124257) ^ (8873650511 + 8873650511 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 8873650511 * (3 : ZMod 9086618124257) ^ 8873650511) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 836173773402 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 9086618124257) ^ 35494602047 = 7668646281236 := by
        calc
          (3 : ZMod 9086618124257) ^ 35494602047 = (3 : ZMod 9086618124257) ^ (17747301023 + 17747301023 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 17747301023 * (3 : ZMod 9086618124257) ^ 17747301023) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7668646281236 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 9086618124257) ^ 70989204095 = 4471470104428 := by
        calc
          (3 : ZMod 9086618124257) ^ 70989204095 = (3 : ZMod 9086618124257) ^ (35494602047 + 35494602047 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 35494602047 * (3 : ZMod 9086618124257) ^ 35494602047) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4471470104428 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 9086618124257) ^ 141978408191 = 7132053416175 := by
        calc
          (3 : ZMod 9086618124257) ^ 141978408191 = (3 : ZMod 9086618124257) ^ (70989204095 + 70989204095 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 70989204095 * (3 : ZMod 9086618124257) ^ 70989204095) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7132053416175 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 9086618124257) ^ 283956816383 = 4750165917157 := by
        calc
          (3 : ZMod 9086618124257) ^ 283956816383 = (3 : ZMod 9086618124257) ^ (141978408191 + 141978408191 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 141978408191 * (3 : ZMod 9086618124257) ^ 141978408191) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4750165917157 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 9086618124257) ^ 567913632766 = 8204878397170 := by
        calc
          (3 : ZMod 9086618124257) ^ 567913632766 = (3 : ZMod 9086618124257) ^ (283956816383 + 283956816383) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 283956816383 * (3 : ZMod 9086618124257) ^ 283956816383 := by rw [pow_add]
          _ = 8204878397170 := by rw [fermat_38]; decide
      have fermat_40 : (3 : ZMod 9086618124257) ^ 1135827265532 = 3102626182066 := by
        calc
          (3 : ZMod 9086618124257) ^ 1135827265532 = (3 : ZMod 9086618124257) ^ (567913632766 + 567913632766) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 567913632766 * (3 : ZMod 9086618124257) ^ 567913632766 := by rw [pow_add]
          _ = 3102626182066 := by rw [fermat_39]; decide
      have fermat_41 : (3 : ZMod 9086618124257) ^ 2271654531064 = 5981623534225 := by
        calc
          (3 : ZMod 9086618124257) ^ 2271654531064 = (3 : ZMod 9086618124257) ^ (1135827265532 + 1135827265532) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1135827265532 * (3 : ZMod 9086618124257) ^ 1135827265532 := by rw [pow_add]
          _ = 5981623534225 := by rw [fermat_40]; decide
      have fermat_42 : (3 : ZMod 9086618124257) ^ 4543309062128 = 9086618124256 := by
        calc
          (3 : ZMod 9086618124257) ^ 4543309062128 = (3 : ZMod 9086618124257) ^ (2271654531064 + 2271654531064) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 2271654531064 * (3 : ZMod 9086618124257) ^ 2271654531064 := by rw [pow_add]
          _ = 9086618124256 := by rw [fermat_41]; decide
      have fermat_43 : (3 : ZMod 9086618124257) ^ 9086618124256 = 1 := by
        calc
          (3 : ZMod 9086618124257) ^ 9086618124256 = (3 : ZMod 9086618124257) ^ (4543309062128 + 4543309062128) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4543309062128 * (3 : ZMod 9086618124257) ^ 4543309062128 := by rw [pow_add]
          _ = 1 := by rw [fermat_42]; decide
      simpa using fermat_43
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (8923, 1), (31823021, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (8923, 1), (31823021, 1)] : List FactorBlock).map factorBlockValue).prod = 9086618124257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 9086618124257) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 9086618124257) ^ 2 = 9 := by
        calc
          (3 : ZMod 9086618124257) ^ 2 = (3 : ZMod 9086618124257) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1 * (3 : ZMod 9086618124257) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 9086618124257) ^ 4 = 81 := by
        calc
          (3 : ZMod 9086618124257) ^ 4 = (3 : ZMod 9086618124257) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 2 * (3 : ZMod 9086618124257) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 9086618124257) ^ 8 = 6561 := by
        calc
          (3 : ZMod 9086618124257) ^ 8 = (3 : ZMod 9086618124257) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4 * (3 : ZMod 9086618124257) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 9086618124257) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 9086618124257) ^ 16 = (3 : ZMod 9086618124257) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 8 * (3 : ZMod 9086618124257) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 9086618124257) ^ 33 = 7136892634496 := by
        calc
          (3 : ZMod 9086618124257) ^ 33 = (3 : ZMod 9086618124257) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 16 * (3 : ZMod 9086618124257) ^ 16) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7136892634496 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 9086618124257) ^ 66 = 3570957471845 := by
        calc
          (3 : ZMod 9086618124257) ^ 66 = (3 : ZMod 9086618124257) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 33 * (3 : ZMod 9086618124257) ^ 33 := by rw [pow_add]
          _ = 3570957471845 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 9086618124257) ^ 132 = 1906107114534 := by
        calc
          (3 : ZMod 9086618124257) ^ 132 = (3 : ZMod 9086618124257) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 66 * (3 : ZMod 9086618124257) ^ 66 := by rw [pow_add]
          _ = 1906107114534 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 9086618124257) ^ 264 = 2896958183354 := by
        calc
          (3 : ZMod 9086618124257) ^ 264 = (3 : ZMod 9086618124257) ^ (132 + 132) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 132 * (3 : ZMod 9086618124257) ^ 132 := by rw [pow_add]
          _ = 2896958183354 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 9086618124257) ^ 528 = 2585110262868 := by
        calc
          (3 : ZMod 9086618124257) ^ 528 = (3 : ZMod 9086618124257) ^ (264 + 264) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 264 * (3 : ZMod 9086618124257) ^ 264 := by rw [pow_add]
          _ = 2585110262868 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 9086618124257) ^ 1057 = 6671519345582 := by
        calc
          (3 : ZMod 9086618124257) ^ 1057 = (3 : ZMod 9086618124257) ^ (528 + 528 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 528 * (3 : ZMod 9086618124257) ^ 528) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6671519345582 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 9086618124257) ^ 2115 = 7285156873767 := by
        calc
          (3 : ZMod 9086618124257) ^ 2115 = (3 : ZMod 9086618124257) ^ (1057 + 1057 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 1057 * (3 : ZMod 9086618124257) ^ 1057) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7285156873767 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 9086618124257) ^ 4231 = 4172352918873 := by
        calc
          (3 : ZMod 9086618124257) ^ 4231 = (3 : ZMod 9086618124257) ^ (2115 + 2115 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 2115 * (3 : ZMod 9086618124257) ^ 2115) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4172352918873 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 9086618124257) ^ 8462 = 8050161599148 := by
        calc
          (3 : ZMod 9086618124257) ^ 8462 = (3 : ZMod 9086618124257) ^ (4231 + 4231) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4231 * (3 : ZMod 9086618124257) ^ 4231 := by rw [pow_add]
          _ = 8050161599148 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 9086618124257) ^ 16925 = 3477001932443 := by
        calc
          (3 : ZMod 9086618124257) ^ 16925 = (3 : ZMod 9086618124257) ^ (8462 + 8462 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 8462 * (3 : ZMod 9086618124257) ^ 8462) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 3477001932443 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 9086618124257) ^ 33850 = 801566376661 := by
        calc
          (3 : ZMod 9086618124257) ^ 33850 = (3 : ZMod 9086618124257) ^ (16925 + 16925) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 16925 * (3 : ZMod 9086618124257) ^ 16925 := by rw [pow_add]
          _ = 801566376661 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 9086618124257) ^ 67700 = 4896868915154 := by
        calc
          (3 : ZMod 9086618124257) ^ 67700 = (3 : ZMod 9086618124257) ^ (33850 + 33850) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 33850 * (3 : ZMod 9086618124257) ^ 33850 := by rw [pow_add]
          _ = 4896868915154 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 9086618124257) ^ 135401 = 4945701369152 := by
        calc
          (3 : ZMod 9086618124257) ^ 135401 = (3 : ZMod 9086618124257) ^ (67700 + 67700 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 67700 * (3 : ZMod 9086618124257) ^ 67700) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4945701369152 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 9086618124257) ^ 270802 = 2194967960675 := by
        calc
          (3 : ZMod 9086618124257) ^ 270802 = (3 : ZMod 9086618124257) ^ (135401 + 135401) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 135401 * (3 : ZMod 9086618124257) ^ 135401 := by rw [pow_add]
          _ = 2194967960675 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 9086618124257) ^ 541604 = 65838790848 := by
        calc
          (3 : ZMod 9086618124257) ^ 541604 = (3 : ZMod 9086618124257) ^ (270802 + 270802) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 270802 * (3 : ZMod 9086618124257) ^ 270802 := by rw [pow_add]
          _ = 65838790848 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 9086618124257) ^ 1083209 = 4592243419371 := by
        calc
          (3 : ZMod 9086618124257) ^ 1083209 = (3 : ZMod 9086618124257) ^ (541604 + 541604 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 541604 * (3 : ZMod 9086618124257) ^ 541604) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4592243419371 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 9086618124257) ^ 2166418 = 3025096530375 := by
        calc
          (3 : ZMod 9086618124257) ^ 2166418 = (3 : ZMod 9086618124257) ^ (1083209 + 1083209) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1083209 * (3 : ZMod 9086618124257) ^ 1083209 := by rw [pow_add]
          _ = 3025096530375 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 9086618124257) ^ 4332837 = 4074161018436 := by
        calc
          (3 : ZMod 9086618124257) ^ 4332837 = (3 : ZMod 9086618124257) ^ (2166418 + 2166418 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 2166418 * (3 : ZMod 9086618124257) ^ 2166418) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4074161018436 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 9086618124257) ^ 8665674 = 6750014329134 := by
        calc
          (3 : ZMod 9086618124257) ^ 8665674 = (3 : ZMod 9086618124257) ^ (4332837 + 4332837) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4332837 * (3 : ZMod 9086618124257) ^ 4332837 := by rw [pow_add]
          _ = 6750014329134 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 9086618124257) ^ 17331348 = 6232147534369 := by
        calc
          (3 : ZMod 9086618124257) ^ 17331348 = (3 : ZMod 9086618124257) ^ (8665674 + 8665674) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 8665674 * (3 : ZMod 9086618124257) ^ 8665674 := by rw [pow_add]
          _ = 6232147534369 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 9086618124257) ^ 34662697 = 1948549925863 := by
        calc
          (3 : ZMod 9086618124257) ^ 34662697 = (3 : ZMod 9086618124257) ^ (17331348 + 17331348 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 17331348 * (3 : ZMod 9086618124257) ^ 17331348) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 1948549925863 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 9086618124257) ^ 69325394 = 7100931164900 := by
        calc
          (3 : ZMod 9086618124257) ^ 69325394 = (3 : ZMod 9086618124257) ^ (34662697 + 34662697) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 34662697 * (3 : ZMod 9086618124257) ^ 34662697 := by rw [pow_add]
          _ = 7100931164900 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 9086618124257) ^ 138650789 = 7077852349770 := by
        calc
          (3 : ZMod 9086618124257) ^ 138650789 = (3 : ZMod 9086618124257) ^ (69325394 + 69325394 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 69325394 * (3 : ZMod 9086618124257) ^ 69325394) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7077852349770 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 9086618124257) ^ 277301578 = 8633403933148 := by
        calc
          (3 : ZMod 9086618124257) ^ 277301578 = (3 : ZMod 9086618124257) ^ (138650789 + 138650789) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 138650789 * (3 : ZMod 9086618124257) ^ 138650789 := by rw [pow_add]
          _ = 8633403933148 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 9086618124257) ^ 554603156 = 7491597852601 := by
        calc
          (3 : ZMod 9086618124257) ^ 554603156 = (3 : ZMod 9086618124257) ^ (277301578 + 277301578) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 277301578 * (3 : ZMod 9086618124257) ^ 277301578 := by rw [pow_add]
          _ = 7491597852601 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 9086618124257) ^ 1109206313 = 7041882943031 := by
        calc
          (3 : ZMod 9086618124257) ^ 1109206313 = (3 : ZMod 9086618124257) ^ (554603156 + 554603156 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 554603156 * (3 : ZMod 9086618124257) ^ 554603156) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7041882943031 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 9086618124257) ^ 2218412627 = 515523402518 := by
        calc
          (3 : ZMod 9086618124257) ^ 2218412627 = (3 : ZMod 9086618124257) ^ (1109206313 + 1109206313 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 1109206313 * (3 : ZMod 9086618124257) ^ 1109206313) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 515523402518 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 9086618124257) ^ 4436825255 = 6813649709098 := by
        calc
          (3 : ZMod 9086618124257) ^ 4436825255 = (3 : ZMod 9086618124257) ^ (2218412627 + 2218412627 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 2218412627 * (3 : ZMod 9086618124257) ^ 2218412627) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6813649709098 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 9086618124257) ^ 8873650511 = 4516049588898 := by
        calc
          (3 : ZMod 9086618124257) ^ 8873650511 = (3 : ZMod 9086618124257) ^ (4436825255 + 4436825255 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 4436825255 * (3 : ZMod 9086618124257) ^ 4436825255) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4516049588898 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 9086618124257) ^ 17747301023 = 836173773402 := by
        calc
          (3 : ZMod 9086618124257) ^ 17747301023 = (3 : ZMod 9086618124257) ^ (8873650511 + 8873650511 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 8873650511 * (3 : ZMod 9086618124257) ^ 8873650511) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 836173773402 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 9086618124257) ^ 35494602047 = 7668646281236 := by
        calc
          (3 : ZMod 9086618124257) ^ 35494602047 = (3 : ZMod 9086618124257) ^ (17747301023 + 17747301023 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 17747301023 * (3 : ZMod 9086618124257) ^ 17747301023) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7668646281236 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 9086618124257) ^ 70989204095 = 4471470104428 := by
        calc
          (3 : ZMod 9086618124257) ^ 70989204095 = (3 : ZMod 9086618124257) ^ (35494602047 + 35494602047 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 35494602047 * (3 : ZMod 9086618124257) ^ 35494602047) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4471470104428 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 9086618124257) ^ 141978408191 = 7132053416175 := by
        calc
          (3 : ZMod 9086618124257) ^ 141978408191 = (3 : ZMod 9086618124257) ^ (70989204095 + 70989204095 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 70989204095 * (3 : ZMod 9086618124257) ^ 70989204095) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 7132053416175 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 9086618124257) ^ 283956816383 = 4750165917157 := by
        calc
          (3 : ZMod 9086618124257) ^ 283956816383 = (3 : ZMod 9086618124257) ^ (141978408191 + 141978408191 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 141978408191 * (3 : ZMod 9086618124257) ^ 141978408191) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4750165917157 := by rw [factor_0_37]; decide
      have factor_0_39 : (3 : ZMod 9086618124257) ^ 567913632766 = 8204878397170 := by
        calc
          (3 : ZMod 9086618124257) ^ 567913632766 = (3 : ZMod 9086618124257) ^ (283956816383 + 283956816383) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 283956816383 * (3 : ZMod 9086618124257) ^ 283956816383 := by rw [pow_add]
          _ = 8204878397170 := by rw [factor_0_38]; decide
      have factor_0_40 : (3 : ZMod 9086618124257) ^ 1135827265532 = 3102626182066 := by
        calc
          (3 : ZMod 9086618124257) ^ 1135827265532 = (3 : ZMod 9086618124257) ^ (567913632766 + 567913632766) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 567913632766 * (3 : ZMod 9086618124257) ^ 567913632766 := by rw [pow_add]
          _ = 3102626182066 := by rw [factor_0_39]; decide
      have factor_0_41 : (3 : ZMod 9086618124257) ^ 2271654531064 = 5981623534225 := by
        calc
          (3 : ZMod 9086618124257) ^ 2271654531064 = (3 : ZMod 9086618124257) ^ (1135827265532 + 1135827265532) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1135827265532 * (3 : ZMod 9086618124257) ^ 1135827265532 := by rw [pow_add]
          _ = 5981623534225 := by rw [factor_0_40]; decide
      have factor_0_42 : (3 : ZMod 9086618124257) ^ 4543309062128 = 9086618124256 := by
        calc
          (3 : ZMod 9086618124257) ^ 4543309062128 = (3 : ZMod 9086618124257) ^ (2271654531064 + 2271654531064) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 2271654531064 * (3 : ZMod 9086618124257) ^ 2271654531064 := by rw [pow_add]
          _ = 9086618124256 := by rw [factor_0_41]; decide
      change (3 : ZMod 9086618124257) ^ 4543309062128 ≠ 1
      rw [factor_0_42]
      decide
    ·
      have factor_1_0 : (3 : ZMod 9086618124257) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 9086618124257) ^ 3 = 27 := by
        calc
          (3 : ZMod 9086618124257) ^ 3 = (3 : ZMod 9086618124257) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 1 * (3 : ZMod 9086618124257) ^ 1) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 9086618124257) ^ 7 = 2187 := by
        calc
          (3 : ZMod 9086618124257) ^ 7 = (3 : ZMod 9086618124257) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 3 * (3 : ZMod 9086618124257) ^ 3) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 9086618124257) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 9086618124257) ^ 15 = (3 : ZMod 9086618124257) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 7 * (3 : ZMod 9086618124257) ^ 7) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 9086618124257) ^ 30 = 5985533360995 := by
        calc
          (3 : ZMod 9086618124257) ^ 30 = (3 : ZMod 9086618124257) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 15 * (3 : ZMod 9086618124257) ^ 15 := by rw [pow_add]
          _ = 5985533360995 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 9086618124257) ^ 60 = 403762328461 := by
        calc
          (3 : ZMod 9086618124257) ^ 60 = (3 : ZMod 9086618124257) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 30 * (3 : ZMod 9086618124257) ^ 30 := by rw [pow_add]
          _ = 403762328461 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 9086618124257) ^ 121 = 6907957960085 := by
        calc
          (3 : ZMod 9086618124257) ^ 121 = (3 : ZMod 9086618124257) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 60 * (3 : ZMod 9086618124257) ^ 60) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6907957960085 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 9086618124257) ^ 242 = 7117282074311 := by
        calc
          (3 : ZMod 9086618124257) ^ 242 = (3 : ZMod 9086618124257) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 121 * (3 : ZMod 9086618124257) ^ 121 := by rw [pow_add]
          _ = 7117282074311 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 9086618124257) ^ 485 = 1698701472716 := by
        calc
          (3 : ZMod 9086618124257) ^ 485 = (3 : ZMod 9086618124257) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 242 * (3 : ZMod 9086618124257) ^ 242) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 1698701472716 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 9086618124257) ^ 971 = 6428461937609 := by
        calc
          (3 : ZMod 9086618124257) ^ 971 = (3 : ZMod 9086618124257) ^ (485 + 485 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 485 * (3 : ZMod 9086618124257) ^ 485) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6428461937609 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 9086618124257) ^ 1942 = 824159059760 := by
        calc
          (3 : ZMod 9086618124257) ^ 1942 = (3 : ZMod 9086618124257) ^ (971 + 971) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 971 * (3 : ZMod 9086618124257) ^ 971 := by rw [pow_add]
          _ = 824159059760 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 9086618124257) ^ 3884 = 2774218626444 := by
        calc
          (3 : ZMod 9086618124257) ^ 3884 = (3 : ZMod 9086618124257) ^ (1942 + 1942) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1942 * (3 : ZMod 9086618124257) ^ 1942 := by rw [pow_add]
          _ = 2774218626444 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 9086618124257) ^ 7769 = 4095178553375 := by
        calc
          (3 : ZMod 9086618124257) ^ 7769 = (3 : ZMod 9086618124257) ^ (3884 + 3884 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 3884 * (3 : ZMod 9086618124257) ^ 3884) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 4095178553375 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 9086618124257) ^ 15538 = 5811015939427 := by
        calc
          (3 : ZMod 9086618124257) ^ 15538 = (3 : ZMod 9086618124257) ^ (7769 + 7769) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 7769 * (3 : ZMod 9086618124257) ^ 7769 := by rw [pow_add]
          _ = 5811015939427 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 9086618124257) ^ 31077 = 1382621035098 := by
        calc
          (3 : ZMod 9086618124257) ^ 31077 = (3 : ZMod 9086618124257) ^ (15538 + 15538 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 15538 * (3 : ZMod 9086618124257) ^ 15538) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 1382621035098 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 9086618124257) ^ 62154 = 3325194278109 := by
        calc
          (3 : ZMod 9086618124257) ^ 62154 = (3 : ZMod 9086618124257) ^ (31077 + 31077) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 31077 * (3 : ZMod 9086618124257) ^ 31077 := by rw [pow_add]
          _ = 3325194278109 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 9086618124257) ^ 124308 = 2475268196755 := by
        calc
          (3 : ZMod 9086618124257) ^ 124308 = (3 : ZMod 9086618124257) ^ (62154 + 62154) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 62154 * (3 : ZMod 9086618124257) ^ 62154 := by rw [pow_add]
          _ = 2475268196755 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 9086618124257) ^ 248617 = 6882031458811 := by
        calc
          (3 : ZMod 9086618124257) ^ 248617 = (3 : ZMod 9086618124257) ^ (124308 + 124308 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 124308 * (3 : ZMod 9086618124257) ^ 124308) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6882031458811 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 9086618124257) ^ 497234 = 4368467525467 := by
        calc
          (3 : ZMod 9086618124257) ^ 497234 = (3 : ZMod 9086618124257) ^ (248617 + 248617) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 248617 * (3 : ZMod 9086618124257) ^ 248617 := by rw [pow_add]
          _ = 4368467525467 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 9086618124257) ^ 994469 = 6504977139125 := by
        calc
          (3 : ZMod 9086618124257) ^ 994469 = (3 : ZMod 9086618124257) ^ (497234 + 497234 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 497234 * (3 : ZMod 9086618124257) ^ 497234) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6504977139125 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 9086618124257) ^ 1988938 = 4077233429522 := by
        calc
          (3 : ZMod 9086618124257) ^ 1988938 = (3 : ZMod 9086618124257) ^ (994469 + 994469) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 994469 * (3 : ZMod 9086618124257) ^ 994469 := by rw [pow_add]
          _ = 4077233429522 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 9086618124257) ^ 3977877 = 3482389254260 := by
        calc
          (3 : ZMod 9086618124257) ^ 3977877 = (3 : ZMod 9086618124257) ^ (1988938 + 1988938 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 1988938 * (3 : ZMod 9086618124257) ^ 1988938) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 3482389254260 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 9086618124257) ^ 7955755 = 1845857992644 := by
        calc
          (3 : ZMod 9086618124257) ^ 7955755 = (3 : ZMod 9086618124257) ^ (3977877 + 3977877 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 3977877 * (3 : ZMod 9086618124257) ^ 3977877) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 1845857992644 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 9086618124257) ^ 15911510 = 5693606566007 := by
        calc
          (3 : ZMod 9086618124257) ^ 15911510 = (3 : ZMod 9086618124257) ^ (7955755 + 7955755) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 7955755 * (3 : ZMod 9086618124257) ^ 7955755 := by rw [pow_add]
          _ = 5693606566007 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 9086618124257) ^ 31823021 = 8495290249542 := by
        calc
          (3 : ZMod 9086618124257) ^ 31823021 = (3 : ZMod 9086618124257) ^ (15911510 + 15911510 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 15911510 * (3 : ZMod 9086618124257) ^ 15911510) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 8495290249542 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 9086618124257) ^ 63646042 = 1054025478012 := by
        calc
          (3 : ZMod 9086618124257) ^ 63646042 = (3 : ZMod 9086618124257) ^ (31823021 + 31823021) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 31823021 * (3 : ZMod 9086618124257) ^ 31823021 := by rw [pow_add]
          _ = 1054025478012 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 9086618124257) ^ 127292084 = 1264029809583 := by
        calc
          (3 : ZMod 9086618124257) ^ 127292084 = (3 : ZMod 9086618124257) ^ (63646042 + 63646042) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 63646042 * (3 : ZMod 9086618124257) ^ 63646042 := by rw [pow_add]
          _ = 1264029809583 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 9086618124257) ^ 254584168 = 2869978928278 := by
        calc
          (3 : ZMod 9086618124257) ^ 254584168 = (3 : ZMod 9086618124257) ^ (127292084 + 127292084) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 127292084 * (3 : ZMod 9086618124257) ^ 127292084 := by rw [pow_add]
          _ = 2869978928278 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 9086618124257) ^ 509168336 = 7654964989687 := by
        calc
          (3 : ZMod 9086618124257) ^ 509168336 = (3 : ZMod 9086618124257) ^ (254584168 + 254584168) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 254584168 * (3 : ZMod 9086618124257) ^ 254584168 := by rw [pow_add]
          _ = 7654964989687 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 9086618124257) ^ 1018336672 = 7587087110108 := by
        calc
          (3 : ZMod 9086618124257) ^ 1018336672 = (3 : ZMod 9086618124257) ^ (509168336 + 509168336) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 509168336 * (3 : ZMod 9086618124257) ^ 509168336 := by rw [pow_add]
          _ = 7587087110108 := by rw [factor_1_28]; decide
      change (3 : ZMod 9086618124257) ^ 1018336672 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (3 : ZMod 9086618124257) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 9086618124257) ^ 2 = 9 := by
        calc
          (3 : ZMod 9086618124257) ^ 2 = (3 : ZMod 9086618124257) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1 * (3 : ZMod 9086618124257) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 9086618124257) ^ 4 = 81 := by
        calc
          (3 : ZMod 9086618124257) ^ 4 = (3 : ZMod 9086618124257) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 2 * (3 : ZMod 9086618124257) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 9086618124257) ^ 8 = 6561 := by
        calc
          (3 : ZMod 9086618124257) ^ 8 = (3 : ZMod 9086618124257) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 4 * (3 : ZMod 9086618124257) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 9086618124257) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 9086618124257) ^ 17 = (3 : ZMod 9086618124257) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 8 * (3 : ZMod 9086618124257) ^ 8) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 9086618124257) ^ 34 = 3237441654974 := by
        calc
          (3 : ZMod 9086618124257) ^ 34 = (3 : ZMod 9086618124257) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 17 * (3 : ZMod 9086618124257) ^ 17 := by rw [pow_add]
          _ = 3237441654974 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 9086618124257) ^ 69 = 5549670497245 := by
        calc
          (3 : ZMod 9086618124257) ^ 69 = (3 : ZMod 9086618124257) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 34 * (3 : ZMod 9086618124257) ^ 34) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 5549670497245 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 9086618124257) ^ 139 = 6985158576152 := by
        calc
          (3 : ZMod 9086618124257) ^ 139 = (3 : ZMod 9086618124257) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 69 * (3 : ZMod 9086618124257) ^ 69) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6985158576152 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 9086618124257) ^ 278 = 4420252738324 := by
        calc
          (3 : ZMod 9086618124257) ^ 278 = (3 : ZMod 9086618124257) ^ (139 + 139) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 139 * (3 : ZMod 9086618124257) ^ 139 := by rw [pow_add]
          _ = 4420252738324 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 9086618124257) ^ 557 = 6838464228755 := by
        calc
          (3 : ZMod 9086618124257) ^ 557 = (3 : ZMod 9086618124257) ^ (278 + 278 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 278 * (3 : ZMod 9086618124257) ^ 278) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 6838464228755 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 9086618124257) ^ 1115 = 3691705920123 := by
        calc
          (3 : ZMod 9086618124257) ^ 1115 = (3 : ZMod 9086618124257) ^ (557 + 557 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 557 * (3 : ZMod 9086618124257) ^ 557) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 3691705920123 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 9086618124257) ^ 2230 = 5518755995049 := by
        calc
          (3 : ZMod 9086618124257) ^ 2230 = (3 : ZMod 9086618124257) ^ (1115 + 1115) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 1115 * (3 : ZMod 9086618124257) ^ 1115 := by rw [pow_add]
          _ = 5518755995049 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 9086618124257) ^ 4461 = 5208282415533 := by
        calc
          (3 : ZMod 9086618124257) ^ 4461 = (3 : ZMod 9086618124257) ^ (2230 + 2230 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 2230 * (3 : ZMod 9086618124257) ^ 2230) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 5208282415533 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 9086618124257) ^ 8923 = 1420173084602 := by
        calc
          (3 : ZMod 9086618124257) ^ 8923 = (3 : ZMod 9086618124257) ^ (4461 + 4461 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = ((3 : ZMod 9086618124257) ^ 4461 * (3 : ZMod 9086618124257) ^ 4461) * (3 : ZMod 9086618124257) := by rw [pow_succ, pow_add]
          _ = 1420173084602 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 9086618124257) ^ 17846 = 2565036692860 := by
        calc
          (3 : ZMod 9086618124257) ^ 17846 = (3 : ZMod 9086618124257) ^ (8923 + 8923) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 8923 * (3 : ZMod 9086618124257) ^ 8923 := by rw [pow_add]
          _ = 2565036692860 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 9086618124257) ^ 35692 = 7657098752109 := by
        calc
          (3 : ZMod 9086618124257) ^ 35692 = (3 : ZMod 9086618124257) ^ (17846 + 17846) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 17846 * (3 : ZMod 9086618124257) ^ 17846 := by rw [pow_add]
          _ = 7657098752109 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 9086618124257) ^ 71384 = 4643542534542 := by
        calc
          (3 : ZMod 9086618124257) ^ 71384 = (3 : ZMod 9086618124257) ^ (35692 + 35692) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 35692 * (3 : ZMod 9086618124257) ^ 35692 := by rw [pow_add]
          _ = 4643542534542 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 9086618124257) ^ 142768 = 3757443910785 := by
        calc
          (3 : ZMod 9086618124257) ^ 142768 = (3 : ZMod 9086618124257) ^ (71384 + 71384) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 71384 * (3 : ZMod 9086618124257) ^ 71384 := by rw [pow_add]
          _ = 3757443910785 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 9086618124257) ^ 285536 = 7604831306143 := by
        calc
          (3 : ZMod 9086618124257) ^ 285536 = (3 : ZMod 9086618124257) ^ (142768 + 142768) :=
            congrArg (fun n : ℕ => (3 : ZMod 9086618124257) ^ n) (by norm_num)
          _ = (3 : ZMod 9086618124257) ^ 142768 * (3 : ZMod 9086618124257) ^ 142768 := by rw [pow_add]
          _ = 7604831306143 := by rw [factor_2_17]; decide
      change (3 : ZMod 9086618124257) ^ 285536 ≠ 1
      rw [factor_2_18]
      decide

#print axioms prime_lucas_9086618124257

end TotientTailPeriodKiller
end Erdos249257
