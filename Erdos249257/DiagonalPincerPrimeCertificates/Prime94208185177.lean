import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_94208185177 : Nat.Prime 94208185177 := by
  apply lucas_primality 94208185177 (10 : ZMod 94208185177)
  ·
      have fermat_0 : (10 : ZMod 94208185177) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 94208185177) ^ 2 = 100 := by
        calc
          (10 : ZMod 94208185177) ^ 2 = (10 : ZMod 94208185177) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1 * (10 : ZMod 94208185177) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 94208185177) ^ 5 = 100000 := by
        calc
          (10 : ZMod 94208185177) ^ 5 = (10 : ZMod 94208185177) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2 * (10 : ZMod 94208185177) ^ 2) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 94208185177) ^ 10 = 10000000000 := by
        calc
          (10 : ZMod 94208185177) ^ 10 = (10 : ZMod 94208185177) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 5 * (10 : ZMod 94208185177) ^ 5 := by rw [pow_add]
          _ = 10000000000 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 94208185177) ^ 21 = 92496716691 := by
        calc
          (10 : ZMod 94208185177) ^ 21 = (10 : ZMod 94208185177) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 10 * (10 : ZMod 94208185177) ^ 10) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 92496716691 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 94208185177) ^ 43 = 87658151647 := by
        calc
          (10 : ZMod 94208185177) ^ 43 = (10 : ZMod 94208185177) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 21 * (10 : ZMod 94208185177) ^ 21) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 87658151647 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 94208185177) ^ 87 = 35213219120 := by
        calc
          (10 : ZMod 94208185177) ^ 87 = (10 : ZMod 94208185177) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 43 * (10 : ZMod 94208185177) ^ 43) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 35213219120 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 94208185177) ^ 175 = 75379246804 := by
        calc
          (10 : ZMod 94208185177) ^ 175 = (10 : ZMod 94208185177) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 87 * (10 : ZMod 94208185177) ^ 87) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 75379246804 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 94208185177) ^ 350 = 77126893548 := by
        calc
          (10 : ZMod 94208185177) ^ 350 = (10 : ZMod 94208185177) ^ (175 + 175) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 175 * (10 : ZMod 94208185177) ^ 175 := by rw [pow_add]
          _ = 77126893548 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 94208185177) ^ 701 = 21817528001 := by
        calc
          (10 : ZMod 94208185177) ^ 701 = (10 : ZMod 94208185177) ^ (350 + 350 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 350 * (10 : ZMod 94208185177) ^ 350) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 21817528001 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 94208185177) ^ 1403 = 12732951595 := by
        calc
          (10 : ZMod 94208185177) ^ 1403 = (10 : ZMod 94208185177) ^ (701 + 701 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 701 * (10 : ZMod 94208185177) ^ 701) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 12732951595 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 94208185177) ^ 2807 = 24473246215 := by
        calc
          (10 : ZMod 94208185177) ^ 2807 = (10 : ZMod 94208185177) ^ (1403 + 1403 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1403 * (10 : ZMod 94208185177) ^ 1403) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 24473246215 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 94208185177) ^ 5615 = 63156586202 := by
        calc
          (10 : ZMod 94208185177) ^ 5615 = (10 : ZMod 94208185177) ^ (2807 + 2807 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2807 * (10 : ZMod 94208185177) ^ 2807) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 63156586202 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 94208185177) ^ 11230 = 66574438912 := by
        calc
          (10 : ZMod 94208185177) ^ 11230 = (10 : ZMod 94208185177) ^ (5615 + 5615) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 5615 * (10 : ZMod 94208185177) ^ 5615 := by rw [pow_add]
          _ = 66574438912 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 94208185177) ^ 22460 = 63666791536 := by
        calc
          (10 : ZMod 94208185177) ^ 22460 = (10 : ZMod 94208185177) ^ (11230 + 11230) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 11230 * (10 : ZMod 94208185177) ^ 11230 := by rw [pow_add]
          _ = 63666791536 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 94208185177) ^ 44921 = 51959886903 := by
        calc
          (10 : ZMod 94208185177) ^ 44921 = (10 : ZMod 94208185177) ^ (22460 + 22460 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 22460 * (10 : ZMod 94208185177) ^ 22460) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 51959886903 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 94208185177) ^ 89843 = 76140940290 := by
        calc
          (10 : ZMod 94208185177) ^ 89843 = (10 : ZMod 94208185177) ^ (44921 + 44921 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 44921 * (10 : ZMod 94208185177) ^ 44921) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 76140940290 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 94208185177) ^ 179687 = 367749499 := by
        calc
          (10 : ZMod 94208185177) ^ 179687 = (10 : ZMod 94208185177) ^ (89843 + 89843 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 89843 * (10 : ZMod 94208185177) ^ 89843) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 367749499 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 94208185177) ^ 359375 = 4992122794 := by
        calc
          (10 : ZMod 94208185177) ^ 359375 = (10 : ZMod 94208185177) ^ (179687 + 179687 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 179687 * (10 : ZMod 94208185177) ^ 179687) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 4992122794 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 94208185177) ^ 718751 = 10963392304 := by
        calc
          (10 : ZMod 94208185177) ^ 718751 = (10 : ZMod 94208185177) ^ (359375 + 359375 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 359375 * (10 : ZMod 94208185177) ^ 359375) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 10963392304 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 94208185177) ^ 1437502 = 89967388550 := by
        calc
          (10 : ZMod 94208185177) ^ 1437502 = (10 : ZMod 94208185177) ^ (718751 + 718751) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 718751 * (10 : ZMod 94208185177) ^ 718751 := by rw [pow_add]
          _ = 89967388550 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 94208185177) ^ 2875005 = 939783003 := by
        calc
          (10 : ZMod 94208185177) ^ 2875005 = (10 : ZMod 94208185177) ^ (1437502 + 1437502 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1437502 * (10 : ZMod 94208185177) ^ 1437502) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 939783003 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 94208185177) ^ 5750011 = 36114851338 := by
        calc
          (10 : ZMod 94208185177) ^ 5750011 = (10 : ZMod 94208185177) ^ (2875005 + 2875005 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2875005 * (10 : ZMod 94208185177) ^ 2875005) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 36114851338 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 94208185177) ^ 11500022 = 64602797914 := by
        calc
          (10 : ZMod 94208185177) ^ 11500022 = (10 : ZMod 94208185177) ^ (5750011 + 5750011) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 5750011 * (10 : ZMod 94208185177) ^ 5750011 := by rw [pow_add]
          _ = 64602797914 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 94208185177) ^ 23000045 = 89997437876 := by
        calc
          (10 : ZMod 94208185177) ^ 23000045 = (10 : ZMod 94208185177) ^ (11500022 + 11500022 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 11500022 * (10 : ZMod 94208185177) ^ 11500022) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 89997437876 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 94208185177) ^ 46000090 = 33340864872 := by
        calc
          (10 : ZMod 94208185177) ^ 46000090 = (10 : ZMod 94208185177) ^ (23000045 + 23000045) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 23000045 * (10 : ZMod 94208185177) ^ 23000045 := by rw [pow_add]
          _ = 33340864872 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 94208185177) ^ 92000180 = 81119701913 := by
        calc
          (10 : ZMod 94208185177) ^ 92000180 = (10 : ZMod 94208185177) ^ (46000090 + 46000090) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 46000090 * (10 : ZMod 94208185177) ^ 46000090 := by rw [pow_add]
          _ = 81119701913 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 94208185177) ^ 184000361 = 1883581434 := by
        calc
          (10 : ZMod 94208185177) ^ 184000361 = (10 : ZMod 94208185177) ^ (92000180 + 92000180 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 92000180 * (10 : ZMod 94208185177) ^ 92000180) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 1883581434 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 94208185177) ^ 368000723 = 82917206924 := by
        calc
          (10 : ZMod 94208185177) ^ 368000723 = (10 : ZMod 94208185177) ^ (184000361 + 184000361 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 184000361 * (10 : ZMod 94208185177) ^ 184000361) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 82917206924 := by rw [fermat_27]; decide
      have fermat_29 : (10 : ZMod 94208185177) ^ 736001446 = 80021554894 := by
        calc
          (10 : ZMod 94208185177) ^ 736001446 = (10 : ZMod 94208185177) ^ (368000723 + 368000723) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 368000723 * (10 : ZMod 94208185177) ^ 368000723 := by rw [pow_add]
          _ = 80021554894 := by rw [fermat_28]; decide
      have fermat_30 : (10 : ZMod 94208185177) ^ 1472002893 = 48050596244 := by
        calc
          (10 : ZMod 94208185177) ^ 1472002893 = (10 : ZMod 94208185177) ^ (736001446 + 736001446 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 736001446 * (10 : ZMod 94208185177) ^ 736001446) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 48050596244 := by rw [fermat_29]; decide
      have fermat_31 : (10 : ZMod 94208185177) ^ 2944005786 = 83501356789 := by
        calc
          (10 : ZMod 94208185177) ^ 2944005786 = (10 : ZMod 94208185177) ^ (1472002893 + 1472002893) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1472002893 * (10 : ZMod 94208185177) ^ 1472002893 := by rw [pow_add]
          _ = 83501356789 := by rw [fermat_30]; decide
      have fermat_32 : (10 : ZMod 94208185177) ^ 5888011573 = 52603330901 := by
        calc
          (10 : ZMod 94208185177) ^ 5888011573 = (10 : ZMod 94208185177) ^ (2944005786 + 2944005786 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2944005786 * (10 : ZMod 94208185177) ^ 2944005786) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 52603330901 := by rw [fermat_31]; decide
      have fermat_33 : (10 : ZMod 94208185177) ^ 11776023147 = 4650185440 := by
        calc
          (10 : ZMod 94208185177) ^ 11776023147 = (10 : ZMod 94208185177) ^ (5888011573 + 5888011573 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 5888011573 * (10 : ZMod 94208185177) ^ 5888011573) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 4650185440 := by rw [fermat_32]; decide
      have fermat_34 : (10 : ZMod 94208185177) ^ 23552046294 = 87060904117 := by
        calc
          (10 : ZMod 94208185177) ^ 23552046294 = (10 : ZMod 94208185177) ^ (11776023147 + 11776023147) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 11776023147 * (10 : ZMod 94208185177) ^ 11776023147 := by rw [pow_add]
          _ = 87060904117 := by rw [fermat_33]; decide
      have fermat_35 : (10 : ZMod 94208185177) ^ 47104092588 = 94208185176 := by
        calc
          (10 : ZMod 94208185177) ^ 47104092588 = (10 : ZMod 94208185177) ^ (23552046294 + 23552046294) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 23552046294 * (10 : ZMod 94208185177) ^ 23552046294 := by rw [pow_add]
          _ = 94208185176 := by rw [fermat_34]; decide
      have fermat_36 : (10 : ZMod 94208185177) ^ 94208185176 = 1 := by
        calc
          (10 : ZMod 94208185177) ^ 94208185176 = (10 : ZMod 94208185177) ^ (47104092588 + 47104092588) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 47104092588 * (10 : ZMod 94208185177) ^ 47104092588 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 3), (11444143, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 3), (11444143, 1)] : List FactorBlock).map factorBlockValue).prod = 94208185177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 94208185177) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 94208185177) ^ 2 = 100 := by
        calc
          (10 : ZMod 94208185177) ^ 2 = (10 : ZMod 94208185177) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1 * (10 : ZMod 94208185177) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 94208185177) ^ 5 = 100000 := by
        calc
          (10 : ZMod 94208185177) ^ 5 = (10 : ZMod 94208185177) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2 * (10 : ZMod 94208185177) ^ 2) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 94208185177) ^ 10 = 10000000000 := by
        calc
          (10 : ZMod 94208185177) ^ 10 = (10 : ZMod 94208185177) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 5 * (10 : ZMod 94208185177) ^ 5 := by rw [pow_add]
          _ = 10000000000 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 94208185177) ^ 21 = 92496716691 := by
        calc
          (10 : ZMod 94208185177) ^ 21 = (10 : ZMod 94208185177) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 10 * (10 : ZMod 94208185177) ^ 10) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 92496716691 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 94208185177) ^ 43 = 87658151647 := by
        calc
          (10 : ZMod 94208185177) ^ 43 = (10 : ZMod 94208185177) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 21 * (10 : ZMod 94208185177) ^ 21) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 87658151647 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 94208185177) ^ 87 = 35213219120 := by
        calc
          (10 : ZMod 94208185177) ^ 87 = (10 : ZMod 94208185177) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 43 * (10 : ZMod 94208185177) ^ 43) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 35213219120 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 94208185177) ^ 175 = 75379246804 := by
        calc
          (10 : ZMod 94208185177) ^ 175 = (10 : ZMod 94208185177) ^ (87 + 87 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 87 * (10 : ZMod 94208185177) ^ 87) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 75379246804 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 94208185177) ^ 350 = 77126893548 := by
        calc
          (10 : ZMod 94208185177) ^ 350 = (10 : ZMod 94208185177) ^ (175 + 175) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 175 * (10 : ZMod 94208185177) ^ 175 := by rw [pow_add]
          _ = 77126893548 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 94208185177) ^ 701 = 21817528001 := by
        calc
          (10 : ZMod 94208185177) ^ 701 = (10 : ZMod 94208185177) ^ (350 + 350 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 350 * (10 : ZMod 94208185177) ^ 350) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 21817528001 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 94208185177) ^ 1403 = 12732951595 := by
        calc
          (10 : ZMod 94208185177) ^ 1403 = (10 : ZMod 94208185177) ^ (701 + 701 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 701 * (10 : ZMod 94208185177) ^ 701) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 12732951595 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 94208185177) ^ 2807 = 24473246215 := by
        calc
          (10 : ZMod 94208185177) ^ 2807 = (10 : ZMod 94208185177) ^ (1403 + 1403 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1403 * (10 : ZMod 94208185177) ^ 1403) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 24473246215 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 94208185177) ^ 5615 = 63156586202 := by
        calc
          (10 : ZMod 94208185177) ^ 5615 = (10 : ZMod 94208185177) ^ (2807 + 2807 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2807 * (10 : ZMod 94208185177) ^ 2807) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 63156586202 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 94208185177) ^ 11230 = 66574438912 := by
        calc
          (10 : ZMod 94208185177) ^ 11230 = (10 : ZMod 94208185177) ^ (5615 + 5615) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 5615 * (10 : ZMod 94208185177) ^ 5615 := by rw [pow_add]
          _ = 66574438912 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 94208185177) ^ 22460 = 63666791536 := by
        calc
          (10 : ZMod 94208185177) ^ 22460 = (10 : ZMod 94208185177) ^ (11230 + 11230) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 11230 * (10 : ZMod 94208185177) ^ 11230 := by rw [pow_add]
          _ = 63666791536 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 94208185177) ^ 44921 = 51959886903 := by
        calc
          (10 : ZMod 94208185177) ^ 44921 = (10 : ZMod 94208185177) ^ (22460 + 22460 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 22460 * (10 : ZMod 94208185177) ^ 22460) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 51959886903 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 94208185177) ^ 89843 = 76140940290 := by
        calc
          (10 : ZMod 94208185177) ^ 89843 = (10 : ZMod 94208185177) ^ (44921 + 44921 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 44921 * (10 : ZMod 94208185177) ^ 44921) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 76140940290 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 94208185177) ^ 179687 = 367749499 := by
        calc
          (10 : ZMod 94208185177) ^ 179687 = (10 : ZMod 94208185177) ^ (89843 + 89843 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 89843 * (10 : ZMod 94208185177) ^ 89843) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 367749499 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 94208185177) ^ 359375 = 4992122794 := by
        calc
          (10 : ZMod 94208185177) ^ 359375 = (10 : ZMod 94208185177) ^ (179687 + 179687 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 179687 * (10 : ZMod 94208185177) ^ 179687) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 4992122794 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 94208185177) ^ 718751 = 10963392304 := by
        calc
          (10 : ZMod 94208185177) ^ 718751 = (10 : ZMod 94208185177) ^ (359375 + 359375 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 359375 * (10 : ZMod 94208185177) ^ 359375) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 10963392304 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 94208185177) ^ 1437502 = 89967388550 := by
        calc
          (10 : ZMod 94208185177) ^ 1437502 = (10 : ZMod 94208185177) ^ (718751 + 718751) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 718751 * (10 : ZMod 94208185177) ^ 718751 := by rw [pow_add]
          _ = 89967388550 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 94208185177) ^ 2875005 = 939783003 := by
        calc
          (10 : ZMod 94208185177) ^ 2875005 = (10 : ZMod 94208185177) ^ (1437502 + 1437502 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1437502 * (10 : ZMod 94208185177) ^ 1437502) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 939783003 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 94208185177) ^ 5750011 = 36114851338 := by
        calc
          (10 : ZMod 94208185177) ^ 5750011 = (10 : ZMod 94208185177) ^ (2875005 + 2875005 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2875005 * (10 : ZMod 94208185177) ^ 2875005) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 36114851338 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 94208185177) ^ 11500022 = 64602797914 := by
        calc
          (10 : ZMod 94208185177) ^ 11500022 = (10 : ZMod 94208185177) ^ (5750011 + 5750011) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 5750011 * (10 : ZMod 94208185177) ^ 5750011 := by rw [pow_add]
          _ = 64602797914 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 94208185177) ^ 23000045 = 89997437876 := by
        calc
          (10 : ZMod 94208185177) ^ 23000045 = (10 : ZMod 94208185177) ^ (11500022 + 11500022 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 11500022 * (10 : ZMod 94208185177) ^ 11500022) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 89997437876 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 94208185177) ^ 46000090 = 33340864872 := by
        calc
          (10 : ZMod 94208185177) ^ 46000090 = (10 : ZMod 94208185177) ^ (23000045 + 23000045) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 23000045 * (10 : ZMod 94208185177) ^ 23000045 := by rw [pow_add]
          _ = 33340864872 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 94208185177) ^ 92000180 = 81119701913 := by
        calc
          (10 : ZMod 94208185177) ^ 92000180 = (10 : ZMod 94208185177) ^ (46000090 + 46000090) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 46000090 * (10 : ZMod 94208185177) ^ 46000090 := by rw [pow_add]
          _ = 81119701913 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 94208185177) ^ 184000361 = 1883581434 := by
        calc
          (10 : ZMod 94208185177) ^ 184000361 = (10 : ZMod 94208185177) ^ (92000180 + 92000180 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 92000180 * (10 : ZMod 94208185177) ^ 92000180) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 1883581434 := by rw [factor_0_26]; decide
      have factor_0_28 : (10 : ZMod 94208185177) ^ 368000723 = 82917206924 := by
        calc
          (10 : ZMod 94208185177) ^ 368000723 = (10 : ZMod 94208185177) ^ (184000361 + 184000361 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 184000361 * (10 : ZMod 94208185177) ^ 184000361) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 82917206924 := by rw [factor_0_27]; decide
      have factor_0_29 : (10 : ZMod 94208185177) ^ 736001446 = 80021554894 := by
        calc
          (10 : ZMod 94208185177) ^ 736001446 = (10 : ZMod 94208185177) ^ (368000723 + 368000723) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 368000723 * (10 : ZMod 94208185177) ^ 368000723 := by rw [pow_add]
          _ = 80021554894 := by rw [factor_0_28]; decide
      have factor_0_30 : (10 : ZMod 94208185177) ^ 1472002893 = 48050596244 := by
        calc
          (10 : ZMod 94208185177) ^ 1472002893 = (10 : ZMod 94208185177) ^ (736001446 + 736001446 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 736001446 * (10 : ZMod 94208185177) ^ 736001446) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 48050596244 := by rw [factor_0_29]; decide
      have factor_0_31 : (10 : ZMod 94208185177) ^ 2944005786 = 83501356789 := by
        calc
          (10 : ZMod 94208185177) ^ 2944005786 = (10 : ZMod 94208185177) ^ (1472002893 + 1472002893) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1472002893 * (10 : ZMod 94208185177) ^ 1472002893 := by rw [pow_add]
          _ = 83501356789 := by rw [factor_0_30]; decide
      have factor_0_32 : (10 : ZMod 94208185177) ^ 5888011573 = 52603330901 := by
        calc
          (10 : ZMod 94208185177) ^ 5888011573 = (10 : ZMod 94208185177) ^ (2944005786 + 2944005786 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 2944005786 * (10 : ZMod 94208185177) ^ 2944005786) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 52603330901 := by rw [factor_0_31]; decide
      have factor_0_33 : (10 : ZMod 94208185177) ^ 11776023147 = 4650185440 := by
        calc
          (10 : ZMod 94208185177) ^ 11776023147 = (10 : ZMod 94208185177) ^ (5888011573 + 5888011573 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 5888011573 * (10 : ZMod 94208185177) ^ 5888011573) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 4650185440 := by rw [factor_0_32]; decide
      have factor_0_34 : (10 : ZMod 94208185177) ^ 23552046294 = 87060904117 := by
        calc
          (10 : ZMod 94208185177) ^ 23552046294 = (10 : ZMod 94208185177) ^ (11776023147 + 11776023147) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 11776023147 * (10 : ZMod 94208185177) ^ 11776023147 := by rw [pow_add]
          _ = 87060904117 := by rw [factor_0_33]; decide
      have factor_0_35 : (10 : ZMod 94208185177) ^ 47104092588 = 94208185176 := by
        calc
          (10 : ZMod 94208185177) ^ 47104092588 = (10 : ZMod 94208185177) ^ (23552046294 + 23552046294) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 23552046294 * (10 : ZMod 94208185177) ^ 23552046294 := by rw [pow_add]
          _ = 94208185176 := by rw [factor_0_34]; decide
      change (10 : ZMod 94208185177) ^ 47104092588 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (10 : ZMod 94208185177) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 94208185177) ^ 3 = 1000 := by
        calc
          (10 : ZMod 94208185177) ^ 3 = (10 : ZMod 94208185177) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1 * (10 : ZMod 94208185177) ^ 1) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 94208185177) ^ 7 = 10000000 := by
        calc
          (10 : ZMod 94208185177) ^ 7 = (10 : ZMod 94208185177) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 3 * (10 : ZMod 94208185177) ^ 3) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 10000000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 94208185177) ^ 14 = 45115527203 := by
        calc
          (10 : ZMod 94208185177) ^ 14 = (10 : ZMod 94208185177) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 7 * (10 : ZMod 94208185177) ^ 7 := by rw [pow_add]
          _ = 45115527203 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 94208185177) ^ 29 = 30912833776 := by
        calc
          (10 : ZMod 94208185177) ^ 29 = (10 : ZMod 94208185177) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 14 * (10 : ZMod 94208185177) ^ 14) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 30912833776 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 94208185177) ^ 58 = 53991807758 := by
        calc
          (10 : ZMod 94208185177) ^ 58 = (10 : ZMod 94208185177) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 29 * (10 : ZMod 94208185177) ^ 29 := by rw [pow_add]
          _ = 53991807758 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 94208185177) ^ 116 = 85472828523 := by
        calc
          (10 : ZMod 94208185177) ^ 116 = (10 : ZMod 94208185177) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 58 * (10 : ZMod 94208185177) ^ 58 := by rw [pow_add]
          _ = 85472828523 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 94208185177) ^ 233 = 62887720043 := by
        calc
          (10 : ZMod 94208185177) ^ 233 = (10 : ZMod 94208185177) ^ (116 + 116 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 116 * (10 : ZMod 94208185177) ^ 116) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 62887720043 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 94208185177) ^ 467 = 17604038782 := by
        calc
          (10 : ZMod 94208185177) ^ 467 = (10 : ZMod 94208185177) ^ (233 + 233 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 233 * (10 : ZMod 94208185177) ^ 233) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 17604038782 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 94208185177) ^ 935 = 83069553493 := by
        calc
          (10 : ZMod 94208185177) ^ 935 = (10 : ZMod 94208185177) ^ (467 + 467 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 467 * (10 : ZMod 94208185177) ^ 467) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 83069553493 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 94208185177) ^ 1871 = 66601022279 := by
        calc
          (10 : ZMod 94208185177) ^ 1871 = (10 : ZMod 94208185177) ^ (935 + 935 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 935 * (10 : ZMod 94208185177) ^ 935) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 66601022279 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 94208185177) ^ 3743 = 68893633230 := by
        calc
          (10 : ZMod 94208185177) ^ 3743 = (10 : ZMod 94208185177) ^ (1871 + 1871 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1871 * (10 : ZMod 94208185177) ^ 1871) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 68893633230 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 94208185177) ^ 7486 = 7986553743 := by
        calc
          (10 : ZMod 94208185177) ^ 7486 = (10 : ZMod 94208185177) ^ (3743 + 3743) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 3743 * (10 : ZMod 94208185177) ^ 3743 := by rw [pow_add]
          _ = 7986553743 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 94208185177) ^ 14973 = 44653955380 := by
        calc
          (10 : ZMod 94208185177) ^ 14973 = (10 : ZMod 94208185177) ^ (7486 + 7486 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 7486 * (10 : ZMod 94208185177) ^ 7486) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 44653955380 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 94208185177) ^ 29947 = 77647836567 := by
        calc
          (10 : ZMod 94208185177) ^ 29947 = (10 : ZMod 94208185177) ^ (14973 + 14973 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 14973 * (10 : ZMod 94208185177) ^ 14973) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 77647836567 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 94208185177) ^ 59895 = 66406953802 := by
        calc
          (10 : ZMod 94208185177) ^ 59895 = (10 : ZMod 94208185177) ^ (29947 + 29947 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 29947 * (10 : ZMod 94208185177) ^ 29947) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 66406953802 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 94208185177) ^ 119791 = 50169983443 := by
        calc
          (10 : ZMod 94208185177) ^ 119791 = (10 : ZMod 94208185177) ^ (59895 + 59895 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 59895 * (10 : ZMod 94208185177) ^ 59895) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 50169983443 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 94208185177) ^ 239583 = 2092911929 := by
        calc
          (10 : ZMod 94208185177) ^ 239583 = (10 : ZMod 94208185177) ^ (119791 + 119791 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 119791 * (10 : ZMod 94208185177) ^ 119791) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 2092911929 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 94208185177) ^ 479167 = 35571810786 := by
        calc
          (10 : ZMod 94208185177) ^ 479167 = (10 : ZMod 94208185177) ^ (239583 + 239583 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 239583 * (10 : ZMod 94208185177) ^ 239583) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 35571810786 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 94208185177) ^ 958335 = 26675433697 := by
        calc
          (10 : ZMod 94208185177) ^ 958335 = (10 : ZMod 94208185177) ^ (479167 + 479167 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 479167 * (10 : ZMod 94208185177) ^ 479167) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 26675433697 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 94208185177) ^ 1916670 = 89190647027 := by
        calc
          (10 : ZMod 94208185177) ^ 1916670 = (10 : ZMod 94208185177) ^ (958335 + 958335) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 958335 * (10 : ZMod 94208185177) ^ 958335 := by rw [pow_add]
          _ = 89190647027 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 94208185177) ^ 3833340 = 48999268875 := by
        calc
          (10 : ZMod 94208185177) ^ 3833340 = (10 : ZMod 94208185177) ^ (1916670 + 1916670) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1916670 * (10 : ZMod 94208185177) ^ 1916670 := by rw [pow_add]
          _ = 48999268875 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 94208185177) ^ 7666681 = 64796333892 := by
        calc
          (10 : ZMod 94208185177) ^ 7666681 = (10 : ZMod 94208185177) ^ (3833340 + 3833340 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 3833340 * (10 : ZMod 94208185177) ^ 3833340) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 64796333892 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 94208185177) ^ 15333363 = 75133078408 := by
        calc
          (10 : ZMod 94208185177) ^ 15333363 = (10 : ZMod 94208185177) ^ (7666681 + 7666681 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 7666681 * (10 : ZMod 94208185177) ^ 7666681) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 75133078408 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 94208185177) ^ 30666726 = 63217580477 := by
        calc
          (10 : ZMod 94208185177) ^ 30666726 = (10 : ZMod 94208185177) ^ (15333363 + 15333363) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 15333363 * (10 : ZMod 94208185177) ^ 15333363 := by rw [pow_add]
          _ = 63217580477 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 94208185177) ^ 61333453 = 31741605099 := by
        calc
          (10 : ZMod 94208185177) ^ 61333453 = (10 : ZMod 94208185177) ^ (30666726 + 30666726 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 30666726 * (10 : ZMod 94208185177) ^ 30666726) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 31741605099 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 94208185177) ^ 122666907 = 18886276956 := by
        calc
          (10 : ZMod 94208185177) ^ 122666907 = (10 : ZMod 94208185177) ^ (61333453 + 61333453 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 61333453 * (10 : ZMod 94208185177) ^ 61333453) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 18886276956 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 94208185177) ^ 245333815 = 46000185508 := by
        calc
          (10 : ZMod 94208185177) ^ 245333815 = (10 : ZMod 94208185177) ^ (122666907 + 122666907 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 122666907 * (10 : ZMod 94208185177) ^ 122666907) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 46000185508 := by rw [factor_1_26]; decide
      have factor_1_28 : (10 : ZMod 94208185177) ^ 490667631 = 14137686878 := by
        calc
          (10 : ZMod 94208185177) ^ 490667631 = (10 : ZMod 94208185177) ^ (245333815 + 245333815 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 245333815 * (10 : ZMod 94208185177) ^ 245333815) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 14137686878 := by rw [factor_1_27]; decide
      have factor_1_29 : (10 : ZMod 94208185177) ^ 981335262 = 72201517881 := by
        calc
          (10 : ZMod 94208185177) ^ 981335262 = (10 : ZMod 94208185177) ^ (490667631 + 490667631) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 490667631 * (10 : ZMod 94208185177) ^ 490667631 := by rw [pow_add]
          _ = 72201517881 := by rw [factor_1_28]; decide
      have factor_1_30 : (10 : ZMod 94208185177) ^ 1962670524 = 47782454295 := by
        calc
          (10 : ZMod 94208185177) ^ 1962670524 = (10 : ZMod 94208185177) ^ (981335262 + 981335262) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 981335262 * (10 : ZMod 94208185177) ^ 981335262 := by rw [pow_add]
          _ = 47782454295 := by rw [factor_1_29]; decide
      have factor_1_31 : (10 : ZMod 94208185177) ^ 3925341049 = 43196017360 := by
        calc
          (10 : ZMod 94208185177) ^ 3925341049 = (10 : ZMod 94208185177) ^ (1962670524 + 1962670524 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1962670524 * (10 : ZMod 94208185177) ^ 1962670524) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 43196017360 := by rw [factor_1_30]; decide
      have factor_1_32 : (10 : ZMod 94208185177) ^ 7850682098 = 72950931624 := by
        calc
          (10 : ZMod 94208185177) ^ 7850682098 = (10 : ZMod 94208185177) ^ (3925341049 + 3925341049) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 3925341049 * (10 : ZMod 94208185177) ^ 3925341049 := by rw [pow_add]
          _ = 72950931624 := by rw [factor_1_31]; decide
      have factor_1_33 : (10 : ZMod 94208185177) ^ 15701364196 = 90253585858 := by
        calc
          (10 : ZMod 94208185177) ^ 15701364196 = (10 : ZMod 94208185177) ^ (7850682098 + 7850682098) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 7850682098 * (10 : ZMod 94208185177) ^ 7850682098 := by rw [pow_add]
          _ = 90253585858 := by rw [factor_1_32]; decide
      have factor_1_34 : (10 : ZMod 94208185177) ^ 31402728392 = 90253585857 := by
        calc
          (10 : ZMod 94208185177) ^ 31402728392 = (10 : ZMod 94208185177) ^ (15701364196 + 15701364196) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 15701364196 * (10 : ZMod 94208185177) ^ 15701364196 := by rw [pow_add]
          _ = 90253585857 := by rw [factor_1_33]; decide
      change (10 : ZMod 94208185177) ^ 31402728392 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (10 : ZMod 94208185177) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 94208185177) ^ 3 = 1000 := by
        calc
          (10 : ZMod 94208185177) ^ 3 = (10 : ZMod 94208185177) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 1 * (10 : ZMod 94208185177) ^ 1) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 94208185177) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 94208185177) ^ 6 = (10 : ZMod 94208185177) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 3 * (10 : ZMod 94208185177) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 94208185177) ^ 12 = 57918148230 := by
        calc
          (10 : ZMod 94208185177) ^ 12 = (10 : ZMod 94208185177) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 6 * (10 : ZMod 94208185177) ^ 6 := by rw [pow_add]
          _ = 57918148230 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 94208185177) ^ 25 = 31204842214 := by
        calc
          (10 : ZMod 94208185177) ^ 25 = (10 : ZMod 94208185177) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 12 * (10 : ZMod 94208185177) ^ 12) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 31204842214 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 94208185177) ^ 50 = 72232568321 := by
        calc
          (10 : ZMod 94208185177) ^ 50 = (10 : ZMod 94208185177) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 25 * (10 : ZMod 94208185177) ^ 25 := by rw [pow_add]
          _ = 72232568321 := by rw [factor_2_4]; decide
      have factor_2_6 : (10 : ZMod 94208185177) ^ 100 = 39565505922 := by
        calc
          (10 : ZMod 94208185177) ^ 100 = (10 : ZMod 94208185177) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 50 * (10 : ZMod 94208185177) ^ 50 := by rw [pow_add]
          _ = 39565505922 := by rw [factor_2_5]; decide
      have factor_2_7 : (10 : ZMod 94208185177) ^ 200 = 82164586888 := by
        calc
          (10 : ZMod 94208185177) ^ 200 = (10 : ZMod 94208185177) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 100 * (10 : ZMod 94208185177) ^ 100 := by rw [pow_add]
          _ = 82164586888 := by rw [factor_2_6]; decide
      have factor_2_8 : (10 : ZMod 94208185177) ^ 401 = 31015801833 := by
        calc
          (10 : ZMod 94208185177) ^ 401 = (10 : ZMod 94208185177) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 200 * (10 : ZMod 94208185177) ^ 200) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 31015801833 := by rw [factor_2_7]; decide
      have factor_2_9 : (10 : ZMod 94208185177) ^ 802 = 21072246931 := by
        calc
          (10 : ZMod 94208185177) ^ 802 = (10 : ZMod 94208185177) ^ (401 + 401) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 401 * (10 : ZMod 94208185177) ^ 401 := by rw [pow_add]
          _ = 21072246931 := by rw [factor_2_8]; decide
      have factor_2_10 : (10 : ZMod 94208185177) ^ 1604 = 68854193659 := by
        calc
          (10 : ZMod 94208185177) ^ 1604 = (10 : ZMod 94208185177) ^ (802 + 802) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 802 * (10 : ZMod 94208185177) ^ 802 := by rw [pow_add]
          _ = 68854193659 := by rw [factor_2_9]; decide
      have factor_2_11 : (10 : ZMod 94208185177) ^ 3208 = 94135520426 := by
        calc
          (10 : ZMod 94208185177) ^ 3208 = (10 : ZMod 94208185177) ^ (1604 + 1604) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1604 * (10 : ZMod 94208185177) ^ 1604 := by rw [pow_add]
          _ = 94135520426 := by rw [factor_2_10]; decide
      have factor_2_12 : (10 : ZMod 94208185177) ^ 6417 = 45167285404 := by
        calc
          (10 : ZMod 94208185177) ^ 6417 = (10 : ZMod 94208185177) ^ (3208 + 3208 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 3208 * (10 : ZMod 94208185177) ^ 3208) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 45167285404 := by rw [factor_2_11]; decide
      have factor_2_13 : (10 : ZMod 94208185177) ^ 12834 = 19481358636 := by
        calc
          (10 : ZMod 94208185177) ^ 12834 = (10 : ZMod 94208185177) ^ (6417 + 6417) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 6417 * (10 : ZMod 94208185177) ^ 6417 := by rw [pow_add]
          _ = 19481358636 := by rw [factor_2_12]; decide
      have factor_2_14 : (10 : ZMod 94208185177) ^ 25669 = 85172908050 := by
        calc
          (10 : ZMod 94208185177) ^ 25669 = (10 : ZMod 94208185177) ^ (12834 + 12834 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 12834 * (10 : ZMod 94208185177) ^ 12834) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 85172908050 := by rw [factor_2_13]; decide
      have factor_2_15 : (10 : ZMod 94208185177) ^ 51339 = 23143020814 := by
        calc
          (10 : ZMod 94208185177) ^ 51339 = (10 : ZMod 94208185177) ^ (25669 + 25669 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 25669 * (10 : ZMod 94208185177) ^ 25669) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 23143020814 := by rw [factor_2_14]; decide
      have factor_2_16 : (10 : ZMod 94208185177) ^ 102678 = 18066804457 := by
        calc
          (10 : ZMod 94208185177) ^ 102678 = (10 : ZMod 94208185177) ^ (51339 + 51339) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 51339 * (10 : ZMod 94208185177) ^ 51339 := by rw [pow_add]
          _ = 18066804457 := by rw [factor_2_15]; decide
      have factor_2_17 : (10 : ZMod 94208185177) ^ 205357 = 34604180160 := by
        calc
          (10 : ZMod 94208185177) ^ 205357 = (10 : ZMod 94208185177) ^ (102678 + 102678 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 102678 * (10 : ZMod 94208185177) ^ 102678) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 34604180160 := by rw [factor_2_16]; decide
      have factor_2_18 : (10 : ZMod 94208185177) ^ 410715 = 38974396142 := by
        calc
          (10 : ZMod 94208185177) ^ 410715 = (10 : ZMod 94208185177) ^ (205357 + 205357 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 205357 * (10 : ZMod 94208185177) ^ 205357) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 38974396142 := by rw [factor_2_17]; decide
      have factor_2_19 : (10 : ZMod 94208185177) ^ 821430 = 9341682818 := by
        calc
          (10 : ZMod 94208185177) ^ 821430 = (10 : ZMod 94208185177) ^ (410715 + 410715) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 410715 * (10 : ZMod 94208185177) ^ 410715 := by rw [pow_add]
          _ = 9341682818 := by rw [factor_2_18]; decide
      have factor_2_20 : (10 : ZMod 94208185177) ^ 1642860 = 48050161202 := by
        calc
          (10 : ZMod 94208185177) ^ 1642860 = (10 : ZMod 94208185177) ^ (821430 + 821430) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 821430 * (10 : ZMod 94208185177) ^ 821430 := by rw [pow_add]
          _ = 48050161202 := by rw [factor_2_19]; decide
      have factor_2_21 : (10 : ZMod 94208185177) ^ 3285720 = 20406568294 := by
        calc
          (10 : ZMod 94208185177) ^ 3285720 = (10 : ZMod 94208185177) ^ (1642860 + 1642860) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1642860 * (10 : ZMod 94208185177) ^ 1642860 := by rw [pow_add]
          _ = 20406568294 := by rw [factor_2_20]; decide
      have factor_2_22 : (10 : ZMod 94208185177) ^ 6571441 = 69376383950 := by
        calc
          (10 : ZMod 94208185177) ^ 6571441 = (10 : ZMod 94208185177) ^ (3285720 + 3285720 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 3285720 * (10 : ZMod 94208185177) ^ 3285720) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 69376383950 := by rw [factor_2_21]; decide
      have factor_2_23 : (10 : ZMod 94208185177) ^ 13142882 = 29691834302 := by
        calc
          (10 : ZMod 94208185177) ^ 13142882 = (10 : ZMod 94208185177) ^ (6571441 + 6571441) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 6571441 * (10 : ZMod 94208185177) ^ 6571441 := by rw [pow_add]
          _ = 29691834302 := by rw [factor_2_22]; decide
      have factor_2_24 : (10 : ZMod 94208185177) ^ 26285765 = 203540293 := by
        calc
          (10 : ZMod 94208185177) ^ 26285765 = (10 : ZMod 94208185177) ^ (13142882 + 13142882 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 13142882 * (10 : ZMod 94208185177) ^ 13142882) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 203540293 := by rw [factor_2_23]; decide
      have factor_2_25 : (10 : ZMod 94208185177) ^ 52571531 = 79313734839 := by
        calc
          (10 : ZMod 94208185177) ^ 52571531 = (10 : ZMod 94208185177) ^ (26285765 + 26285765 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 26285765 * (10 : ZMod 94208185177) ^ 26285765) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 79313734839 := by rw [factor_2_24]; decide
      have factor_2_26 : (10 : ZMod 94208185177) ^ 105143063 = 75944936985 := by
        calc
          (10 : ZMod 94208185177) ^ 105143063 = (10 : ZMod 94208185177) ^ (52571531 + 52571531 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 52571531 * (10 : ZMod 94208185177) ^ 52571531) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 75944936985 := by rw [factor_2_25]; decide
      have factor_2_27 : (10 : ZMod 94208185177) ^ 210286127 = 42366672014 := by
        calc
          (10 : ZMod 94208185177) ^ 210286127 = (10 : ZMod 94208185177) ^ (105143063 + 105143063 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 105143063 * (10 : ZMod 94208185177) ^ 105143063) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 42366672014 := by rw [factor_2_26]; decide
      have factor_2_28 : (10 : ZMod 94208185177) ^ 420572255 = 24583742707 := by
        calc
          (10 : ZMod 94208185177) ^ 420572255 = (10 : ZMod 94208185177) ^ (210286127 + 210286127 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 210286127 * (10 : ZMod 94208185177) ^ 210286127) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 24583742707 := by rw [factor_2_27]; decide
      have factor_2_29 : (10 : ZMod 94208185177) ^ 841144510 = 56365908131 := by
        calc
          (10 : ZMod 94208185177) ^ 841144510 = (10 : ZMod 94208185177) ^ (420572255 + 420572255) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 420572255 * (10 : ZMod 94208185177) ^ 420572255 := by rw [pow_add]
          _ = 56365908131 := by rw [factor_2_28]; decide
      have factor_2_30 : (10 : ZMod 94208185177) ^ 1682289021 = 1437254490 := by
        calc
          (10 : ZMod 94208185177) ^ 1682289021 = (10 : ZMod 94208185177) ^ (841144510 + 841144510 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 841144510 * (10 : ZMod 94208185177) ^ 841144510) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 1437254490 := by rw [factor_2_29]; decide
      have factor_2_31 : (10 : ZMod 94208185177) ^ 3364578042 = 42061895702 := by
        calc
          (10 : ZMod 94208185177) ^ 3364578042 = (10 : ZMod 94208185177) ^ (1682289021 + 1682289021) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1682289021 * (10 : ZMod 94208185177) ^ 1682289021 := by rw [pow_add]
          _ = 42061895702 := by rw [factor_2_30]; decide
      have factor_2_32 : (10 : ZMod 94208185177) ^ 6729156084 = 54917053847 := by
        calc
          (10 : ZMod 94208185177) ^ 6729156084 = (10 : ZMod 94208185177) ^ (3364578042 + 3364578042) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 3364578042 * (10 : ZMod 94208185177) ^ 3364578042 := by rw [pow_add]
          _ = 54917053847 := by rw [factor_2_31]; decide
      have factor_2_33 : (10 : ZMod 94208185177) ^ 13458312168 = 66266648220 := by
        calc
          (10 : ZMod 94208185177) ^ 13458312168 = (10 : ZMod 94208185177) ^ (6729156084 + 6729156084) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 6729156084 * (10 : ZMod 94208185177) ^ 6729156084 := by rw [pow_add]
          _ = 66266648220 := by rw [factor_2_32]; decide
      change (10 : ZMod 94208185177) ^ 13458312168 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (10 : ZMod 94208185177) ^ 1 = 10 := by norm_num
      have factor_3_1 : (10 : ZMod 94208185177) ^ 2 = 100 := by
        calc
          (10 : ZMod 94208185177) ^ 2 = (10 : ZMod 94208185177) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1 * (10 : ZMod 94208185177) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_3_0]; decide
      have factor_3_2 : (10 : ZMod 94208185177) ^ 4 = 10000 := by
        calc
          (10 : ZMod 94208185177) ^ 4 = (10 : ZMod 94208185177) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 2 * (10 : ZMod 94208185177) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_3_1]; decide
      have factor_3_3 : (10 : ZMod 94208185177) ^ 8 = 100000000 := by
        calc
          (10 : ZMod 94208185177) ^ 8 = (10 : ZMod 94208185177) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 4 * (10 : ZMod 94208185177) ^ 4 := by rw [pow_add]
          _ = 100000000 := by rw [factor_3_2]; decide
      have factor_3_4 : (10 : ZMod 94208185177) ^ 16 = 83768016981 := by
        calc
          (10 : ZMod 94208185177) ^ 16 = (10 : ZMod 94208185177) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 8 * (10 : ZMod 94208185177) ^ 8 := by rw [pow_add]
          _ = 83768016981 := by rw [factor_3_3]; decide
      have factor_3_5 : (10 : ZMod 94208185177) ^ 32 = 12549037944 := by
        calc
          (10 : ZMod 94208185177) ^ 32 = (10 : ZMod 94208185177) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 16 * (10 : ZMod 94208185177) ^ 16 := by rw [pow_add]
          _ = 12549037944 := by rw [factor_3_4]; decide
      have factor_3_6 : (10 : ZMod 94208185177) ^ 64 = 60543024353 := by
        calc
          (10 : ZMod 94208185177) ^ 64 = (10 : ZMod 94208185177) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 32 * (10 : ZMod 94208185177) ^ 32 := by rw [pow_add]
          _ = 60543024353 := by rw [factor_3_5]; decide
      have factor_3_7 : (10 : ZMod 94208185177) ^ 128 = 47286270062 := by
        calc
          (10 : ZMod 94208185177) ^ 128 = (10 : ZMod 94208185177) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 64 * (10 : ZMod 94208185177) ^ 64 := by rw [pow_add]
          _ = 47286270062 := by rw [factor_3_6]; decide
      have factor_3_8 : (10 : ZMod 94208185177) ^ 257 = 67427915780 := by
        calc
          (10 : ZMod 94208185177) ^ 257 = (10 : ZMod 94208185177) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 128 * (10 : ZMod 94208185177) ^ 128) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 67427915780 := by rw [factor_3_7]; decide
      have factor_3_9 : (10 : ZMod 94208185177) ^ 514 = 16975169544 := by
        calc
          (10 : ZMod 94208185177) ^ 514 = (10 : ZMod 94208185177) ^ (257 + 257) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 257 * (10 : ZMod 94208185177) ^ 257 := by rw [pow_add]
          _ = 16975169544 := by rw [factor_3_8]; decide
      have factor_3_10 : (10 : ZMod 94208185177) ^ 1029 = 84064580983 := by
        calc
          (10 : ZMod 94208185177) ^ 1029 = (10 : ZMod 94208185177) ^ (514 + 514 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = ((10 : ZMod 94208185177) ^ 514 * (10 : ZMod 94208185177) ^ 514) * (10 : ZMod 94208185177) := by rw [pow_succ, pow_add]
          _ = 84064580983 := by rw [factor_3_9]; decide
      have factor_3_11 : (10 : ZMod 94208185177) ^ 2058 = 81272083801 := by
        calc
          (10 : ZMod 94208185177) ^ 2058 = (10 : ZMod 94208185177) ^ (1029 + 1029) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 1029 * (10 : ZMod 94208185177) ^ 1029 := by rw [pow_add]
          _ = 81272083801 := by rw [factor_3_10]; decide
      have factor_3_12 : (10 : ZMod 94208185177) ^ 4116 = 12333796627 := by
        calc
          (10 : ZMod 94208185177) ^ 4116 = (10 : ZMod 94208185177) ^ (2058 + 2058) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 2058 * (10 : ZMod 94208185177) ^ 2058 := by rw [pow_add]
          _ = 12333796627 := by rw [factor_3_11]; decide
      have factor_3_13 : (10 : ZMod 94208185177) ^ 8232 = 62143112318 := by
        calc
          (10 : ZMod 94208185177) ^ 8232 = (10 : ZMod 94208185177) ^ (4116 + 4116) :=
            congrArg (fun n : ℕ => (10 : ZMod 94208185177) ^ n) (by norm_num)
          _ = (10 : ZMod 94208185177) ^ 4116 * (10 : ZMod 94208185177) ^ 4116 := by rw [pow_add]
          _ = 62143112318 := by rw [factor_3_12]; decide
      change (10 : ZMod 94208185177) ^ 8232 ≠ 1
      rw [factor_3_13]
      decide

#print axioms prime_lucas_94208185177

end TotientTailPeriodKiller
end Erdos249257
