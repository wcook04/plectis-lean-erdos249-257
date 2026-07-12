import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1931549951

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_173839495591 : Nat.Prime 173839495591 := by
  apply lucas_primality 173839495591 (3 : ZMod 173839495591)
  ·
      have fermat_0 : (3 : ZMod 173839495591) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 173839495591) ^ 2 = 9 := by
        calc
          (3 : ZMod 173839495591) ^ 2 = (3 : ZMod 173839495591) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1 * (3 : ZMod 173839495591) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 173839495591) ^ 5 = 243 := by
        calc
          (3 : ZMod 173839495591) ^ 5 = (3 : ZMod 173839495591) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 2 * (3 : ZMod 173839495591) ^ 2) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 173839495591) ^ 10 = 59049 := by
        calc
          (3 : ZMod 173839495591) ^ 10 = (3 : ZMod 173839495591) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 5 * (3 : ZMod 173839495591) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 173839495591) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 173839495591) ^ 20 = (3 : ZMod 173839495591) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 10 * (3 : ZMod 173839495591) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 173839495591) ^ 40 = 71801422969 := by
        calc
          (3 : ZMod 173839495591) ^ 40 = (3 : ZMod 173839495591) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 20 * (3 : ZMod 173839495591) ^ 20 := by rw [pow_add]
          _ = 71801422969 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 173839495591) ^ 80 = 99151093085 := by
        calc
          (3 : ZMod 173839495591) ^ 80 = (3 : ZMod 173839495591) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 40 * (3 : ZMod 173839495591) ^ 40 := by rw [pow_add]
          _ = 99151093085 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 173839495591) ^ 161 = 77953163122 := by
        calc
          (3 : ZMod 173839495591) ^ 161 = (3 : ZMod 173839495591) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 80 * (3 : ZMod 173839495591) ^ 80) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 77953163122 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 173839495591) ^ 323 = 168080750812 := by
        calc
          (3 : ZMod 173839495591) ^ 323 = (3 : ZMod 173839495591) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 161 * (3 : ZMod 173839495591) ^ 161) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 168080750812 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 173839495591) ^ 647 = 28266391685 := by
        calc
          (3 : ZMod 173839495591) ^ 647 = (3 : ZMod 173839495591) ^ (323 + 323 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 323 * (3 : ZMod 173839495591) ^ 323) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 28266391685 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 173839495591) ^ 1295 = 116531252255 := by
        calc
          (3 : ZMod 173839495591) ^ 1295 = (3 : ZMod 173839495591) ^ (647 + 647 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 647 * (3 : ZMod 173839495591) ^ 647) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 116531252255 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 173839495591) ^ 2590 = 168299380813 := by
        calc
          (3 : ZMod 173839495591) ^ 2590 = (3 : ZMod 173839495591) ^ (1295 + 1295) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1295 * (3 : ZMod 173839495591) ^ 1295 := by rw [pow_add]
          _ = 168299380813 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 173839495591) ^ 5180 = 53840704995 := by
        calc
          (3 : ZMod 173839495591) ^ 5180 = (3 : ZMod 173839495591) ^ (2590 + 2590) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 2590 * (3 : ZMod 173839495591) ^ 2590 := by rw [pow_add]
          _ = 53840704995 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 173839495591) ^ 10361 = 95176366433 := by
        calc
          (3 : ZMod 173839495591) ^ 10361 = (3 : ZMod 173839495591) ^ (5180 + 5180 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 5180 * (3 : ZMod 173839495591) ^ 5180) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 95176366433 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 173839495591) ^ 20723 = 96607871436 := by
        calc
          (3 : ZMod 173839495591) ^ 20723 = (3 : ZMod 173839495591) ^ (10361 + 10361 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 10361 * (3 : ZMod 173839495591) ^ 10361) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 96607871436 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 173839495591) ^ 41446 = 88268222062 := by
        calc
          (3 : ZMod 173839495591) ^ 41446 = (3 : ZMod 173839495591) ^ (20723 + 20723) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 20723 * (3 : ZMod 173839495591) ^ 20723 := by rw [pow_add]
          _ = 88268222062 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 173839495591) ^ 82893 = 111161334135 := by
        calc
          (3 : ZMod 173839495591) ^ 82893 = (3 : ZMod 173839495591) ^ (41446 + 41446 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 41446 * (3 : ZMod 173839495591) ^ 41446) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 111161334135 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 173839495591) ^ 165786 = 44852627475 := by
        calc
          (3 : ZMod 173839495591) ^ 165786 = (3 : ZMod 173839495591) ^ (82893 + 82893) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 82893 * (3 : ZMod 173839495591) ^ 82893 := by rw [pow_add]
          _ = 44852627475 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 173839495591) ^ 331572 = 80661318569 := by
        calc
          (3 : ZMod 173839495591) ^ 331572 = (3 : ZMod 173839495591) ^ (165786 + 165786) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 165786 * (3 : ZMod 173839495591) ^ 165786 := by rw [pow_add]
          _ = 80661318569 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 173839495591) ^ 663145 = 97072803395 := by
        calc
          (3 : ZMod 173839495591) ^ 663145 = (3 : ZMod 173839495591) ^ (331572 + 331572 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 331572 * (3 : ZMod 173839495591) ^ 331572) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 97072803395 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 173839495591) ^ 1326290 = 24791279310 := by
        calc
          (3 : ZMod 173839495591) ^ 1326290 = (3 : ZMod 173839495591) ^ (663145 + 663145) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 663145 * (3 : ZMod 173839495591) ^ 663145 := by rw [pow_add]
          _ = 24791279310 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 173839495591) ^ 2652580 = 141430174195 := by
        calc
          (3 : ZMod 173839495591) ^ 2652580 = (3 : ZMod 173839495591) ^ (1326290 + 1326290) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1326290 * (3 : ZMod 173839495591) ^ 1326290 := by rw [pow_add]
          _ = 141430174195 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 173839495591) ^ 5305160 = 111976791918 := by
        calc
          (3 : ZMod 173839495591) ^ 5305160 = (3 : ZMod 173839495591) ^ (2652580 + 2652580) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 2652580 * (3 : ZMod 173839495591) ^ 2652580 := by rw [pow_add]
          _ = 111976791918 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 173839495591) ^ 10610320 = 135762080651 := by
        calc
          (3 : ZMod 173839495591) ^ 10610320 = (3 : ZMod 173839495591) ^ (5305160 + 5305160) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 5305160 * (3 : ZMod 173839495591) ^ 5305160 := by rw [pow_add]
          _ = 135762080651 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 173839495591) ^ 21220641 = 157884845270 := by
        calc
          (3 : ZMod 173839495591) ^ 21220641 = (3 : ZMod 173839495591) ^ (10610320 + 10610320 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 10610320 * (3 : ZMod 173839495591) ^ 10610320) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 157884845270 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 173839495591) ^ 42441283 = 95574308878 := by
        calc
          (3 : ZMod 173839495591) ^ 42441283 = (3 : ZMod 173839495591) ^ (21220641 + 21220641 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 21220641 * (3 : ZMod 173839495591) ^ 21220641) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 95574308878 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 173839495591) ^ 84882566 = 119939586893 := by
        calc
          (3 : ZMod 173839495591) ^ 84882566 = (3 : ZMod 173839495591) ^ (42441283 + 42441283) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 42441283 * (3 : ZMod 173839495591) ^ 42441283 := by rw [pow_add]
          _ = 119939586893 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 173839495591) ^ 169765132 = 142486244031 := by
        calc
          (3 : ZMod 173839495591) ^ 169765132 = (3 : ZMod 173839495591) ^ (84882566 + 84882566) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 84882566 * (3 : ZMod 173839495591) ^ 84882566 := by rw [pow_add]
          _ = 142486244031 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 173839495591) ^ 339530264 = 80064290862 := by
        calc
          (3 : ZMod 173839495591) ^ 339530264 = (3 : ZMod 173839495591) ^ (169765132 + 169765132) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 169765132 * (3 : ZMod 173839495591) ^ 169765132 := by rw [pow_add]
          _ = 80064290862 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 173839495591) ^ 679060529 = 169022164120 := by
        calc
          (3 : ZMod 173839495591) ^ 679060529 = (3 : ZMod 173839495591) ^ (339530264 + 339530264 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 339530264 * (3 : ZMod 173839495591) ^ 339530264) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 169022164120 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 173839495591) ^ 1358121059 = 42596840465 := by
        calc
          (3 : ZMod 173839495591) ^ 1358121059 = (3 : ZMod 173839495591) ^ (679060529 + 679060529 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 679060529 * (3 : ZMod 173839495591) ^ 679060529) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 42596840465 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 173839495591) ^ 2716242118 = 98482364332 := by
        calc
          (3 : ZMod 173839495591) ^ 2716242118 = (3 : ZMod 173839495591) ^ (1358121059 + 1358121059) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1358121059 * (3 : ZMod 173839495591) ^ 1358121059 := by rw [pow_add]
          _ = 98482364332 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 173839495591) ^ 5432484237 = 32490108239 := by
        calc
          (3 : ZMod 173839495591) ^ 5432484237 = (3 : ZMod 173839495591) ^ (2716242118 + 2716242118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 2716242118 * (3 : ZMod 173839495591) ^ 2716242118) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 32490108239 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 173839495591) ^ 10864968474 = 96925053303 := by
        calc
          (3 : ZMod 173839495591) ^ 10864968474 = (3 : ZMod 173839495591) ^ (5432484237 + 5432484237) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 5432484237 * (3 : ZMod 173839495591) ^ 5432484237 := by rw [pow_add]
          _ = 96925053303 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 173839495591) ^ 21729936948 = 43561216470 := by
        calc
          (3 : ZMod 173839495591) ^ 21729936948 = (3 : ZMod 173839495591) ^ (10864968474 + 10864968474) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 10864968474 * (3 : ZMod 173839495591) ^ 10864968474 := by rw [pow_add]
          _ = 43561216470 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 173839495591) ^ 43459873897 = 105845834971 := by
        calc
          (3 : ZMod 173839495591) ^ 43459873897 = (3 : ZMod 173839495591) ^ (21729936948 + 21729936948 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 21729936948 * (3 : ZMod 173839495591) ^ 21729936948) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 105845834971 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 173839495591) ^ 86919747795 = 173839495590 := by
        calc
          (3 : ZMod 173839495591) ^ 86919747795 = (3 : ZMod 173839495591) ^ (43459873897 + 43459873897 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 43459873897 * (3 : ZMod 173839495591) ^ 43459873897) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 173839495590 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 173839495591) ^ 173839495590 = 1 := by
        calc
          (3 : ZMod 173839495591) ^ 173839495590 = (3 : ZMod 173839495591) ^ (86919747795 + 86919747795) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 86919747795 * (3 : ZMod 173839495591) ^ 86919747795 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (1931549951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (1931549951, 1)] : List FactorBlock).map factorBlockValue).prod = 173839495591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_1931549951) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 173839495591) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 173839495591) ^ 2 = 9 := by
        calc
          (3 : ZMod 173839495591) ^ 2 = (3 : ZMod 173839495591) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1 * (3 : ZMod 173839495591) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 173839495591) ^ 5 = 243 := by
        calc
          (3 : ZMod 173839495591) ^ 5 = (3 : ZMod 173839495591) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 2 * (3 : ZMod 173839495591) ^ 2) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 173839495591) ^ 10 = 59049 := by
        calc
          (3 : ZMod 173839495591) ^ 10 = (3 : ZMod 173839495591) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 5 * (3 : ZMod 173839495591) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 173839495591) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 173839495591) ^ 20 = (3 : ZMod 173839495591) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 10 * (3 : ZMod 173839495591) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 173839495591) ^ 40 = 71801422969 := by
        calc
          (3 : ZMod 173839495591) ^ 40 = (3 : ZMod 173839495591) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 20 * (3 : ZMod 173839495591) ^ 20 := by rw [pow_add]
          _ = 71801422969 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 173839495591) ^ 80 = 99151093085 := by
        calc
          (3 : ZMod 173839495591) ^ 80 = (3 : ZMod 173839495591) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 40 * (3 : ZMod 173839495591) ^ 40 := by rw [pow_add]
          _ = 99151093085 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 173839495591) ^ 161 = 77953163122 := by
        calc
          (3 : ZMod 173839495591) ^ 161 = (3 : ZMod 173839495591) ^ (80 + 80 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 80 * (3 : ZMod 173839495591) ^ 80) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 77953163122 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 173839495591) ^ 323 = 168080750812 := by
        calc
          (3 : ZMod 173839495591) ^ 323 = (3 : ZMod 173839495591) ^ (161 + 161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 161 * (3 : ZMod 173839495591) ^ 161) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 168080750812 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 173839495591) ^ 647 = 28266391685 := by
        calc
          (3 : ZMod 173839495591) ^ 647 = (3 : ZMod 173839495591) ^ (323 + 323 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 323 * (3 : ZMod 173839495591) ^ 323) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 28266391685 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 173839495591) ^ 1295 = 116531252255 := by
        calc
          (3 : ZMod 173839495591) ^ 1295 = (3 : ZMod 173839495591) ^ (647 + 647 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 647 * (3 : ZMod 173839495591) ^ 647) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 116531252255 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 173839495591) ^ 2590 = 168299380813 := by
        calc
          (3 : ZMod 173839495591) ^ 2590 = (3 : ZMod 173839495591) ^ (1295 + 1295) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1295 * (3 : ZMod 173839495591) ^ 1295 := by rw [pow_add]
          _ = 168299380813 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 173839495591) ^ 5180 = 53840704995 := by
        calc
          (3 : ZMod 173839495591) ^ 5180 = (3 : ZMod 173839495591) ^ (2590 + 2590) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 2590 * (3 : ZMod 173839495591) ^ 2590 := by rw [pow_add]
          _ = 53840704995 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 173839495591) ^ 10361 = 95176366433 := by
        calc
          (3 : ZMod 173839495591) ^ 10361 = (3 : ZMod 173839495591) ^ (5180 + 5180 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 5180 * (3 : ZMod 173839495591) ^ 5180) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 95176366433 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 173839495591) ^ 20723 = 96607871436 := by
        calc
          (3 : ZMod 173839495591) ^ 20723 = (3 : ZMod 173839495591) ^ (10361 + 10361 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 10361 * (3 : ZMod 173839495591) ^ 10361) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 96607871436 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 173839495591) ^ 41446 = 88268222062 := by
        calc
          (3 : ZMod 173839495591) ^ 41446 = (3 : ZMod 173839495591) ^ (20723 + 20723) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 20723 * (3 : ZMod 173839495591) ^ 20723 := by rw [pow_add]
          _ = 88268222062 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 173839495591) ^ 82893 = 111161334135 := by
        calc
          (3 : ZMod 173839495591) ^ 82893 = (3 : ZMod 173839495591) ^ (41446 + 41446 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 41446 * (3 : ZMod 173839495591) ^ 41446) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 111161334135 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 173839495591) ^ 165786 = 44852627475 := by
        calc
          (3 : ZMod 173839495591) ^ 165786 = (3 : ZMod 173839495591) ^ (82893 + 82893) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 82893 * (3 : ZMod 173839495591) ^ 82893 := by rw [pow_add]
          _ = 44852627475 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 173839495591) ^ 331572 = 80661318569 := by
        calc
          (3 : ZMod 173839495591) ^ 331572 = (3 : ZMod 173839495591) ^ (165786 + 165786) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 165786 * (3 : ZMod 173839495591) ^ 165786 := by rw [pow_add]
          _ = 80661318569 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 173839495591) ^ 663145 = 97072803395 := by
        calc
          (3 : ZMod 173839495591) ^ 663145 = (3 : ZMod 173839495591) ^ (331572 + 331572 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 331572 * (3 : ZMod 173839495591) ^ 331572) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 97072803395 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 173839495591) ^ 1326290 = 24791279310 := by
        calc
          (3 : ZMod 173839495591) ^ 1326290 = (3 : ZMod 173839495591) ^ (663145 + 663145) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 663145 * (3 : ZMod 173839495591) ^ 663145 := by rw [pow_add]
          _ = 24791279310 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 173839495591) ^ 2652580 = 141430174195 := by
        calc
          (3 : ZMod 173839495591) ^ 2652580 = (3 : ZMod 173839495591) ^ (1326290 + 1326290) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1326290 * (3 : ZMod 173839495591) ^ 1326290 := by rw [pow_add]
          _ = 141430174195 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 173839495591) ^ 5305160 = 111976791918 := by
        calc
          (3 : ZMod 173839495591) ^ 5305160 = (3 : ZMod 173839495591) ^ (2652580 + 2652580) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 2652580 * (3 : ZMod 173839495591) ^ 2652580 := by rw [pow_add]
          _ = 111976791918 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 173839495591) ^ 10610320 = 135762080651 := by
        calc
          (3 : ZMod 173839495591) ^ 10610320 = (3 : ZMod 173839495591) ^ (5305160 + 5305160) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 5305160 * (3 : ZMod 173839495591) ^ 5305160 := by rw [pow_add]
          _ = 135762080651 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 173839495591) ^ 21220641 = 157884845270 := by
        calc
          (3 : ZMod 173839495591) ^ 21220641 = (3 : ZMod 173839495591) ^ (10610320 + 10610320 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 10610320 * (3 : ZMod 173839495591) ^ 10610320) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 157884845270 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 173839495591) ^ 42441283 = 95574308878 := by
        calc
          (3 : ZMod 173839495591) ^ 42441283 = (3 : ZMod 173839495591) ^ (21220641 + 21220641 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 21220641 * (3 : ZMod 173839495591) ^ 21220641) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 95574308878 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 173839495591) ^ 84882566 = 119939586893 := by
        calc
          (3 : ZMod 173839495591) ^ 84882566 = (3 : ZMod 173839495591) ^ (42441283 + 42441283) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 42441283 * (3 : ZMod 173839495591) ^ 42441283 := by rw [pow_add]
          _ = 119939586893 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 173839495591) ^ 169765132 = 142486244031 := by
        calc
          (3 : ZMod 173839495591) ^ 169765132 = (3 : ZMod 173839495591) ^ (84882566 + 84882566) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 84882566 * (3 : ZMod 173839495591) ^ 84882566 := by rw [pow_add]
          _ = 142486244031 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 173839495591) ^ 339530264 = 80064290862 := by
        calc
          (3 : ZMod 173839495591) ^ 339530264 = (3 : ZMod 173839495591) ^ (169765132 + 169765132) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 169765132 * (3 : ZMod 173839495591) ^ 169765132 := by rw [pow_add]
          _ = 80064290862 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 173839495591) ^ 679060529 = 169022164120 := by
        calc
          (3 : ZMod 173839495591) ^ 679060529 = (3 : ZMod 173839495591) ^ (339530264 + 339530264 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 339530264 * (3 : ZMod 173839495591) ^ 339530264) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 169022164120 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 173839495591) ^ 1358121059 = 42596840465 := by
        calc
          (3 : ZMod 173839495591) ^ 1358121059 = (3 : ZMod 173839495591) ^ (679060529 + 679060529 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 679060529 * (3 : ZMod 173839495591) ^ 679060529) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 42596840465 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 173839495591) ^ 2716242118 = 98482364332 := by
        calc
          (3 : ZMod 173839495591) ^ 2716242118 = (3 : ZMod 173839495591) ^ (1358121059 + 1358121059) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1358121059 * (3 : ZMod 173839495591) ^ 1358121059 := by rw [pow_add]
          _ = 98482364332 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 173839495591) ^ 5432484237 = 32490108239 := by
        calc
          (3 : ZMod 173839495591) ^ 5432484237 = (3 : ZMod 173839495591) ^ (2716242118 + 2716242118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 2716242118 * (3 : ZMod 173839495591) ^ 2716242118) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 32490108239 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 173839495591) ^ 10864968474 = 96925053303 := by
        calc
          (3 : ZMod 173839495591) ^ 10864968474 = (3 : ZMod 173839495591) ^ (5432484237 + 5432484237) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 5432484237 * (3 : ZMod 173839495591) ^ 5432484237 := by rw [pow_add]
          _ = 96925053303 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 173839495591) ^ 21729936948 = 43561216470 := by
        calc
          (3 : ZMod 173839495591) ^ 21729936948 = (3 : ZMod 173839495591) ^ (10864968474 + 10864968474) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 10864968474 * (3 : ZMod 173839495591) ^ 10864968474 := by rw [pow_add]
          _ = 43561216470 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 173839495591) ^ 43459873897 = 105845834971 := by
        calc
          (3 : ZMod 173839495591) ^ 43459873897 = (3 : ZMod 173839495591) ^ (21729936948 + 21729936948 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 21729936948 * (3 : ZMod 173839495591) ^ 21729936948) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 105845834971 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 173839495591) ^ 86919747795 = 173839495590 := by
        calc
          (3 : ZMod 173839495591) ^ 86919747795 = (3 : ZMod 173839495591) ^ (43459873897 + 43459873897 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 43459873897 * (3 : ZMod 173839495591) ^ 43459873897) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 173839495590 := by rw [factor_0_35]; decide
      change (3 : ZMod 173839495591) ^ 86919747795 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (3 : ZMod 173839495591) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 173839495591) ^ 3 = 27 := by
        calc
          (3 : ZMod 173839495591) ^ 3 = (3 : ZMod 173839495591) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 1 * (3 : ZMod 173839495591) ^ 1) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 173839495591) ^ 6 = 729 := by
        calc
          (3 : ZMod 173839495591) ^ 6 = (3 : ZMod 173839495591) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 3 * (3 : ZMod 173839495591) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 173839495591) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 173839495591) ^ 13 = (3 : ZMod 173839495591) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 6 * (3 : ZMod 173839495591) ^ 6) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 173839495591) ^ 26 = 108112890055 := by
        calc
          (3 : ZMod 173839495591) ^ 26 = (3 : ZMod 173839495591) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 13 * (3 : ZMod 173839495591) ^ 13 := by rw [pow_add]
          _ = 108112890055 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 173839495591) ^ 53 = 135349062350 := by
        calc
          (3 : ZMod 173839495591) ^ 53 = (3 : ZMod 173839495591) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 26 * (3 : ZMod 173839495591) ^ 26) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 135349062350 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 173839495591) ^ 107 = 50225441853 := by
        calc
          (3 : ZMod 173839495591) ^ 107 = (3 : ZMod 173839495591) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 53 * (3 : ZMod 173839495591) ^ 53) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 50225441853 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 173839495591) ^ 215 = 98869349772 := by
        calc
          (3 : ZMod 173839495591) ^ 215 = (3 : ZMod 173839495591) ^ (107 + 107 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 107 * (3 : ZMod 173839495591) ^ 107) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 98869349772 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 173839495591) ^ 431 = 58505304927 := by
        calc
          (3 : ZMod 173839495591) ^ 431 = (3 : ZMod 173839495591) ^ (215 + 215 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 215 * (3 : ZMod 173839495591) ^ 215) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 58505304927 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 173839495591) ^ 863 = 133820657881 := by
        calc
          (3 : ZMod 173839495591) ^ 863 = (3 : ZMod 173839495591) ^ (431 + 431 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 431 * (3 : ZMod 173839495591) ^ 431) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 133820657881 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 173839495591) ^ 1726 = 58481499747 := by
        calc
          (3 : ZMod 173839495591) ^ 1726 = (3 : ZMod 173839495591) ^ (863 + 863) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 863 * (3 : ZMod 173839495591) ^ 863 := by rw [pow_add]
          _ = 58481499747 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 173839495591) ^ 3453 = 49802162531 := by
        calc
          (3 : ZMod 173839495591) ^ 3453 = (3 : ZMod 173839495591) ^ (1726 + 1726 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 1726 * (3 : ZMod 173839495591) ^ 1726) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 49802162531 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 173839495591) ^ 6907 = 57233106363 := by
        calc
          (3 : ZMod 173839495591) ^ 6907 = (3 : ZMod 173839495591) ^ (3453 + 3453 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 3453 * (3 : ZMod 173839495591) ^ 3453) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 57233106363 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 173839495591) ^ 13815 = 89858201223 := by
        calc
          (3 : ZMod 173839495591) ^ 13815 = (3 : ZMod 173839495591) ^ (6907 + 6907 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 6907 * (3 : ZMod 173839495591) ^ 6907) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 89858201223 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 173839495591) ^ 27631 = 142340656754 := by
        calc
          (3 : ZMod 173839495591) ^ 27631 = (3 : ZMod 173839495591) ^ (13815 + 13815 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 13815 * (3 : ZMod 173839495591) ^ 13815) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 142340656754 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 173839495591) ^ 55262 = 146635807519 := by
        calc
          (3 : ZMod 173839495591) ^ 55262 = (3 : ZMod 173839495591) ^ (27631 + 27631) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 27631 * (3 : ZMod 173839495591) ^ 27631 := by rw [pow_add]
          _ = 146635807519 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 173839495591) ^ 110524 = 54222018456 := by
        calc
          (3 : ZMod 173839495591) ^ 110524 = (3 : ZMod 173839495591) ^ (55262 + 55262) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 55262 * (3 : ZMod 173839495591) ^ 55262 := by rw [pow_add]
          _ = 54222018456 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 173839495591) ^ 221048 = 133651498744 := by
        calc
          (3 : ZMod 173839495591) ^ 221048 = (3 : ZMod 173839495591) ^ (110524 + 110524) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 110524 * (3 : ZMod 173839495591) ^ 110524 := by rw [pow_add]
          _ = 133651498744 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 173839495591) ^ 442096 = 63851339566 := by
        calc
          (3 : ZMod 173839495591) ^ 442096 = (3 : ZMod 173839495591) ^ (221048 + 221048) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 221048 * (3 : ZMod 173839495591) ^ 221048 := by rw [pow_add]
          _ = 63851339566 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 173839495591) ^ 884193 = 48624542535 := by
        calc
          (3 : ZMod 173839495591) ^ 884193 = (3 : ZMod 173839495591) ^ (442096 + 442096 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 442096 * (3 : ZMod 173839495591) ^ 442096) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 48624542535 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 173839495591) ^ 1768386 = 145757898221 := by
        calc
          (3 : ZMod 173839495591) ^ 1768386 = (3 : ZMod 173839495591) ^ (884193 + 884193) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 884193 * (3 : ZMod 173839495591) ^ 884193 := by rw [pow_add]
          _ = 145757898221 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 173839495591) ^ 3536773 = 42896833197 := by
        calc
          (3 : ZMod 173839495591) ^ 3536773 = (3 : ZMod 173839495591) ^ (1768386 + 1768386 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 1768386 * (3 : ZMod 173839495591) ^ 1768386) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 42896833197 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 173839495591) ^ 7073547 = 109268399546 := by
        calc
          (3 : ZMod 173839495591) ^ 7073547 = (3 : ZMod 173839495591) ^ (3536773 + 3536773 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 3536773 * (3 : ZMod 173839495591) ^ 3536773) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 109268399546 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 173839495591) ^ 14147094 = 96993436612 := by
        calc
          (3 : ZMod 173839495591) ^ 14147094 = (3 : ZMod 173839495591) ^ (7073547 + 7073547) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 7073547 * (3 : ZMod 173839495591) ^ 7073547 := by rw [pow_add]
          _ = 96993436612 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 173839495591) ^ 28294188 = 163853457315 := by
        calc
          (3 : ZMod 173839495591) ^ 28294188 = (3 : ZMod 173839495591) ^ (14147094 + 14147094) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 14147094 * (3 : ZMod 173839495591) ^ 14147094 := by rw [pow_add]
          _ = 163853457315 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 173839495591) ^ 56588377 = 6773994815 := by
        calc
          (3 : ZMod 173839495591) ^ 56588377 = (3 : ZMod 173839495591) ^ (28294188 + 28294188 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 28294188 * (3 : ZMod 173839495591) ^ 28294188) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 6773994815 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 173839495591) ^ 113176754 = 116330954233 := by
        calc
          (3 : ZMod 173839495591) ^ 113176754 = (3 : ZMod 173839495591) ^ (56588377 + 56588377) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 56588377 * (3 : ZMod 173839495591) ^ 56588377 := by rw [pow_add]
          _ = 116330954233 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 173839495591) ^ 226353509 = 61832687515 := by
        calc
          (3 : ZMod 173839495591) ^ 226353509 = (3 : ZMod 173839495591) ^ (113176754 + 113176754 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 113176754 * (3 : ZMod 173839495591) ^ 113176754) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 61832687515 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 173839495591) ^ 452707019 = 78583306608 := by
        calc
          (3 : ZMod 173839495591) ^ 452707019 = (3 : ZMod 173839495591) ^ (226353509 + 226353509 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 226353509 * (3 : ZMod 173839495591) ^ 226353509) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 78583306608 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 173839495591) ^ 905414039 = 158156355159 := by
        calc
          (3 : ZMod 173839495591) ^ 905414039 = (3 : ZMod 173839495591) ^ (452707019 + 452707019 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 452707019 * (3 : ZMod 173839495591) ^ 452707019) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 158156355159 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 173839495591) ^ 1810828079 = 123305587693 := by
        calc
          (3 : ZMod 173839495591) ^ 1810828079 = (3 : ZMod 173839495591) ^ (905414039 + 905414039 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 905414039 * (3 : ZMod 173839495591) ^ 905414039) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 123305587693 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 173839495591) ^ 3621656158 = 153560656180 := by
        calc
          (3 : ZMod 173839495591) ^ 3621656158 = (3 : ZMod 173839495591) ^ (1810828079 + 1810828079) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1810828079 * (3 : ZMod 173839495591) ^ 1810828079 := by rw [pow_add]
          _ = 153560656180 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 173839495591) ^ 7243312316 = 3641427781 := by
        calc
          (3 : ZMod 173839495591) ^ 7243312316 = (3 : ZMod 173839495591) ^ (3621656158 + 3621656158) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 3621656158 * (3 : ZMod 173839495591) ^ 3621656158 := by rw [pow_add]
          _ = 3641427781 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 173839495591) ^ 14486624632 = 52922917485 := by
        calc
          (3 : ZMod 173839495591) ^ 14486624632 = (3 : ZMod 173839495591) ^ (7243312316 + 7243312316) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 7243312316 * (3 : ZMod 173839495591) ^ 7243312316 := by rw [pow_add]
          _ = 52922917485 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 173839495591) ^ 28973249265 = 15070743135 := by
        calc
          (3 : ZMod 173839495591) ^ 28973249265 = (3 : ZMod 173839495591) ^ (14486624632 + 14486624632 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 14486624632 * (3 : ZMod 173839495591) ^ 14486624632) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 15070743135 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 173839495591) ^ 57946498530 = 15070743134 := by
        calc
          (3 : ZMod 173839495591) ^ 57946498530 = (3 : ZMod 173839495591) ^ (28973249265 + 28973249265) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 28973249265 * (3 : ZMod 173839495591) ^ 28973249265 := by rw [pow_add]
          _ = 15070743134 := by rw [factor_1_34]; decide
      change (3 : ZMod 173839495591) ^ 57946498530 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (3 : ZMod 173839495591) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 173839495591) ^ 2 = 9 := by
        calc
          (3 : ZMod 173839495591) ^ 2 = (3 : ZMod 173839495591) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1 * (3 : ZMod 173839495591) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 173839495591) ^ 4 = 81 := by
        calc
          (3 : ZMod 173839495591) ^ 4 = (3 : ZMod 173839495591) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 2 * (3 : ZMod 173839495591) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 173839495591) ^ 8 = 6561 := by
        calc
          (3 : ZMod 173839495591) ^ 8 = (3 : ZMod 173839495591) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 4 * (3 : ZMod 173839495591) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 173839495591) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 173839495591) ^ 16 = (3 : ZMod 173839495591) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 8 * (3 : ZMod 173839495591) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 173839495591) ^ 32 = 65005347372 := by
        calc
          (3 : ZMod 173839495591) ^ 32 = (3 : ZMod 173839495591) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 16 * (3 : ZMod 173839495591) ^ 16 := by rw [pow_add]
          _ = 65005347372 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 173839495591) ^ 64 = 41758222366 := by
        calc
          (3 : ZMod 173839495591) ^ 64 = (3 : ZMod 173839495591) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 32 * (3 : ZMod 173839495591) ^ 32 := by rw [pow_add]
          _ = 41758222366 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 173839495591) ^ 129 = 110347136671 := by
        calc
          (3 : ZMod 173839495591) ^ 129 = (3 : ZMod 173839495591) ^ (64 + 64 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 64 * (3 : ZMod 173839495591) ^ 64) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 110347136671 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 173839495591) ^ 259 = 73369227467 := by
        calc
          (3 : ZMod 173839495591) ^ 259 = (3 : ZMod 173839495591) ^ (129 + 129 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 129 * (3 : ZMod 173839495591) ^ 129) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 73369227467 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 173839495591) ^ 518 = 29314225888 := by
        calc
          (3 : ZMod 173839495591) ^ 518 = (3 : ZMod 173839495591) ^ (259 + 259) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 259 * (3 : ZMod 173839495591) ^ 259 := by rw [pow_add]
          _ = 29314225888 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 173839495591) ^ 1036 = 125828466766 := by
        calc
          (3 : ZMod 173839495591) ^ 1036 = (3 : ZMod 173839495591) ^ (518 + 518) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 518 * (3 : ZMod 173839495591) ^ 518 := by rw [pow_add]
          _ = 125828466766 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 173839495591) ^ 2072 = 167451161885 := by
        calc
          (3 : ZMod 173839495591) ^ 2072 = (3 : ZMod 173839495591) ^ (1036 + 1036) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1036 * (3 : ZMod 173839495591) ^ 1036 := by rw [pow_add]
          _ = 167451161885 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 173839495591) ^ 4144 = 6830812852 := by
        calc
          (3 : ZMod 173839495591) ^ 4144 = (3 : ZMod 173839495591) ^ (2072 + 2072) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 2072 * (3 : ZMod 173839495591) ^ 2072 := by rw [pow_add]
          _ = 6830812852 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 173839495591) ^ 8289 = 168505800930 := by
        calc
          (3 : ZMod 173839495591) ^ 8289 = (3 : ZMod 173839495591) ^ (4144 + 4144 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 4144 * (3 : ZMod 173839495591) ^ 4144) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 168505800930 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 173839495591) ^ 16578 = 13601192837 := by
        calc
          (3 : ZMod 173839495591) ^ 16578 = (3 : ZMod 173839495591) ^ (8289 + 8289) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 8289 * (3 : ZMod 173839495591) ^ 8289 := by rw [pow_add]
          _ = 13601192837 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 173839495591) ^ 33157 = 46279673907 := by
        calc
          (3 : ZMod 173839495591) ^ 33157 = (3 : ZMod 173839495591) ^ (16578 + 16578 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 16578 * (3 : ZMod 173839495591) ^ 16578) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 46279673907 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 173839495591) ^ 66314 = 121393711773 := by
        calc
          (3 : ZMod 173839495591) ^ 66314 = (3 : ZMod 173839495591) ^ (33157 + 33157) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 33157 * (3 : ZMod 173839495591) ^ 33157 := by rw [pow_add]
          _ = 121393711773 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 173839495591) ^ 132629 = 100212560276 := by
        calc
          (3 : ZMod 173839495591) ^ 132629 = (3 : ZMod 173839495591) ^ (66314 + 66314 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 66314 * (3 : ZMod 173839495591) ^ 66314) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 100212560276 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 173839495591) ^ 265258 = 94398088476 := by
        calc
          (3 : ZMod 173839495591) ^ 265258 = (3 : ZMod 173839495591) ^ (132629 + 132629) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 132629 * (3 : ZMod 173839495591) ^ 132629 := by rw [pow_add]
          _ = 94398088476 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 173839495591) ^ 530516 = 156517726557 := by
        calc
          (3 : ZMod 173839495591) ^ 530516 = (3 : ZMod 173839495591) ^ (265258 + 265258) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 265258 * (3 : ZMod 173839495591) ^ 265258 := by rw [pow_add]
          _ = 156517726557 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 173839495591) ^ 1061032 = 34357927784 := by
        calc
          (3 : ZMod 173839495591) ^ 1061032 = (3 : ZMod 173839495591) ^ (530516 + 530516) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 530516 * (3 : ZMod 173839495591) ^ 530516 := by rw [pow_add]
          _ = 34357927784 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 173839495591) ^ 2122064 = 119278981098 := by
        calc
          (3 : ZMod 173839495591) ^ 2122064 = (3 : ZMod 173839495591) ^ (1061032 + 1061032) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1061032 * (3 : ZMod 173839495591) ^ 1061032 := by rw [pow_add]
          _ = 119278981098 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 173839495591) ^ 4244128 = 119289578975 := by
        calc
          (3 : ZMod 173839495591) ^ 4244128 = (3 : ZMod 173839495591) ^ (2122064 + 2122064) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 2122064 * (3 : ZMod 173839495591) ^ 2122064 := by rw [pow_add]
          _ = 119289578975 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 173839495591) ^ 8488256 = 141850804724 := by
        calc
          (3 : ZMod 173839495591) ^ 8488256 = (3 : ZMod 173839495591) ^ (4244128 + 4244128) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 4244128 * (3 : ZMod 173839495591) ^ 4244128 := by rw [pow_add]
          _ = 141850804724 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 173839495591) ^ 16976513 = 54629120893 := by
        calc
          (3 : ZMod 173839495591) ^ 16976513 = (3 : ZMod 173839495591) ^ (8488256 + 8488256 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 8488256 * (3 : ZMod 173839495591) ^ 8488256) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 54629120893 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 173839495591) ^ 33953026 = 35515691821 := by
        calc
          (3 : ZMod 173839495591) ^ 33953026 = (3 : ZMod 173839495591) ^ (16976513 + 16976513) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 16976513 * (3 : ZMod 173839495591) ^ 16976513 := by rw [pow_add]
          _ = 35515691821 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 173839495591) ^ 67906052 = 33184490711 := by
        calc
          (3 : ZMod 173839495591) ^ 67906052 = (3 : ZMod 173839495591) ^ (33953026 + 33953026) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 33953026 * (3 : ZMod 173839495591) ^ 33953026 := by rw [pow_add]
          _ = 33184490711 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 173839495591) ^ 135812105 = 115410022511 := by
        calc
          (3 : ZMod 173839495591) ^ 135812105 = (3 : ZMod 173839495591) ^ (67906052 + 67906052 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 67906052 * (3 : ZMod 173839495591) ^ 67906052) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 115410022511 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 173839495591) ^ 271624211 = 39515646687 := by
        calc
          (3 : ZMod 173839495591) ^ 271624211 = (3 : ZMod 173839495591) ^ (135812105 + 135812105 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 135812105 * (3 : ZMod 173839495591) ^ 135812105) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 39515646687 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 173839495591) ^ 543248423 = 83458230711 := by
        calc
          (3 : ZMod 173839495591) ^ 543248423 = (3 : ZMod 173839495591) ^ (271624211 + 271624211 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 271624211 * (3 : ZMod 173839495591) ^ 271624211) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 83458230711 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 173839495591) ^ 1086496847 = 105223466643 := by
        calc
          (3 : ZMod 173839495591) ^ 1086496847 = (3 : ZMod 173839495591) ^ (543248423 + 543248423 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 543248423 * (3 : ZMod 173839495591) ^ 543248423) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 105223466643 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 173839495591) ^ 2172993694 = 39454055633 := by
        calc
          (3 : ZMod 173839495591) ^ 2172993694 = (3 : ZMod 173839495591) ^ (1086496847 + 1086496847) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1086496847 * (3 : ZMod 173839495591) ^ 1086496847 := by rw [pow_add]
          _ = 39454055633 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 173839495591) ^ 4345987389 = 86698995827 := by
        calc
          (3 : ZMod 173839495591) ^ 4345987389 = (3 : ZMod 173839495591) ^ (2172993694 + 2172993694 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 2172993694 * (3 : ZMod 173839495591) ^ 2172993694) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 86698995827 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 173839495591) ^ 8691974779 = 103043846627 := by
        calc
          (3 : ZMod 173839495591) ^ 8691974779 = (3 : ZMod 173839495591) ^ (4345987389 + 4345987389 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 4345987389 * (3 : ZMod 173839495591) ^ 4345987389) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 103043846627 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 173839495591) ^ 17383949559 = 31160867313 := by
        calc
          (3 : ZMod 173839495591) ^ 17383949559 = (3 : ZMod 173839495591) ^ (8691974779 + 8691974779 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 8691974779 * (3 : ZMod 173839495591) ^ 8691974779) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 31160867313 := by rw [factor_2_33]; decide
      have factor_2_35 : (3 : ZMod 173839495591) ^ 34767899118 = 132903504546 := by
        calc
          (3 : ZMod 173839495591) ^ 34767899118 = (3 : ZMod 173839495591) ^ (17383949559 + 17383949559) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 17383949559 * (3 : ZMod 173839495591) ^ 17383949559 := by rw [pow_add]
          _ = 132903504546 := by rw [factor_2_34]; decide
      change (3 : ZMod 173839495591) ^ 34767899118 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (3 : ZMod 173839495591) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 173839495591) ^ 2 = 9 := by
        calc
          (3 : ZMod 173839495591) ^ 2 = (3 : ZMod 173839495591) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 1 * (3 : ZMod 173839495591) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 173839495591) ^ 5 = 243 := by
        calc
          (3 : ZMod 173839495591) ^ 5 = (3 : ZMod 173839495591) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 2 * (3 : ZMod 173839495591) ^ 2) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 173839495591) ^ 11 = 177147 := by
        calc
          (3 : ZMod 173839495591) ^ 11 = (3 : ZMod 173839495591) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 5 * (3 : ZMod 173839495591) ^ 5) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 173839495591) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 173839495591) ^ 22 = (3 : ZMod 173839495591) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 11 * (3 : ZMod 173839495591) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 173839495591) ^ 45 = 63796222367 := by
        calc
          (3 : ZMod 173839495591) ^ 45 = (3 : ZMod 173839495591) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = ((3 : ZMod 173839495591) ^ 22 * (3 : ZMod 173839495591) ^ 22) * (3 : ZMod 173839495591) := by rw [pow_succ, pow_add]
          _ = 63796222367 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 173839495591) ^ 90 = 32523566876 := by
        calc
          (3 : ZMod 173839495591) ^ 90 = (3 : ZMod 173839495591) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (3 : ZMod 173839495591) ^ n) (by norm_num)
          _ = (3 : ZMod 173839495591) ^ 45 * (3 : ZMod 173839495591) ^ 45 := by rw [pow_add]
          _ = 32523566876 := by rw [factor_3_5]; decide
      change (3 : ZMod 173839495591) ^ 90 ≠ 1
      rw [factor_3_6]
      decide

#print axioms prime_lucas_173839495591

end TotientTailPeriodKiller
end Erdos249257
