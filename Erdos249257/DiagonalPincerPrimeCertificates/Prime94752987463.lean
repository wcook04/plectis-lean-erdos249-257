import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=31 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_94752987463 : Nat.Prime 94752987463 := by
  apply lucas_primality 94752987463 (3 : ZMod 94752987463)
  ·
      have fermat_0 : (3 : ZMod 94752987463) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 94752987463) ^ 2 = 9 := by
        calc
          (3 : ZMod 94752987463) ^ 2 = (3 : ZMod 94752987463) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1 * (3 : ZMod 94752987463) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 94752987463) ^ 5 = 243 := by
        calc
          (3 : ZMod 94752987463) ^ 5 = (3 : ZMod 94752987463) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 2 * (3 : ZMod 94752987463) ^ 2) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 94752987463) ^ 11 = 177147 := by
        calc
          (3 : ZMod 94752987463) ^ 11 = (3 : ZMod 94752987463) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 5 * (3 : ZMod 94752987463) ^ 5) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 94752987463) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 94752987463) ^ 22 = (3 : ZMod 94752987463) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 11 * (3 : ZMod 94752987463) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 94752987463) ^ 44 = 36053857242 := by
        calc
          (3 : ZMod 94752987463) ^ 44 = (3 : ZMod 94752987463) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 22 * (3 : ZMod 94752987463) ^ 22 := by rw [pow_add]
          _ = 36053857242 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 94752987463) ^ 88 = 26709802577 := by
        calc
          (3 : ZMod 94752987463) ^ 88 = (3 : ZMod 94752987463) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 44 * (3 : ZMod 94752987463) ^ 44 := by rw [pow_add]
          _ = 26709802577 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 94752987463) ^ 176 = 78561616179 := by
        calc
          (3 : ZMod 94752987463) ^ 176 = (3 : ZMod 94752987463) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 88 * (3 : ZMod 94752987463) ^ 88 := by rw [pow_add]
          _ = 78561616179 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 94752987463) ^ 352 = 73965616073 := by
        calc
          (3 : ZMod 94752987463) ^ 352 = (3 : ZMod 94752987463) ^ (176 + 176) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 176 * (3 : ZMod 94752987463) ^ 176 := by rw [pow_add]
          _ = 73965616073 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 94752987463) ^ 705 = 11832044892 := by
        calc
          (3 : ZMod 94752987463) ^ 705 = (3 : ZMod 94752987463) ^ (352 + 352 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 352 * (3 : ZMod 94752987463) ^ 352) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 11832044892 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 94752987463) ^ 1411 = 73062078992 := by
        calc
          (3 : ZMod 94752987463) ^ 1411 = (3 : ZMod 94752987463) ^ (705 + 705 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 705 * (3 : ZMod 94752987463) ^ 705) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 73062078992 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 94752987463) ^ 2823 = 63035960068 := by
        calc
          (3 : ZMod 94752987463) ^ 2823 = (3 : ZMod 94752987463) ^ (1411 + 1411 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1411 * (3 : ZMod 94752987463) ^ 1411) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 63035960068 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 94752987463) ^ 5647 = 36332347236 := by
        calc
          (3 : ZMod 94752987463) ^ 5647 = (3 : ZMod 94752987463) ^ (2823 + 2823 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 2823 * (3 : ZMod 94752987463) ^ 2823) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 36332347236 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 94752987463) ^ 11295 = 9577458468 := by
        calc
          (3 : ZMod 94752987463) ^ 11295 = (3 : ZMod 94752987463) ^ (5647 + 5647 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 5647 * (3 : ZMod 94752987463) ^ 5647) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 9577458468 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 94752987463) ^ 22590 = 38091119692 := by
        calc
          (3 : ZMod 94752987463) ^ 22590 = (3 : ZMod 94752987463) ^ (11295 + 11295) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 11295 * (3 : ZMod 94752987463) ^ 11295 := by rw [pow_add]
          _ = 38091119692 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 94752987463) ^ 45181 = 70440952320 := by
        calc
          (3 : ZMod 94752987463) ^ 45181 = (3 : ZMod 94752987463) ^ (22590 + 22590 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 22590 * (3 : ZMod 94752987463) ^ 22590) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 70440952320 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 94752987463) ^ 90363 = 70900760390 := by
        calc
          (3 : ZMod 94752987463) ^ 90363 = (3 : ZMod 94752987463) ^ (45181 + 45181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 45181 * (3 : ZMod 94752987463) ^ 45181) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 70900760390 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 94752987463) ^ 180726 = 37744627214 := by
        calc
          (3 : ZMod 94752987463) ^ 180726 = (3 : ZMod 94752987463) ^ (90363 + 90363) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 90363 * (3 : ZMod 94752987463) ^ 90363 := by rw [pow_add]
          _ = 37744627214 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 94752987463) ^ 361453 = 83145986334 := by
        calc
          (3 : ZMod 94752987463) ^ 361453 = (3 : ZMod 94752987463) ^ (180726 + 180726 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 180726 * (3 : ZMod 94752987463) ^ 180726) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 83145986334 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 94752987463) ^ 722907 = 27123473172 := by
        calc
          (3 : ZMod 94752987463) ^ 722907 = (3 : ZMod 94752987463) ^ (361453 + 361453 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 361453 * (3 : ZMod 94752987463) ^ 361453) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 27123473172 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 94752987463) ^ 1445815 = 37964022093 := by
        calc
          (3 : ZMod 94752987463) ^ 1445815 = (3 : ZMod 94752987463) ^ (722907 + 722907 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 722907 * (3 : ZMod 94752987463) ^ 722907) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 37964022093 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 94752987463) ^ 2891631 = 72778218002 := by
        calc
          (3 : ZMod 94752987463) ^ 2891631 = (3 : ZMod 94752987463) ^ (1445815 + 1445815 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1445815 * (3 : ZMod 94752987463) ^ 1445815) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 72778218002 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 94752987463) ^ 5783263 = 85763541408 := by
        calc
          (3 : ZMod 94752987463) ^ 5783263 = (3 : ZMod 94752987463) ^ (2891631 + 2891631 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 2891631 * (3 : ZMod 94752987463) ^ 2891631) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 85763541408 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 94752987463) ^ 11566526 = 61202784485 := by
        calc
          (3 : ZMod 94752987463) ^ 11566526 = (3 : ZMod 94752987463) ^ (5783263 + 5783263) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 5783263 * (3 : ZMod 94752987463) ^ 5783263 := by rw [pow_add]
          _ = 61202784485 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 94752987463) ^ 23133053 = 19797931217 := by
        calc
          (3 : ZMod 94752987463) ^ 23133053 = (3 : ZMod 94752987463) ^ (11566526 + 11566526 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 11566526 * (3 : ZMod 94752987463) ^ 11566526) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 19797931217 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 94752987463) ^ 46266107 = 6148118343 := by
        calc
          (3 : ZMod 94752987463) ^ 46266107 = (3 : ZMod 94752987463) ^ (23133053 + 23133053 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 23133053 * (3 : ZMod 94752987463) ^ 23133053) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 6148118343 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 94752987463) ^ 92532214 = 42361912362 := by
        calc
          (3 : ZMod 94752987463) ^ 92532214 = (3 : ZMod 94752987463) ^ (46266107 + 46266107) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 46266107 * (3 : ZMod 94752987463) ^ 46266107 := by rw [pow_add]
          _ = 42361912362 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 94752987463) ^ 185064428 = 19507114246 := by
        calc
          (3 : ZMod 94752987463) ^ 185064428 = (3 : ZMod 94752987463) ^ (92532214 + 92532214) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 92532214 * (3 : ZMod 94752987463) ^ 92532214 := by rw [pow_add]
          _ = 19507114246 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 94752987463) ^ 370128857 = 21749369828 := by
        calc
          (3 : ZMod 94752987463) ^ 370128857 = (3 : ZMod 94752987463) ^ (185064428 + 185064428 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 185064428 * (3 : ZMod 94752987463) ^ 185064428) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 21749369828 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 94752987463) ^ 740257714 = 78010576386 := by
        calc
          (3 : ZMod 94752987463) ^ 740257714 = (3 : ZMod 94752987463) ^ (370128857 + 370128857) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 370128857 * (3 : ZMod 94752987463) ^ 370128857 := by rw [pow_add]
          _ = 78010576386 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 94752987463) ^ 1480515429 = 78607800142 := by
        calc
          (3 : ZMod 94752987463) ^ 1480515429 = (3 : ZMod 94752987463) ^ (740257714 + 740257714 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 740257714 * (3 : ZMod 94752987463) ^ 740257714) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 78607800142 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 94752987463) ^ 2961030858 = 3858533821 := by
        calc
          (3 : ZMod 94752987463) ^ 2961030858 = (3 : ZMod 94752987463) ^ (1480515429 + 1480515429) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1480515429 * (3 : ZMod 94752987463) ^ 1480515429 := by rw [pow_add]
          _ = 3858533821 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 94752987463) ^ 5922061716 = 76240095955 := by
        calc
          (3 : ZMod 94752987463) ^ 5922061716 = (3 : ZMod 94752987463) ^ (2961030858 + 2961030858) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 2961030858 * (3 : ZMod 94752987463) ^ 2961030858 := by rw [pow_add]
          _ = 76240095955 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 94752987463) ^ 11844123432 = 32361974358 := by
        calc
          (3 : ZMod 94752987463) ^ 11844123432 = (3 : ZMod 94752987463) ^ (5922061716 + 5922061716) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 5922061716 * (3 : ZMod 94752987463) ^ 5922061716 := by rw [pow_add]
          _ = 32361974358 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 94752987463) ^ 23688246865 = 28308721431 := by
        calc
          (3 : ZMod 94752987463) ^ 23688246865 = (3 : ZMod 94752987463) ^ (11844123432 + 11844123432 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 11844123432 * (3 : ZMod 94752987463) ^ 11844123432) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 28308721431 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 94752987463) ^ 47376493731 = 94752987462 := by
        calc
          (3 : ZMod 94752987463) ^ 47376493731 = (3 : ZMod 94752987463) ^ (23688246865 + 23688246865 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 23688246865 * (3 : ZMod 94752987463) ^ 23688246865) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 94752987462 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 94752987463) ^ 94752987462 = 1 := by
        calc
          (3 : ZMod 94752987463) ^ 94752987462 = (3 : ZMod 94752987463) ^ (47376493731 + 47376493731) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 47376493731 * (3 : ZMod 94752987463) ^ 47376493731 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 2), (331, 1), (108187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 2), (331, 1), (108187, 1)] : List FactorBlock).map factorBlockValue).prod = 94752987463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 94752987463) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 94752987463) ^ 2 = 9 := by
        calc
          (3 : ZMod 94752987463) ^ 2 = (3 : ZMod 94752987463) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1 * (3 : ZMod 94752987463) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 94752987463) ^ 5 = 243 := by
        calc
          (3 : ZMod 94752987463) ^ 5 = (3 : ZMod 94752987463) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 2 * (3 : ZMod 94752987463) ^ 2) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 94752987463) ^ 11 = 177147 := by
        calc
          (3 : ZMod 94752987463) ^ 11 = (3 : ZMod 94752987463) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 5 * (3 : ZMod 94752987463) ^ 5) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 94752987463) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 94752987463) ^ 22 = (3 : ZMod 94752987463) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 11 * (3 : ZMod 94752987463) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 94752987463) ^ 44 = 36053857242 := by
        calc
          (3 : ZMod 94752987463) ^ 44 = (3 : ZMod 94752987463) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 22 * (3 : ZMod 94752987463) ^ 22 := by rw [pow_add]
          _ = 36053857242 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 94752987463) ^ 88 = 26709802577 := by
        calc
          (3 : ZMod 94752987463) ^ 88 = (3 : ZMod 94752987463) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 44 * (3 : ZMod 94752987463) ^ 44 := by rw [pow_add]
          _ = 26709802577 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 94752987463) ^ 176 = 78561616179 := by
        calc
          (3 : ZMod 94752987463) ^ 176 = (3 : ZMod 94752987463) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 88 * (3 : ZMod 94752987463) ^ 88 := by rw [pow_add]
          _ = 78561616179 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 94752987463) ^ 352 = 73965616073 := by
        calc
          (3 : ZMod 94752987463) ^ 352 = (3 : ZMod 94752987463) ^ (176 + 176) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 176 * (3 : ZMod 94752987463) ^ 176 := by rw [pow_add]
          _ = 73965616073 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 94752987463) ^ 705 = 11832044892 := by
        calc
          (3 : ZMod 94752987463) ^ 705 = (3 : ZMod 94752987463) ^ (352 + 352 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 352 * (3 : ZMod 94752987463) ^ 352) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 11832044892 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 94752987463) ^ 1411 = 73062078992 := by
        calc
          (3 : ZMod 94752987463) ^ 1411 = (3 : ZMod 94752987463) ^ (705 + 705 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 705 * (3 : ZMod 94752987463) ^ 705) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 73062078992 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 94752987463) ^ 2823 = 63035960068 := by
        calc
          (3 : ZMod 94752987463) ^ 2823 = (3 : ZMod 94752987463) ^ (1411 + 1411 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1411 * (3 : ZMod 94752987463) ^ 1411) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 63035960068 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 94752987463) ^ 5647 = 36332347236 := by
        calc
          (3 : ZMod 94752987463) ^ 5647 = (3 : ZMod 94752987463) ^ (2823 + 2823 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 2823 * (3 : ZMod 94752987463) ^ 2823) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 36332347236 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 94752987463) ^ 11295 = 9577458468 := by
        calc
          (3 : ZMod 94752987463) ^ 11295 = (3 : ZMod 94752987463) ^ (5647 + 5647 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 5647 * (3 : ZMod 94752987463) ^ 5647) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 9577458468 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 94752987463) ^ 22590 = 38091119692 := by
        calc
          (3 : ZMod 94752987463) ^ 22590 = (3 : ZMod 94752987463) ^ (11295 + 11295) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 11295 * (3 : ZMod 94752987463) ^ 11295 := by rw [pow_add]
          _ = 38091119692 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 94752987463) ^ 45181 = 70440952320 := by
        calc
          (3 : ZMod 94752987463) ^ 45181 = (3 : ZMod 94752987463) ^ (22590 + 22590 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 22590 * (3 : ZMod 94752987463) ^ 22590) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 70440952320 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 94752987463) ^ 90363 = 70900760390 := by
        calc
          (3 : ZMod 94752987463) ^ 90363 = (3 : ZMod 94752987463) ^ (45181 + 45181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 45181 * (3 : ZMod 94752987463) ^ 45181) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 70900760390 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 94752987463) ^ 180726 = 37744627214 := by
        calc
          (3 : ZMod 94752987463) ^ 180726 = (3 : ZMod 94752987463) ^ (90363 + 90363) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 90363 * (3 : ZMod 94752987463) ^ 90363 := by rw [pow_add]
          _ = 37744627214 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 94752987463) ^ 361453 = 83145986334 := by
        calc
          (3 : ZMod 94752987463) ^ 361453 = (3 : ZMod 94752987463) ^ (180726 + 180726 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 180726 * (3 : ZMod 94752987463) ^ 180726) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 83145986334 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 94752987463) ^ 722907 = 27123473172 := by
        calc
          (3 : ZMod 94752987463) ^ 722907 = (3 : ZMod 94752987463) ^ (361453 + 361453 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 361453 * (3 : ZMod 94752987463) ^ 361453) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 27123473172 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 94752987463) ^ 1445815 = 37964022093 := by
        calc
          (3 : ZMod 94752987463) ^ 1445815 = (3 : ZMod 94752987463) ^ (722907 + 722907 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 722907 * (3 : ZMod 94752987463) ^ 722907) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 37964022093 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 94752987463) ^ 2891631 = 72778218002 := by
        calc
          (3 : ZMod 94752987463) ^ 2891631 = (3 : ZMod 94752987463) ^ (1445815 + 1445815 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1445815 * (3 : ZMod 94752987463) ^ 1445815) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 72778218002 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 94752987463) ^ 5783263 = 85763541408 := by
        calc
          (3 : ZMod 94752987463) ^ 5783263 = (3 : ZMod 94752987463) ^ (2891631 + 2891631 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 2891631 * (3 : ZMod 94752987463) ^ 2891631) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 85763541408 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 94752987463) ^ 11566526 = 61202784485 := by
        calc
          (3 : ZMod 94752987463) ^ 11566526 = (3 : ZMod 94752987463) ^ (5783263 + 5783263) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 5783263 * (3 : ZMod 94752987463) ^ 5783263 := by rw [pow_add]
          _ = 61202784485 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 94752987463) ^ 23133053 = 19797931217 := by
        calc
          (3 : ZMod 94752987463) ^ 23133053 = (3 : ZMod 94752987463) ^ (11566526 + 11566526 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 11566526 * (3 : ZMod 94752987463) ^ 11566526) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 19797931217 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 94752987463) ^ 46266107 = 6148118343 := by
        calc
          (3 : ZMod 94752987463) ^ 46266107 = (3 : ZMod 94752987463) ^ (23133053 + 23133053 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 23133053 * (3 : ZMod 94752987463) ^ 23133053) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 6148118343 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 94752987463) ^ 92532214 = 42361912362 := by
        calc
          (3 : ZMod 94752987463) ^ 92532214 = (3 : ZMod 94752987463) ^ (46266107 + 46266107) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 46266107 * (3 : ZMod 94752987463) ^ 46266107 := by rw [pow_add]
          _ = 42361912362 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 94752987463) ^ 185064428 = 19507114246 := by
        calc
          (3 : ZMod 94752987463) ^ 185064428 = (3 : ZMod 94752987463) ^ (92532214 + 92532214) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 92532214 * (3 : ZMod 94752987463) ^ 92532214 := by rw [pow_add]
          _ = 19507114246 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 94752987463) ^ 370128857 = 21749369828 := by
        calc
          (3 : ZMod 94752987463) ^ 370128857 = (3 : ZMod 94752987463) ^ (185064428 + 185064428 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 185064428 * (3 : ZMod 94752987463) ^ 185064428) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 21749369828 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 94752987463) ^ 740257714 = 78010576386 := by
        calc
          (3 : ZMod 94752987463) ^ 740257714 = (3 : ZMod 94752987463) ^ (370128857 + 370128857) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 370128857 * (3 : ZMod 94752987463) ^ 370128857 := by rw [pow_add]
          _ = 78010576386 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 94752987463) ^ 1480515429 = 78607800142 := by
        calc
          (3 : ZMod 94752987463) ^ 1480515429 = (3 : ZMod 94752987463) ^ (740257714 + 740257714 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 740257714 * (3 : ZMod 94752987463) ^ 740257714) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 78607800142 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 94752987463) ^ 2961030858 = 3858533821 := by
        calc
          (3 : ZMod 94752987463) ^ 2961030858 = (3 : ZMod 94752987463) ^ (1480515429 + 1480515429) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1480515429 * (3 : ZMod 94752987463) ^ 1480515429 := by rw [pow_add]
          _ = 3858533821 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 94752987463) ^ 5922061716 = 76240095955 := by
        calc
          (3 : ZMod 94752987463) ^ 5922061716 = (3 : ZMod 94752987463) ^ (2961030858 + 2961030858) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 2961030858 * (3 : ZMod 94752987463) ^ 2961030858 := by rw [pow_add]
          _ = 76240095955 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 94752987463) ^ 11844123432 = 32361974358 := by
        calc
          (3 : ZMod 94752987463) ^ 11844123432 = (3 : ZMod 94752987463) ^ (5922061716 + 5922061716) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 5922061716 * (3 : ZMod 94752987463) ^ 5922061716 := by rw [pow_add]
          _ = 32361974358 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 94752987463) ^ 23688246865 = 28308721431 := by
        calc
          (3 : ZMod 94752987463) ^ 23688246865 = (3 : ZMod 94752987463) ^ (11844123432 + 11844123432 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 11844123432 * (3 : ZMod 94752987463) ^ 11844123432) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 28308721431 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 94752987463) ^ 47376493731 = 94752987462 := by
        calc
          (3 : ZMod 94752987463) ^ 47376493731 = (3 : ZMod 94752987463) ^ (23688246865 + 23688246865 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 23688246865 * (3 : ZMod 94752987463) ^ 23688246865) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 94752987462 := by rw [factor_0_34]; decide
      change (3 : ZMod 94752987463) ^ 47376493731 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (3 : ZMod 94752987463) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 94752987463) ^ 3 = 27 := by
        calc
          (3 : ZMod 94752987463) ^ 3 = (3 : ZMod 94752987463) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1 * (3 : ZMod 94752987463) ^ 1) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 94752987463) ^ 7 = 2187 := by
        calc
          (3 : ZMod 94752987463) ^ 7 = (3 : ZMod 94752987463) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 3 * (3 : ZMod 94752987463) ^ 3) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 94752987463) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 94752987463) ^ 14 = (3 : ZMod 94752987463) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 7 * (3 : ZMod 94752987463) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 94752987463) ^ 29 = 29214441671 := by
        calc
          (3 : ZMod 94752987463) ^ 29 = (3 : ZMod 94752987463) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 14 * (3 : ZMod 94752987463) ^ 14) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 29214441671 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 94752987463) ^ 58 = 13774461667 := by
        calc
          (3 : ZMod 94752987463) ^ 58 = (3 : ZMod 94752987463) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 29 * (3 : ZMod 94752987463) ^ 29 := by rw [pow_add]
          _ = 13774461667 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 94752987463) ^ 117 = 73571107357 := by
        calc
          (3 : ZMod 94752987463) ^ 117 = (3 : ZMod 94752987463) ^ (58 + 58 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 58 * (3 : ZMod 94752987463) ^ 58) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 73571107357 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 94752987463) ^ 235 = 41667392666 := by
        calc
          (3 : ZMod 94752987463) ^ 235 = (3 : ZMod 94752987463) ^ (117 + 117 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 117 * (3 : ZMod 94752987463) ^ 117) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 41667392666 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 94752987463) ^ 470 = 63115666400 := by
        calc
          (3 : ZMod 94752987463) ^ 470 = (3 : ZMod 94752987463) ^ (235 + 235) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 235 * (3 : ZMod 94752987463) ^ 235 := by rw [pow_add]
          _ = 63115666400 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 94752987463) ^ 941 = 2205732004 := by
        calc
          (3 : ZMod 94752987463) ^ 941 = (3 : ZMod 94752987463) ^ (470 + 470 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 470 * (3 : ZMod 94752987463) ^ 470) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 2205732004 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 94752987463) ^ 1882 = 73091484064 := by
        calc
          (3 : ZMod 94752987463) ^ 1882 = (3 : ZMod 94752987463) ^ (941 + 941) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 941 * (3 : ZMod 94752987463) ^ 941 := by rw [pow_add]
          _ = 73091484064 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 94752987463) ^ 3765 = 68334832488 := by
        calc
          (3 : ZMod 94752987463) ^ 3765 = (3 : ZMod 94752987463) ^ (1882 + 1882 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1882 * (3 : ZMod 94752987463) ^ 1882) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 68334832488 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 94752987463) ^ 7530 = 24516051252 := by
        calc
          (3 : ZMod 94752987463) ^ 7530 = (3 : ZMod 94752987463) ^ (3765 + 3765) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 3765 * (3 : ZMod 94752987463) ^ 3765 := by rw [pow_add]
          _ = 24516051252 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 94752987463) ^ 15060 = 11904743690 := by
        calc
          (3 : ZMod 94752987463) ^ 15060 = (3 : ZMod 94752987463) ^ (7530 + 7530) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 7530 * (3 : ZMod 94752987463) ^ 7530 := by rw [pow_add]
          _ = 11904743690 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 94752987463) ^ 30121 = 47669040473 := by
        calc
          (3 : ZMod 94752987463) ^ 30121 = (3 : ZMod 94752987463) ^ (15060 + 15060 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 15060 * (3 : ZMod 94752987463) ^ 15060) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 47669040473 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 94752987463) ^ 60242 = 68290284124 := by
        calc
          (3 : ZMod 94752987463) ^ 60242 = (3 : ZMod 94752987463) ^ (30121 + 30121) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 30121 * (3 : ZMod 94752987463) ^ 30121 := by rw [pow_add]
          _ = 68290284124 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 94752987463) ^ 120484 = 58047358749 := by
        calc
          (3 : ZMod 94752987463) ^ 120484 = (3 : ZMod 94752987463) ^ (60242 + 60242) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 60242 * (3 : ZMod 94752987463) ^ 60242 := by rw [pow_add]
          _ = 58047358749 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 94752987463) ^ 240969 = 76640086337 := by
        calc
          (3 : ZMod 94752987463) ^ 240969 = (3 : ZMod 94752987463) ^ (120484 + 120484 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 120484 * (3 : ZMod 94752987463) ^ 120484) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 76640086337 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 94752987463) ^ 481938 = 61766777954 := by
        calc
          (3 : ZMod 94752987463) ^ 481938 = (3 : ZMod 94752987463) ^ (240969 + 240969) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 240969 * (3 : ZMod 94752987463) ^ 240969 := by rw [pow_add]
          _ = 61766777954 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 94752987463) ^ 963877 = 80711160437 := by
        calc
          (3 : ZMod 94752987463) ^ 963877 = (3 : ZMod 94752987463) ^ (481938 + 481938 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 481938 * (3 : ZMod 94752987463) ^ 481938) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 80711160437 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 94752987463) ^ 1927754 = 48997469549 := by
        calc
          (3 : ZMod 94752987463) ^ 1927754 = (3 : ZMod 94752987463) ^ (963877 + 963877) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 963877 * (3 : ZMod 94752987463) ^ 963877 := by rw [pow_add]
          _ = 48997469549 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 94752987463) ^ 3855508 = 29546286981 := by
        calc
          (3 : ZMod 94752987463) ^ 3855508 = (3 : ZMod 94752987463) ^ (1927754 + 1927754) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1927754 * (3 : ZMod 94752987463) ^ 1927754 := by rw [pow_add]
          _ = 29546286981 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 94752987463) ^ 7711017 = 65975727488 := by
        calc
          (3 : ZMod 94752987463) ^ 7711017 = (3 : ZMod 94752987463) ^ (3855508 + 3855508 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 3855508 * (3 : ZMod 94752987463) ^ 3855508) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 65975727488 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 94752987463) ^ 15422035 = 83831396611 := by
        calc
          (3 : ZMod 94752987463) ^ 15422035 = (3 : ZMod 94752987463) ^ (7711017 + 7711017 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 7711017 * (3 : ZMod 94752987463) ^ 7711017) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 83831396611 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 94752987463) ^ 30844071 = 28030862390 := by
        calc
          (3 : ZMod 94752987463) ^ 30844071 = (3 : ZMod 94752987463) ^ (15422035 + 15422035 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 15422035 * (3 : ZMod 94752987463) ^ 15422035) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 28030862390 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 94752987463) ^ 61688142 = 45896820378 := by
        calc
          (3 : ZMod 94752987463) ^ 61688142 = (3 : ZMod 94752987463) ^ (30844071 + 30844071) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 30844071 * (3 : ZMod 94752987463) ^ 30844071 := by rw [pow_add]
          _ = 45896820378 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 94752987463) ^ 123376285 = 33339384827 := by
        calc
          (3 : ZMod 94752987463) ^ 123376285 = (3 : ZMod 94752987463) ^ (61688142 + 61688142 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 61688142 * (3 : ZMod 94752987463) ^ 61688142) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 33339384827 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 94752987463) ^ 246752571 = 45472534891 := by
        calc
          (3 : ZMod 94752987463) ^ 246752571 = (3 : ZMod 94752987463) ^ (123376285 + 123376285 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 123376285 * (3 : ZMod 94752987463) ^ 123376285) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 45472534891 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 94752987463) ^ 493505143 = 2988491326 := by
        calc
          (3 : ZMod 94752987463) ^ 493505143 = (3 : ZMod 94752987463) ^ (246752571 + 246752571 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 246752571 * (3 : ZMod 94752987463) ^ 246752571) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 2988491326 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 94752987463) ^ 987010286 = 85667364463 := by
        calc
          (3 : ZMod 94752987463) ^ 987010286 = (3 : ZMod 94752987463) ^ (493505143 + 493505143) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 493505143 * (3 : ZMod 94752987463) ^ 493505143 := by rw [pow_add]
          _ = 85667364463 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 94752987463) ^ 1974020572 = 64230336971 := by
        calc
          (3 : ZMod 94752987463) ^ 1974020572 = (3 : ZMod 94752987463) ^ (987010286 + 987010286) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 987010286 * (3 : ZMod 94752987463) ^ 987010286 := by rw [pow_add]
          _ = 64230336971 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 94752987463) ^ 3948041144 = 57130622148 := by
        calc
          (3 : ZMod 94752987463) ^ 3948041144 = (3 : ZMod 94752987463) ^ (1974020572 + 1974020572) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1974020572 * (3 : ZMod 94752987463) ^ 1974020572 := by rw [pow_add]
          _ = 57130622148 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 94752987463) ^ 7896082288 = 14154360715 := by
        calc
          (3 : ZMod 94752987463) ^ 7896082288 = (3 : ZMod 94752987463) ^ (3948041144 + 3948041144) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 3948041144 * (3 : ZMod 94752987463) ^ 3948041144 := by rw [pow_add]
          _ = 14154360715 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 94752987463) ^ 15792164577 = 52289905317 := by
        calc
          (3 : ZMod 94752987463) ^ 15792164577 = (3 : ZMod 94752987463) ^ (7896082288 + 7896082288 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 7896082288 * (3 : ZMod 94752987463) ^ 7896082288) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 52289905317 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 94752987463) ^ 31584329154 = 52289905316 := by
        calc
          (3 : ZMod 94752987463) ^ 31584329154 = (3 : ZMod 94752987463) ^ (15792164577 + 15792164577) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 15792164577 * (3 : ZMod 94752987463) ^ 15792164577 := by rw [pow_add]
          _ = 52289905316 := by rw [factor_1_33]; decide
      change (3 : ZMod 94752987463) ^ 31584329154 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (3 : ZMod 94752987463) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 94752987463) ^ 3 = 27 := by
        calc
          (3 : ZMod 94752987463) ^ 3 = (3 : ZMod 94752987463) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1 * (3 : ZMod 94752987463) ^ 1) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 94752987463) ^ 6 = 729 := by
        calc
          (3 : ZMod 94752987463) ^ 6 = (3 : ZMod 94752987463) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 3 * (3 : ZMod 94752987463) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 94752987463) ^ 12 = 531441 := by
        calc
          (3 : ZMod 94752987463) ^ 12 = (3 : ZMod 94752987463) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 6 * (3 : ZMod 94752987463) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 94752987463) ^ 25 = 89264709739 := by
        calc
          (3 : ZMod 94752987463) ^ 25 = (3 : ZMod 94752987463) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 12 * (3 : ZMod 94752987463) ^ 12) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 89264709739 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 94752987463) ^ 50 = 36684402167 := by
        calc
          (3 : ZMod 94752987463) ^ 50 = (3 : ZMod 94752987463) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 25 * (3 : ZMod 94752987463) ^ 25 := by rw [pow_add]
          _ = 36684402167 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 94752987463) ^ 100 = 23398453816 := by
        calc
          (3 : ZMod 94752987463) ^ 100 = (3 : ZMod 94752987463) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 50 * (3 : ZMod 94752987463) ^ 50 := by rw [pow_add]
          _ = 23398453816 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 94752987463) ^ 201 = 55285701624 := by
        calc
          (3 : ZMod 94752987463) ^ 201 = (3 : ZMod 94752987463) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 100 * (3 : ZMod 94752987463) ^ 100) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 55285701624 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 94752987463) ^ 403 = 47822764439 := by
        calc
          (3 : ZMod 94752987463) ^ 403 = (3 : ZMod 94752987463) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 201 * (3 : ZMod 94752987463) ^ 201) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 47822764439 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 94752987463) ^ 806 = 53831816242 := by
        calc
          (3 : ZMod 94752987463) ^ 806 = (3 : ZMod 94752987463) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 403 * (3 : ZMod 94752987463) ^ 403 := by rw [pow_add]
          _ = 53831816242 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 94752987463) ^ 1613 = 30491144269 := by
        calc
          (3 : ZMod 94752987463) ^ 1613 = (3 : ZMod 94752987463) ^ (806 + 806 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 806 * (3 : ZMod 94752987463) ^ 806) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 30491144269 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 94752987463) ^ 3227 = 48134670665 := by
        calc
          (3 : ZMod 94752987463) ^ 3227 = (3 : ZMod 94752987463) ^ (1613 + 1613 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1613 * (3 : ZMod 94752987463) ^ 1613) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 48134670665 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 94752987463) ^ 6454 = 22317175968 := by
        calc
          (3 : ZMod 94752987463) ^ 6454 = (3 : ZMod 94752987463) ^ (3227 + 3227) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 3227 * (3 : ZMod 94752987463) ^ 3227 := by rw [pow_add]
          _ = 22317175968 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 94752987463) ^ 12909 = 61856541932 := by
        calc
          (3 : ZMod 94752987463) ^ 12909 = (3 : ZMod 94752987463) ^ (6454 + 6454 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 6454 * (3 : ZMod 94752987463) ^ 6454) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 61856541932 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 94752987463) ^ 25818 = 37411728967 := by
        calc
          (3 : ZMod 94752987463) ^ 25818 = (3 : ZMod 94752987463) ^ (12909 + 12909) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 12909 * (3 : ZMod 94752987463) ^ 12909 := by rw [pow_add]
          _ = 37411728967 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 94752987463) ^ 51636 = 72882130881 := by
        calc
          (3 : ZMod 94752987463) ^ 51636 = (3 : ZMod 94752987463) ^ (25818 + 25818) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 25818 * (3 : ZMod 94752987463) ^ 25818 := by rw [pow_add]
          _ = 72882130881 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 94752987463) ^ 103272 = 90037234996 := by
        calc
          (3 : ZMod 94752987463) ^ 103272 = (3 : ZMod 94752987463) ^ (51636 + 51636) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 51636 * (3 : ZMod 94752987463) ^ 51636 := by rw [pow_add]
          _ = 90037234996 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 94752987463) ^ 206545 = 85228143285 := by
        calc
          (3 : ZMod 94752987463) ^ 206545 = (3 : ZMod 94752987463) ^ (103272 + 103272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 103272 * (3 : ZMod 94752987463) ^ 103272) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 85228143285 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 94752987463) ^ 413090 = 76066533263 := by
        calc
          (3 : ZMod 94752987463) ^ 413090 = (3 : ZMod 94752987463) ^ (206545 + 206545) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 206545 * (3 : ZMod 94752987463) ^ 206545 := by rw [pow_add]
          _ = 76066533263 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 94752987463) ^ 826180 = 77929660758 := by
        calc
          (3 : ZMod 94752987463) ^ 826180 = (3 : ZMod 94752987463) ^ (413090 + 413090) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 413090 * (3 : ZMod 94752987463) ^ 413090 := by rw [pow_add]
          _ = 77929660758 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 94752987463) ^ 1652360 = 30860780788 := by
        calc
          (3 : ZMod 94752987463) ^ 1652360 = (3 : ZMod 94752987463) ^ (826180 + 826180) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 826180 * (3 : ZMod 94752987463) ^ 826180 := by rw [pow_add]
          _ = 30860780788 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 94752987463) ^ 3304721 = 5105103969 := by
        calc
          (3 : ZMod 94752987463) ^ 3304721 = (3 : ZMod 94752987463) ^ (1652360 + 1652360 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1652360 * (3 : ZMod 94752987463) ^ 1652360) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 5105103969 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 94752987463) ^ 6609443 = 66574283743 := by
        calc
          (3 : ZMod 94752987463) ^ 6609443 = (3 : ZMod 94752987463) ^ (3304721 + 3304721 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 3304721 * (3 : ZMod 94752987463) ^ 3304721) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 66574283743 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 94752987463) ^ 13218887 = 72105357155 := by
        calc
          (3 : ZMod 94752987463) ^ 13218887 = (3 : ZMod 94752987463) ^ (6609443 + 6609443 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 6609443 * (3 : ZMod 94752987463) ^ 6609443) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 72105357155 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 94752987463) ^ 26437775 = 90931692638 := by
        calc
          (3 : ZMod 94752987463) ^ 26437775 = (3 : ZMod 94752987463) ^ (13218887 + 13218887 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 13218887 * (3 : ZMod 94752987463) ^ 13218887) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 90931692638 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 94752987463) ^ 52875551 = 75594310368 := by
        calc
          (3 : ZMod 94752987463) ^ 52875551 = (3 : ZMod 94752987463) ^ (26437775 + 26437775 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 26437775 * (3 : ZMod 94752987463) ^ 26437775) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 75594310368 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 94752987463) ^ 105751102 = 73054120607 := by
        calc
          (3 : ZMod 94752987463) ^ 105751102 = (3 : ZMod 94752987463) ^ (52875551 + 52875551) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 52875551 * (3 : ZMod 94752987463) ^ 52875551 := by rw [pow_add]
          _ = 73054120607 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 94752987463) ^ 211502204 = 45200565158 := by
        calc
          (3 : ZMod 94752987463) ^ 211502204 = (3 : ZMod 94752987463) ^ (105751102 + 105751102) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 105751102 * (3 : ZMod 94752987463) ^ 105751102 := by rw [pow_add]
          _ = 45200565158 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 94752987463) ^ 423004408 = 52852138953 := by
        calc
          (3 : ZMod 94752987463) ^ 423004408 = (3 : ZMod 94752987463) ^ (211502204 + 211502204) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 211502204 * (3 : ZMod 94752987463) ^ 211502204 := by rw [pow_add]
          _ = 52852138953 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 94752987463) ^ 846008816 = 44670304501 := by
        calc
          (3 : ZMod 94752987463) ^ 846008816 = (3 : ZMod 94752987463) ^ (423004408 + 423004408) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 423004408 * (3 : ZMod 94752987463) ^ 423004408 := by rw [pow_add]
          _ = 44670304501 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 94752987463) ^ 1692017633 = 15674179060 := by
        calc
          (3 : ZMod 94752987463) ^ 1692017633 = (3 : ZMod 94752987463) ^ (846008816 + 846008816 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 846008816 * (3 : ZMod 94752987463) ^ 846008816) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 15674179060 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 94752987463) ^ 3384035266 = 23436754606 := by
        calc
          (3 : ZMod 94752987463) ^ 3384035266 = (3 : ZMod 94752987463) ^ (1692017633 + 1692017633) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1692017633 * (3 : ZMod 94752987463) ^ 1692017633 := by rw [pow_add]
          _ = 23436754606 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 94752987463) ^ 6768070533 = 3818806679 := by
        calc
          (3 : ZMod 94752987463) ^ 6768070533 = (3 : ZMod 94752987463) ^ (3384035266 + 3384035266 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 3384035266 * (3 : ZMod 94752987463) ^ 3384035266) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 3818806679 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 94752987463) ^ 13536141066 = 60558108784 := by
        calc
          (3 : ZMod 94752987463) ^ 13536141066 = (3 : ZMod 94752987463) ^ (6768070533 + 6768070533) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 6768070533 * (3 : ZMod 94752987463) ^ 6768070533 := by rw [pow_add]
          _ = 60558108784 := by rw [factor_2_32]; decide
      change (3 : ZMod 94752987463) ^ 13536141066 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (3 : ZMod 94752987463) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 94752987463) ^ 2 = 9 := by
        calc
          (3 : ZMod 94752987463) ^ 2 = (3 : ZMod 94752987463) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1 * (3 : ZMod 94752987463) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 94752987463) ^ 4 = 81 := by
        calc
          (3 : ZMod 94752987463) ^ 4 = (3 : ZMod 94752987463) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 2 * (3 : ZMod 94752987463) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 94752987463) ^ 8 = 6561 := by
        calc
          (3 : ZMod 94752987463) ^ 8 = (3 : ZMod 94752987463) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 4 * (3 : ZMod 94752987463) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 94752987463) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 94752987463) ^ 17 = (3 : ZMod 94752987463) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 8 * (3 : ZMod 94752987463) ^ 8) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 94752987463) ^ 34 = 87388253791 := by
        calc
          (3 : ZMod 94752987463) ^ 34 = (3 : ZMod 94752987463) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 17 * (3 : ZMod 94752987463) ^ 17 := by rw [pow_add]
          _ = 87388253791 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 94752987463) ^ 68 = 8542592291 := by
        calc
          (3 : ZMod 94752987463) ^ 68 = (3 : ZMod 94752987463) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 34 * (3 : ZMod 94752987463) ^ 34 := by rw [pow_add]
          _ = 8542592291 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 94752987463) ^ 136 = 89674558765 := by
        calc
          (3 : ZMod 94752987463) ^ 136 = (3 : ZMod 94752987463) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 68 * (3 : ZMod 94752987463) ^ 68 := by rw [pow_add]
          _ = 89674558765 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 94752987463) ^ 273 = 16066123240 := by
        calc
          (3 : ZMod 94752987463) ^ 273 = (3 : ZMod 94752987463) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 136 * (3 : ZMod 94752987463) ^ 136) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 16066123240 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 94752987463) ^ 546 = 57665718486 := by
        calc
          (3 : ZMod 94752987463) ^ 546 = (3 : ZMod 94752987463) ^ (273 + 273) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 273 * (3 : ZMod 94752987463) ^ 273 := by rw [pow_add]
          _ = 57665718486 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 94752987463) ^ 1092 = 40431704370 := by
        calc
          (3 : ZMod 94752987463) ^ 1092 = (3 : ZMod 94752987463) ^ (546 + 546) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 546 * (3 : ZMod 94752987463) ^ 546 := by rw [pow_add]
          _ = 40431704370 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 94752987463) ^ 2184 = 65749460613 := by
        calc
          (3 : ZMod 94752987463) ^ 2184 = (3 : ZMod 94752987463) ^ (1092 + 1092) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1092 * (3 : ZMod 94752987463) ^ 1092 := by rw [pow_add]
          _ = 65749460613 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 94752987463) ^ 4368 = 48287234738 := by
        calc
          (3 : ZMod 94752987463) ^ 4368 = (3 : ZMod 94752987463) ^ (2184 + 2184) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 2184 * (3 : ZMod 94752987463) ^ 2184 := by rw [pow_add]
          _ = 48287234738 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 94752987463) ^ 8736 = 29190333193 := by
        calc
          (3 : ZMod 94752987463) ^ 8736 = (3 : ZMod 94752987463) ^ (4368 + 4368) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 4368 * (3 : ZMod 94752987463) ^ 4368 := by rw [pow_add]
          _ = 29190333193 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 94752987463) ^ 17472 = 23228186535 := by
        calc
          (3 : ZMod 94752987463) ^ 17472 = (3 : ZMod 94752987463) ^ (8736 + 8736) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 8736 * (3 : ZMod 94752987463) ^ 8736 := by rw [pow_add]
          _ = 23228186535 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 94752987463) ^ 34944 = 80576510232 := by
        calc
          (3 : ZMod 94752987463) ^ 34944 = (3 : ZMod 94752987463) ^ (17472 + 17472) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 17472 * (3 : ZMod 94752987463) ^ 17472 := by rw [pow_add]
          _ = 80576510232 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 94752987463) ^ 69888 = 19509344454 := by
        calc
          (3 : ZMod 94752987463) ^ 69888 = (3 : ZMod 94752987463) ^ (34944 + 34944) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 34944 * (3 : ZMod 94752987463) ^ 34944 := by rw [pow_add]
          _ = 19509344454 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 94752987463) ^ 139776 = 61922669518 := by
        calc
          (3 : ZMod 94752987463) ^ 139776 = (3 : ZMod 94752987463) ^ (69888 + 69888) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 69888 * (3 : ZMod 94752987463) ^ 69888 := by rw [pow_add]
          _ = 61922669518 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 94752987463) ^ 279553 = 78825106835 := by
        calc
          (3 : ZMod 94752987463) ^ 279553 = (3 : ZMod 94752987463) ^ (139776 + 139776 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 139776 * (3 : ZMod 94752987463) ^ 139776) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 78825106835 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 94752987463) ^ 559107 = 47660926263 := by
        calc
          (3 : ZMod 94752987463) ^ 559107 = (3 : ZMod 94752987463) ^ (279553 + 279553 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 279553 * (3 : ZMod 94752987463) ^ 279553) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 47660926263 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 94752987463) ^ 1118214 = 82414061624 := by
        calc
          (3 : ZMod 94752987463) ^ 1118214 = (3 : ZMod 94752987463) ^ (559107 + 559107) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 559107 * (3 : ZMod 94752987463) ^ 559107 := by rw [pow_add]
          _ = 82414061624 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 94752987463) ^ 2236428 = 80092200221 := by
        calc
          (3 : ZMod 94752987463) ^ 2236428 = (3 : ZMod 94752987463) ^ (1118214 + 1118214) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 1118214 * (3 : ZMod 94752987463) ^ 1118214 := by rw [pow_add]
          _ = 80092200221 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 94752987463) ^ 4472856 = 85911834282 := by
        calc
          (3 : ZMod 94752987463) ^ 4472856 = (3 : ZMod 94752987463) ^ (2236428 + 2236428) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 2236428 * (3 : ZMod 94752987463) ^ 2236428 := by rw [pow_add]
          _ = 85911834282 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 94752987463) ^ 8945712 = 66425065896 := by
        calc
          (3 : ZMod 94752987463) ^ 8945712 = (3 : ZMod 94752987463) ^ (4472856 + 4472856) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 4472856 * (3 : ZMod 94752987463) ^ 4472856 := by rw [pow_add]
          _ = 66425065896 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 94752987463) ^ 17891425 = 26462220518 := by
        calc
          (3 : ZMod 94752987463) ^ 17891425 = (3 : ZMod 94752987463) ^ (8945712 + 8945712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 8945712 * (3 : ZMod 94752987463) ^ 8945712) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 26462220518 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 94752987463) ^ 35782850 = 63303782381 := by
        calc
          (3 : ZMod 94752987463) ^ 35782850 = (3 : ZMod 94752987463) ^ (17891425 + 17891425) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 17891425 * (3 : ZMod 94752987463) ^ 17891425 := by rw [pow_add]
          _ = 63303782381 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 94752987463) ^ 71565700 = 14307993087 := by
        calc
          (3 : ZMod 94752987463) ^ 71565700 = (3 : ZMod 94752987463) ^ (35782850 + 35782850) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 35782850 * (3 : ZMod 94752987463) ^ 35782850 := by rw [pow_add]
          _ = 14307993087 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 94752987463) ^ 143131401 = 8490759813 := by
        calc
          (3 : ZMod 94752987463) ^ 143131401 = (3 : ZMod 94752987463) ^ (71565700 + 71565700 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 71565700 * (3 : ZMod 94752987463) ^ 71565700) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 8490759813 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 94752987463) ^ 286262802 = 5538607320 := by
        calc
          (3 : ZMod 94752987463) ^ 286262802 = (3 : ZMod 94752987463) ^ (143131401 + 143131401) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 143131401 * (3 : ZMod 94752987463) ^ 143131401 := by rw [pow_add]
          _ = 5538607320 := by rw [factor_3_27]; decide
      change (3 : ZMod 94752987463) ^ 286262802 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (3 : ZMod 94752987463) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 94752987463) ^ 3 = 27 := by
        calc
          (3 : ZMod 94752987463) ^ 3 = (3 : ZMod 94752987463) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1 * (3 : ZMod 94752987463) ^ 1) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 94752987463) ^ 6 = 729 := by
        calc
          (3 : ZMod 94752987463) ^ 6 = (3 : ZMod 94752987463) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 3 * (3 : ZMod 94752987463) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 94752987463) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 94752987463) ^ 13 = (3 : ZMod 94752987463) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 6 * (3 : ZMod 94752987463) ^ 6) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 94752987463) ^ 26 = 78288154291 := by
        calc
          (3 : ZMod 94752987463) ^ 26 = (3 : ZMod 94752987463) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 13 * (3 : ZMod 94752987463) ^ 13 := by rw [pow_add]
          _ = 78288154291 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 94752987463) ^ 53 = 42948983879 := by
        calc
          (3 : ZMod 94752987463) ^ 53 = (3 : ZMod 94752987463) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 26 * (3 : ZMod 94752987463) ^ 26) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 42948983879 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 94752987463) ^ 106 = 1935088524 := by
        calc
          (3 : ZMod 94752987463) ^ 106 = (3 : ZMod 94752987463) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 53 * (3 : ZMod 94752987463) ^ 53 := by rw [pow_add]
          _ = 1935088524 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 94752987463) ^ 213 = 82204233144 := by
        calc
          (3 : ZMod 94752987463) ^ 213 = (3 : ZMod 94752987463) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 106 * (3 : ZMod 94752987463) ^ 106) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 82204233144 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 94752987463) ^ 427 = 24065582360 := by
        calc
          (3 : ZMod 94752987463) ^ 427 = (3 : ZMod 94752987463) ^ (213 + 213 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 213 * (3 : ZMod 94752987463) ^ 213) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 24065582360 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 94752987463) ^ 855 = 12828125156 := by
        calc
          (3 : ZMod 94752987463) ^ 855 = (3 : ZMod 94752987463) ^ (427 + 427 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 427 * (3 : ZMod 94752987463) ^ 427) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 12828125156 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 94752987463) ^ 1710 = 16040130794 := by
        calc
          (3 : ZMod 94752987463) ^ 1710 = (3 : ZMod 94752987463) ^ (855 + 855) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 855 * (3 : ZMod 94752987463) ^ 855 := by rw [pow_add]
          _ = 16040130794 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 94752987463) ^ 3421 = 68666898761 := by
        calc
          (3 : ZMod 94752987463) ^ 3421 = (3 : ZMod 94752987463) ^ (1710 + 1710 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 1710 * (3 : ZMod 94752987463) ^ 1710) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 68666898761 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 94752987463) ^ 6842 = 39886013119 := by
        calc
          (3 : ZMod 94752987463) ^ 6842 = (3 : ZMod 94752987463) ^ (3421 + 3421) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 3421 * (3 : ZMod 94752987463) ^ 3421 := by rw [pow_add]
          _ = 39886013119 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 94752987463) ^ 13684 = 51455968307 := by
        calc
          (3 : ZMod 94752987463) ^ 13684 = (3 : ZMod 94752987463) ^ (6842 + 6842) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 6842 * (3 : ZMod 94752987463) ^ 6842 := by rw [pow_add]
          _ = 51455968307 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 94752987463) ^ 27369 = 2567667552 := by
        calc
          (3 : ZMod 94752987463) ^ 27369 = (3 : ZMod 94752987463) ^ (13684 + 13684 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 13684 * (3 : ZMod 94752987463) ^ 13684) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 2567667552 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 94752987463) ^ 54739 = 94148890015 := by
        calc
          (3 : ZMod 94752987463) ^ 54739 = (3 : ZMod 94752987463) ^ (27369 + 27369 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 27369 * (3 : ZMod 94752987463) ^ 27369) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 94148890015 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 94752987463) ^ 109478 = 80952377781 := by
        calc
          (3 : ZMod 94752987463) ^ 109478 = (3 : ZMod 94752987463) ^ (54739 + 54739) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 54739 * (3 : ZMod 94752987463) ^ 54739 := by rw [pow_add]
          _ = 80952377781 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 94752987463) ^ 218956 = 91270776103 := by
        calc
          (3 : ZMod 94752987463) ^ 218956 = (3 : ZMod 94752987463) ^ (109478 + 109478) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 109478 * (3 : ZMod 94752987463) ^ 109478 := by rw [pow_add]
          _ = 91270776103 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 94752987463) ^ 437913 = 3490493870 := by
        calc
          (3 : ZMod 94752987463) ^ 437913 = (3 : ZMod 94752987463) ^ (218956 + 218956 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = ((3 : ZMod 94752987463) ^ 218956 * (3 : ZMod 94752987463) ^ 218956) * (3 : ZMod 94752987463) := by rw [pow_succ, pow_add]
          _ = 3490493870 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 94752987463) ^ 875826 = 61448593226 := by
        calc
          (3 : ZMod 94752987463) ^ 875826 = (3 : ZMod 94752987463) ^ (437913 + 437913) :=
            congrArg (fun n : ℕ => (3 : ZMod 94752987463) ^ n) (by norm_num)
          _ = (3 : ZMod 94752987463) ^ 437913 * (3 : ZMod 94752987463) ^ 437913 := by rw [pow_add]
          _ = 61448593226 := by rw [factor_4_18]; decide
      change (3 : ZMod 94752987463) ^ 875826 ≠ 1
      rw [factor_4_19]
      decide

#print axioms prime_lucas_94752987463

end TotientTailPeriodKiller
end Erdos249257
