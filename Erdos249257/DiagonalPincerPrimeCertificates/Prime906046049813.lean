import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_906046049813 : Nat.Prime 906046049813 := by
  apply lucas_primality 906046049813 (2 : ZMod 906046049813)
  ·
      have fermat_0 : (2 : ZMod 906046049813) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 906046049813) ^ 3 = 8 := by
        calc
          (2 : ZMod 906046049813) ^ 3 = (2 : ZMod 906046049813) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 1 * (2 : ZMod 906046049813) ^ 1) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 906046049813) ^ 6 = 64 := by
        calc
          (2 : ZMod 906046049813) ^ 6 = (2 : ZMod 906046049813) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3 * (2 : ZMod 906046049813) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 906046049813) ^ 13 = 8192 := by
        calc
          (2 : ZMod 906046049813) ^ 13 = (2 : ZMod 906046049813) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 6 * (2 : ZMod 906046049813) ^ 6) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 906046049813) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 906046049813) ^ 26 = (2 : ZMod 906046049813) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 13 * (2 : ZMod 906046049813) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 906046049813) ^ 52 = 550759799886 := by
        calc
          (2 : ZMod 906046049813) ^ 52 = (2 : ZMod 906046049813) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 26 * (2 : ZMod 906046049813) ^ 26 := by rw [pow_add]
          _ = 550759799886 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 906046049813) ^ 105 = 889366128262 := by
        calc
          (2 : ZMod 906046049813) ^ 105 = (2 : ZMod 906046049813) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 52 * (2 : ZMod 906046049813) ^ 52) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 889366128262 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 906046049813) ^ 210 = 450154131416 := by
        calc
          (2 : ZMod 906046049813) ^ 210 = (2 : ZMod 906046049813) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 105 * (2 : ZMod 906046049813) ^ 105 := by rw [pow_add]
          _ = 450154131416 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 906046049813) ^ 421 = 270877949494 := by
        calc
          (2 : ZMod 906046049813) ^ 421 = (2 : ZMod 906046049813) ^ (210 + 210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 210 * (2 : ZMod 906046049813) ^ 210) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 270877949494 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 906046049813) ^ 843 = 875837174818 := by
        calc
          (2 : ZMod 906046049813) ^ 843 = (2 : ZMod 906046049813) ^ (421 + 421 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 421 * (2 : ZMod 906046049813) ^ 421) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 875837174818 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 906046049813) ^ 1687 = 6253402574 := by
        calc
          (2 : ZMod 906046049813) ^ 1687 = (2 : ZMod 906046049813) ^ (843 + 843 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 843 * (2 : ZMod 906046049813) ^ 843) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 6253402574 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 906046049813) ^ 3375 = 403398930596 := by
        calc
          (2 : ZMod 906046049813) ^ 3375 = (2 : ZMod 906046049813) ^ (1687 + 1687 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 1687 * (2 : ZMod 906046049813) ^ 1687) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 403398930596 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 906046049813) ^ 6750 = 58534695632 := by
        calc
          (2 : ZMod 906046049813) ^ 6750 = (2 : ZMod 906046049813) ^ (3375 + 3375) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3375 * (2 : ZMod 906046049813) ^ 3375 := by rw [pow_add]
          _ = 58534695632 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 906046049813) ^ 13501 = 287712886662 := by
        calc
          (2 : ZMod 906046049813) ^ 13501 = (2 : ZMod 906046049813) ^ (6750 + 6750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 6750 * (2 : ZMod 906046049813) ^ 6750) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 287712886662 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 906046049813) ^ 27002 = 412233703313 := by
        calc
          (2 : ZMod 906046049813) ^ 27002 = (2 : ZMod 906046049813) ^ (13501 + 13501) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 13501 * (2 : ZMod 906046049813) ^ 13501 := by rw [pow_add]
          _ = 412233703313 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 906046049813) ^ 54004 = 623120222529 := by
        calc
          (2 : ZMod 906046049813) ^ 54004 = (2 : ZMod 906046049813) ^ (27002 + 27002) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 27002 * (2 : ZMod 906046049813) ^ 27002 := by rw [pow_add]
          _ = 623120222529 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 906046049813) ^ 108009 = 461140415098 := by
        calc
          (2 : ZMod 906046049813) ^ 108009 = (2 : ZMod 906046049813) ^ (54004 + 54004 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 54004 * (2 : ZMod 906046049813) ^ 54004) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 461140415098 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 906046049813) ^ 216018 = 94832132941 := by
        calc
          (2 : ZMod 906046049813) ^ 216018 = (2 : ZMod 906046049813) ^ (108009 + 108009) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 108009 * (2 : ZMod 906046049813) ^ 108009 := by rw [pow_add]
          _ = 94832132941 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 906046049813) ^ 432036 = 621026191557 := by
        calc
          (2 : ZMod 906046049813) ^ 432036 = (2 : ZMod 906046049813) ^ (216018 + 216018) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 216018 * (2 : ZMod 906046049813) ^ 216018 := by rw [pow_add]
          _ = 621026191557 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 906046049813) ^ 864072 = 483679791184 := by
        calc
          (2 : ZMod 906046049813) ^ 864072 = (2 : ZMod 906046049813) ^ (432036 + 432036) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 432036 * (2 : ZMod 906046049813) ^ 432036 := by rw [pow_add]
          _ = 483679791184 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 906046049813) ^ 1728145 = 503396835046 := by
        calc
          (2 : ZMod 906046049813) ^ 1728145 = (2 : ZMod 906046049813) ^ (864072 + 864072 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 864072 * (2 : ZMod 906046049813) ^ 864072) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 503396835046 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 906046049813) ^ 3456291 = 559651632025 := by
        calc
          (2 : ZMod 906046049813) ^ 3456291 = (2 : ZMod 906046049813) ^ (1728145 + 1728145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 1728145 * (2 : ZMod 906046049813) ^ 1728145) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 559651632025 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 906046049813) ^ 6912582 = 840214961529 := by
        calc
          (2 : ZMod 906046049813) ^ 6912582 = (2 : ZMod 906046049813) ^ (3456291 + 3456291) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3456291 * (2 : ZMod 906046049813) ^ 3456291 := by rw [pow_add]
          _ = 840214961529 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 906046049813) ^ 13825165 = 715654956820 := by
        calc
          (2 : ZMod 906046049813) ^ 13825165 = (2 : ZMod 906046049813) ^ (6912582 + 6912582 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 6912582 * (2 : ZMod 906046049813) ^ 6912582) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 715654956820 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 906046049813) ^ 27650331 = 149763201253 := by
        calc
          (2 : ZMod 906046049813) ^ 27650331 = (2 : ZMod 906046049813) ^ (13825165 + 13825165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 13825165 * (2 : ZMod 906046049813) ^ 13825165) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 149763201253 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 906046049813) ^ 55300662 = 526123736038 := by
        calc
          (2 : ZMod 906046049813) ^ 55300662 = (2 : ZMod 906046049813) ^ (27650331 + 27650331) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 27650331 * (2 : ZMod 906046049813) ^ 27650331 := by rw [pow_add]
          _ = 526123736038 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 906046049813) ^ 110601324 = 125285240207 := by
        calc
          (2 : ZMod 906046049813) ^ 110601324 = (2 : ZMod 906046049813) ^ (55300662 + 55300662) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 55300662 * (2 : ZMod 906046049813) ^ 55300662 := by rw [pow_add]
          _ = 125285240207 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 906046049813) ^ 221202648 = 878023949327 := by
        calc
          (2 : ZMod 906046049813) ^ 221202648 = (2 : ZMod 906046049813) ^ (110601324 + 110601324) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 110601324 * (2 : ZMod 906046049813) ^ 110601324 := by rw [pow_add]
          _ = 878023949327 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 906046049813) ^ 442405297 = 769514864956 := by
        calc
          (2 : ZMod 906046049813) ^ 442405297 = (2 : ZMod 906046049813) ^ (221202648 + 221202648 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 221202648 * (2 : ZMod 906046049813) ^ 221202648) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 769514864956 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 906046049813) ^ 884810595 = 828915423052 := by
        calc
          (2 : ZMod 906046049813) ^ 884810595 = (2 : ZMod 906046049813) ^ (442405297 + 442405297 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 442405297 * (2 : ZMod 906046049813) ^ 442405297) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 828915423052 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 906046049813) ^ 1769621191 = 582827890931 := by
        calc
          (2 : ZMod 906046049813) ^ 1769621191 = (2 : ZMod 906046049813) ^ (884810595 + 884810595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 884810595 * (2 : ZMod 906046049813) ^ 884810595) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 582827890931 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 906046049813) ^ 3539242382 = 869819561844 := by
        calc
          (2 : ZMod 906046049813) ^ 3539242382 = (2 : ZMod 906046049813) ^ (1769621191 + 1769621191) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1769621191 * (2 : ZMod 906046049813) ^ 1769621191 := by rw [pow_add]
          _ = 869819561844 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 906046049813) ^ 7078484764 = 10252175527 := by
        calc
          (2 : ZMod 906046049813) ^ 7078484764 = (2 : ZMod 906046049813) ^ (3539242382 + 3539242382) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3539242382 * (2 : ZMod 906046049813) ^ 3539242382 := by rw [pow_add]
          _ = 10252175527 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 906046049813) ^ 14156969528 = 617325016675 := by
        calc
          (2 : ZMod 906046049813) ^ 14156969528 = (2 : ZMod 906046049813) ^ (7078484764 + 7078484764) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 7078484764 * (2 : ZMod 906046049813) ^ 7078484764 := by rw [pow_add]
          _ = 617325016675 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 906046049813) ^ 28313939056 = 785696103902 := by
        calc
          (2 : ZMod 906046049813) ^ 28313939056 = (2 : ZMod 906046049813) ^ (14156969528 + 14156969528) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 14156969528 * (2 : ZMod 906046049813) ^ 14156969528 := by rw [pow_add]
          _ = 785696103902 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 906046049813) ^ 56627878113 = 436595603944 := by
        calc
          (2 : ZMod 906046049813) ^ 56627878113 = (2 : ZMod 906046049813) ^ (28313939056 + 28313939056 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 28313939056 * (2 : ZMod 906046049813) ^ 28313939056) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 436595603944 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 906046049813) ^ 113255756226 = 667405896325 := by
        calc
          (2 : ZMod 906046049813) ^ 113255756226 = (2 : ZMod 906046049813) ^ (56627878113 + 56627878113) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 56627878113 * (2 : ZMod 906046049813) ^ 56627878113 := by rw [pow_add]
          _ = 667405896325 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 906046049813) ^ 226511512453 = 477280306975 := by
        calc
          (2 : ZMod 906046049813) ^ 226511512453 = (2 : ZMod 906046049813) ^ (113255756226 + 113255756226 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 113255756226 * (2 : ZMod 906046049813) ^ 113255756226) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 477280306975 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 906046049813) ^ 453023024906 = 906046049812 := by
        calc
          (2 : ZMod 906046049813) ^ 453023024906 = (2 : ZMod 906046049813) ^ (226511512453 + 226511512453) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 226511512453 * (2 : ZMod 906046049813) ^ 226511512453 := by rw [pow_add]
          _ = 906046049812 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 906046049813) ^ 906046049812 = 1 := by
        calc
          (2 : ZMod 906046049813) ^ 906046049812 = (2 : ZMod 906046049813) ^ (453023024906 + 453023024906) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 453023024906 * (2 : ZMod 906046049813) ^ 453023024906 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (587, 1), (10429187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (587, 1), (10429187, 1)] : List FactorBlock).map factorBlockValue).prod = 906046049813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 906046049813) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 906046049813) ^ 3 = 8 := by
        calc
          (2 : ZMod 906046049813) ^ 3 = (2 : ZMod 906046049813) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 1 * (2 : ZMod 906046049813) ^ 1) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 906046049813) ^ 6 = 64 := by
        calc
          (2 : ZMod 906046049813) ^ 6 = (2 : ZMod 906046049813) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3 * (2 : ZMod 906046049813) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 906046049813) ^ 13 = 8192 := by
        calc
          (2 : ZMod 906046049813) ^ 13 = (2 : ZMod 906046049813) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 6 * (2 : ZMod 906046049813) ^ 6) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 906046049813) ^ 26 = 67108864 := by
        calc
          (2 : ZMod 906046049813) ^ 26 = (2 : ZMod 906046049813) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 13 * (2 : ZMod 906046049813) ^ 13 := by rw [pow_add]
          _ = 67108864 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 906046049813) ^ 52 = 550759799886 := by
        calc
          (2 : ZMod 906046049813) ^ 52 = (2 : ZMod 906046049813) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 26 * (2 : ZMod 906046049813) ^ 26 := by rw [pow_add]
          _ = 550759799886 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 906046049813) ^ 105 = 889366128262 := by
        calc
          (2 : ZMod 906046049813) ^ 105 = (2 : ZMod 906046049813) ^ (52 + 52 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 52 * (2 : ZMod 906046049813) ^ 52) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 889366128262 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 906046049813) ^ 210 = 450154131416 := by
        calc
          (2 : ZMod 906046049813) ^ 210 = (2 : ZMod 906046049813) ^ (105 + 105) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 105 * (2 : ZMod 906046049813) ^ 105 := by rw [pow_add]
          _ = 450154131416 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 906046049813) ^ 421 = 270877949494 := by
        calc
          (2 : ZMod 906046049813) ^ 421 = (2 : ZMod 906046049813) ^ (210 + 210 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 210 * (2 : ZMod 906046049813) ^ 210) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 270877949494 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 906046049813) ^ 843 = 875837174818 := by
        calc
          (2 : ZMod 906046049813) ^ 843 = (2 : ZMod 906046049813) ^ (421 + 421 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 421 * (2 : ZMod 906046049813) ^ 421) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 875837174818 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 906046049813) ^ 1687 = 6253402574 := by
        calc
          (2 : ZMod 906046049813) ^ 1687 = (2 : ZMod 906046049813) ^ (843 + 843 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 843 * (2 : ZMod 906046049813) ^ 843) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 6253402574 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 906046049813) ^ 3375 = 403398930596 := by
        calc
          (2 : ZMod 906046049813) ^ 3375 = (2 : ZMod 906046049813) ^ (1687 + 1687 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 1687 * (2 : ZMod 906046049813) ^ 1687) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 403398930596 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 906046049813) ^ 6750 = 58534695632 := by
        calc
          (2 : ZMod 906046049813) ^ 6750 = (2 : ZMod 906046049813) ^ (3375 + 3375) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3375 * (2 : ZMod 906046049813) ^ 3375 := by rw [pow_add]
          _ = 58534695632 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 906046049813) ^ 13501 = 287712886662 := by
        calc
          (2 : ZMod 906046049813) ^ 13501 = (2 : ZMod 906046049813) ^ (6750 + 6750 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 6750 * (2 : ZMod 906046049813) ^ 6750) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 287712886662 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 906046049813) ^ 27002 = 412233703313 := by
        calc
          (2 : ZMod 906046049813) ^ 27002 = (2 : ZMod 906046049813) ^ (13501 + 13501) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 13501 * (2 : ZMod 906046049813) ^ 13501 := by rw [pow_add]
          _ = 412233703313 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 906046049813) ^ 54004 = 623120222529 := by
        calc
          (2 : ZMod 906046049813) ^ 54004 = (2 : ZMod 906046049813) ^ (27002 + 27002) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 27002 * (2 : ZMod 906046049813) ^ 27002 := by rw [pow_add]
          _ = 623120222529 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 906046049813) ^ 108009 = 461140415098 := by
        calc
          (2 : ZMod 906046049813) ^ 108009 = (2 : ZMod 906046049813) ^ (54004 + 54004 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 54004 * (2 : ZMod 906046049813) ^ 54004) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 461140415098 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 906046049813) ^ 216018 = 94832132941 := by
        calc
          (2 : ZMod 906046049813) ^ 216018 = (2 : ZMod 906046049813) ^ (108009 + 108009) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 108009 * (2 : ZMod 906046049813) ^ 108009 := by rw [pow_add]
          _ = 94832132941 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 906046049813) ^ 432036 = 621026191557 := by
        calc
          (2 : ZMod 906046049813) ^ 432036 = (2 : ZMod 906046049813) ^ (216018 + 216018) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 216018 * (2 : ZMod 906046049813) ^ 216018 := by rw [pow_add]
          _ = 621026191557 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 906046049813) ^ 864072 = 483679791184 := by
        calc
          (2 : ZMod 906046049813) ^ 864072 = (2 : ZMod 906046049813) ^ (432036 + 432036) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 432036 * (2 : ZMod 906046049813) ^ 432036 := by rw [pow_add]
          _ = 483679791184 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 906046049813) ^ 1728145 = 503396835046 := by
        calc
          (2 : ZMod 906046049813) ^ 1728145 = (2 : ZMod 906046049813) ^ (864072 + 864072 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 864072 * (2 : ZMod 906046049813) ^ 864072) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 503396835046 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 906046049813) ^ 3456291 = 559651632025 := by
        calc
          (2 : ZMod 906046049813) ^ 3456291 = (2 : ZMod 906046049813) ^ (1728145 + 1728145 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 1728145 * (2 : ZMod 906046049813) ^ 1728145) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 559651632025 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 906046049813) ^ 6912582 = 840214961529 := by
        calc
          (2 : ZMod 906046049813) ^ 6912582 = (2 : ZMod 906046049813) ^ (3456291 + 3456291) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3456291 * (2 : ZMod 906046049813) ^ 3456291 := by rw [pow_add]
          _ = 840214961529 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 906046049813) ^ 13825165 = 715654956820 := by
        calc
          (2 : ZMod 906046049813) ^ 13825165 = (2 : ZMod 906046049813) ^ (6912582 + 6912582 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 6912582 * (2 : ZMod 906046049813) ^ 6912582) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 715654956820 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 906046049813) ^ 27650331 = 149763201253 := by
        calc
          (2 : ZMod 906046049813) ^ 27650331 = (2 : ZMod 906046049813) ^ (13825165 + 13825165 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 13825165 * (2 : ZMod 906046049813) ^ 13825165) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 149763201253 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 906046049813) ^ 55300662 = 526123736038 := by
        calc
          (2 : ZMod 906046049813) ^ 55300662 = (2 : ZMod 906046049813) ^ (27650331 + 27650331) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 27650331 * (2 : ZMod 906046049813) ^ 27650331 := by rw [pow_add]
          _ = 526123736038 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 906046049813) ^ 110601324 = 125285240207 := by
        calc
          (2 : ZMod 906046049813) ^ 110601324 = (2 : ZMod 906046049813) ^ (55300662 + 55300662) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 55300662 * (2 : ZMod 906046049813) ^ 55300662 := by rw [pow_add]
          _ = 125285240207 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 906046049813) ^ 221202648 = 878023949327 := by
        calc
          (2 : ZMod 906046049813) ^ 221202648 = (2 : ZMod 906046049813) ^ (110601324 + 110601324) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 110601324 * (2 : ZMod 906046049813) ^ 110601324 := by rw [pow_add]
          _ = 878023949327 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 906046049813) ^ 442405297 = 769514864956 := by
        calc
          (2 : ZMod 906046049813) ^ 442405297 = (2 : ZMod 906046049813) ^ (221202648 + 221202648 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 221202648 * (2 : ZMod 906046049813) ^ 221202648) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 769514864956 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 906046049813) ^ 884810595 = 828915423052 := by
        calc
          (2 : ZMod 906046049813) ^ 884810595 = (2 : ZMod 906046049813) ^ (442405297 + 442405297 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 442405297 * (2 : ZMod 906046049813) ^ 442405297) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 828915423052 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 906046049813) ^ 1769621191 = 582827890931 := by
        calc
          (2 : ZMod 906046049813) ^ 1769621191 = (2 : ZMod 906046049813) ^ (884810595 + 884810595 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 884810595 * (2 : ZMod 906046049813) ^ 884810595) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 582827890931 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 906046049813) ^ 3539242382 = 869819561844 := by
        calc
          (2 : ZMod 906046049813) ^ 3539242382 = (2 : ZMod 906046049813) ^ (1769621191 + 1769621191) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1769621191 * (2 : ZMod 906046049813) ^ 1769621191 := by rw [pow_add]
          _ = 869819561844 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 906046049813) ^ 7078484764 = 10252175527 := by
        calc
          (2 : ZMod 906046049813) ^ 7078484764 = (2 : ZMod 906046049813) ^ (3539242382 + 3539242382) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 3539242382 * (2 : ZMod 906046049813) ^ 3539242382 := by rw [pow_add]
          _ = 10252175527 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 906046049813) ^ 14156969528 = 617325016675 := by
        calc
          (2 : ZMod 906046049813) ^ 14156969528 = (2 : ZMod 906046049813) ^ (7078484764 + 7078484764) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 7078484764 * (2 : ZMod 906046049813) ^ 7078484764 := by rw [pow_add]
          _ = 617325016675 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 906046049813) ^ 28313939056 = 785696103902 := by
        calc
          (2 : ZMod 906046049813) ^ 28313939056 = (2 : ZMod 906046049813) ^ (14156969528 + 14156969528) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 14156969528 * (2 : ZMod 906046049813) ^ 14156969528 := by rw [pow_add]
          _ = 785696103902 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 906046049813) ^ 56627878113 = 436595603944 := by
        calc
          (2 : ZMod 906046049813) ^ 56627878113 = (2 : ZMod 906046049813) ^ (28313939056 + 28313939056 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 28313939056 * (2 : ZMod 906046049813) ^ 28313939056) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 436595603944 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 906046049813) ^ 113255756226 = 667405896325 := by
        calc
          (2 : ZMod 906046049813) ^ 113255756226 = (2 : ZMod 906046049813) ^ (56627878113 + 56627878113) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 56627878113 * (2 : ZMod 906046049813) ^ 56627878113 := by rw [pow_add]
          _ = 667405896325 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 906046049813) ^ 226511512453 = 477280306975 := by
        calc
          (2 : ZMod 906046049813) ^ 226511512453 = (2 : ZMod 906046049813) ^ (113255756226 + 113255756226 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 113255756226 * (2 : ZMod 906046049813) ^ 113255756226) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 477280306975 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 906046049813) ^ 453023024906 = 906046049812 := by
        calc
          (2 : ZMod 906046049813) ^ 453023024906 = (2 : ZMod 906046049813) ^ (226511512453 + 226511512453) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 226511512453 * (2 : ZMod 906046049813) ^ 226511512453 := by rw [pow_add]
          _ = 906046049812 := by rw [factor_0_37]; decide
      change (2 : ZMod 906046049813) ^ 453023024906 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (2 : ZMod 906046049813) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 906046049813) ^ 2 = 4 := by
        calc
          (2 : ZMod 906046049813) ^ 2 = (2 : ZMod 906046049813) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1 * (2 : ZMod 906046049813) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 906046049813) ^ 5 = 32 := by
        calc
          (2 : ZMod 906046049813) ^ 5 = (2 : ZMod 906046049813) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 2 * (2 : ZMod 906046049813) ^ 2) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 906046049813) ^ 11 = 2048 := by
        calc
          (2 : ZMod 906046049813) ^ 11 = (2 : ZMod 906046049813) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 5 * (2 : ZMod 906046049813) ^ 5) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 906046049813) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 906046049813) ^ 22 = (2 : ZMod 906046049813) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 11 * (2 : ZMod 906046049813) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 906046049813) ^ 45 = 754622195938 := by
        calc
          (2 : ZMod 906046049813) ^ 45 = (2 : ZMod 906046049813) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 22 * (2 : ZMod 906046049813) ^ 22) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 754622195938 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 906046049813) ^ 91 = 623956353767 := by
        calc
          (2 : ZMod 906046049813) ^ 91 = (2 : ZMod 906046049813) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 45 * (2 : ZMod 906046049813) ^ 45) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 623956353767 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 906046049813) ^ 182 = 310016837194 := by
        calc
          (2 : ZMod 906046049813) ^ 182 = (2 : ZMod 906046049813) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 91 * (2 : ZMod 906046049813) ^ 91 := by rw [pow_add]
          _ = 310016837194 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 906046049813) ^ 364 = 490815871010 := by
        calc
          (2 : ZMod 906046049813) ^ 364 = (2 : ZMod 906046049813) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 182 * (2 : ZMod 906046049813) ^ 182 := by rw [pow_add]
          _ = 490815871010 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 906046049813) ^ 729 = 354324634942 := by
        calc
          (2 : ZMod 906046049813) ^ 729 = (2 : ZMod 906046049813) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 364 * (2 : ZMod 906046049813) ^ 364) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 354324634942 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 906046049813) ^ 1459 = 537586959288 := by
        calc
          (2 : ZMod 906046049813) ^ 1459 = (2 : ZMod 906046049813) ^ (729 + 729 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 729 * (2 : ZMod 906046049813) ^ 729) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 537586959288 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 906046049813) ^ 2919 = 733703027364 := by
        calc
          (2 : ZMod 906046049813) ^ 2919 = (2 : ZMod 906046049813) ^ (1459 + 1459 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 1459 * (2 : ZMod 906046049813) ^ 1459) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 733703027364 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 906046049813) ^ 5838 = 74138453957 := by
        calc
          (2 : ZMod 906046049813) ^ 5838 = (2 : ZMod 906046049813) ^ (2919 + 2919) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 2919 * (2 : ZMod 906046049813) ^ 2919 := by rw [pow_add]
          _ = 74138453957 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 906046049813) ^ 11676 = 702838441411 := by
        calc
          (2 : ZMod 906046049813) ^ 11676 = (2 : ZMod 906046049813) ^ (5838 + 5838) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 5838 * (2 : ZMod 906046049813) ^ 5838 := by rw [pow_add]
          _ = 702838441411 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 906046049813) ^ 23353 = 111383066554 := by
        calc
          (2 : ZMod 906046049813) ^ 23353 = (2 : ZMod 906046049813) ^ (11676 + 11676 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 11676 * (2 : ZMod 906046049813) ^ 11676) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 111383066554 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 906046049813) ^ 46706 = 462033451735 := by
        calc
          (2 : ZMod 906046049813) ^ 46706 = (2 : ZMod 906046049813) ^ (23353 + 23353) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 23353 * (2 : ZMod 906046049813) ^ 23353 := by rw [pow_add]
          _ = 462033451735 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 906046049813) ^ 93413 = 539477615474 := by
        calc
          (2 : ZMod 906046049813) ^ 93413 = (2 : ZMod 906046049813) ^ (46706 + 46706 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 46706 * (2 : ZMod 906046049813) ^ 46706) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 539477615474 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 906046049813) ^ 186826 = 821438531897 := by
        calc
          (2 : ZMod 906046049813) ^ 186826 = (2 : ZMod 906046049813) ^ (93413 + 93413) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 93413 * (2 : ZMod 906046049813) ^ 93413 := by rw [pow_add]
          _ = 821438531897 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 906046049813) ^ 373653 = 506990426268 := by
        calc
          (2 : ZMod 906046049813) ^ 373653 = (2 : ZMod 906046049813) ^ (186826 + 186826 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 186826 * (2 : ZMod 906046049813) ^ 186826) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 506990426268 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 906046049813) ^ 747306 = 479547938090 := by
        calc
          (2 : ZMod 906046049813) ^ 747306 = (2 : ZMod 906046049813) ^ (373653 + 373653) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 373653 * (2 : ZMod 906046049813) ^ 373653 := by rw [pow_add]
          _ = 479547938090 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 906046049813) ^ 1494612 = 647198312227 := by
        calc
          (2 : ZMod 906046049813) ^ 1494612 = (2 : ZMod 906046049813) ^ (747306 + 747306) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 747306 * (2 : ZMod 906046049813) ^ 747306 := by rw [pow_add]
          _ = 647198312227 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 906046049813) ^ 2989224 = 232049274458 := by
        calc
          (2 : ZMod 906046049813) ^ 2989224 = (2 : ZMod 906046049813) ^ (1494612 + 1494612) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1494612 * (2 : ZMod 906046049813) ^ 1494612 := by rw [pow_add]
          _ = 232049274458 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 906046049813) ^ 5978449 = 557724119934 := by
        calc
          (2 : ZMod 906046049813) ^ 5978449 = (2 : ZMod 906046049813) ^ (2989224 + 2989224 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 2989224 * (2 : ZMod 906046049813) ^ 2989224) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 557724119934 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 906046049813) ^ 11956899 = 452452654772 := by
        calc
          (2 : ZMod 906046049813) ^ 11956899 = (2 : ZMod 906046049813) ^ (5978449 + 5978449 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 5978449 * (2 : ZMod 906046049813) ^ 5978449) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 452452654772 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 906046049813) ^ 23913799 = 280666708405 := by
        calc
          (2 : ZMod 906046049813) ^ 23913799 = (2 : ZMod 906046049813) ^ (11956899 + 11956899 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 11956899 * (2 : ZMod 906046049813) ^ 11956899) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 280666708405 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 906046049813) ^ 47827599 = 580362372487 := by
        calc
          (2 : ZMod 906046049813) ^ 47827599 = (2 : ZMod 906046049813) ^ (23913799 + 23913799 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 23913799 * (2 : ZMod 906046049813) ^ 23913799) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 580362372487 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 906046049813) ^ 95655199 = 310987183914 := by
        calc
          (2 : ZMod 906046049813) ^ 95655199 = (2 : ZMod 906046049813) ^ (47827599 + 47827599 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 47827599 * (2 : ZMod 906046049813) ^ 47827599) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 310987183914 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 906046049813) ^ 191310399 = 275856687210 := by
        calc
          (2 : ZMod 906046049813) ^ 191310399 = (2 : ZMod 906046049813) ^ (95655199 + 95655199 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 95655199 * (2 : ZMod 906046049813) ^ 95655199) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 275856687210 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 906046049813) ^ 382620798 = 772332248007 := by
        calc
          (2 : ZMod 906046049813) ^ 382620798 = (2 : ZMod 906046049813) ^ (191310399 + 191310399) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 191310399 * (2 : ZMod 906046049813) ^ 191310399 := by rw [pow_add]
          _ = 772332248007 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 906046049813) ^ 765241596 = 537088870944 := by
        calc
          (2 : ZMod 906046049813) ^ 765241596 = (2 : ZMod 906046049813) ^ (382620798 + 382620798) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 382620798 * (2 : ZMod 906046049813) ^ 382620798 := by rw [pow_add]
          _ = 537088870944 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 906046049813) ^ 1530483192 = 549204502495 := by
        calc
          (2 : ZMod 906046049813) ^ 1530483192 = (2 : ZMod 906046049813) ^ (765241596 + 765241596) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 765241596 * (2 : ZMod 906046049813) ^ 765241596 := by rw [pow_add]
          _ = 549204502495 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 906046049813) ^ 3060966384 = 851980041242 := by
        calc
          (2 : ZMod 906046049813) ^ 3060966384 = (2 : ZMod 906046049813) ^ (1530483192 + 1530483192) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1530483192 * (2 : ZMod 906046049813) ^ 1530483192 := by rw [pow_add]
          _ = 851980041242 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 906046049813) ^ 6121932769 = 427416938138 := by
        calc
          (2 : ZMod 906046049813) ^ 6121932769 = (2 : ZMod 906046049813) ^ (3060966384 + 3060966384 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 3060966384 * (2 : ZMod 906046049813) ^ 3060966384) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 427416938138 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 906046049813) ^ 12243865538 = 282054024380 := by
        calc
          (2 : ZMod 906046049813) ^ 12243865538 = (2 : ZMod 906046049813) ^ (6121932769 + 6121932769) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 6121932769 * (2 : ZMod 906046049813) ^ 6121932769 := by rw [pow_add]
          _ = 282054024380 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 906046049813) ^ 24487731076 = 837084430407 := by
        calc
          (2 : ZMod 906046049813) ^ 24487731076 = (2 : ZMod 906046049813) ^ (12243865538 + 12243865538) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 12243865538 * (2 : ZMod 906046049813) ^ 12243865538 := by rw [pow_add]
          _ = 837084430407 := by rw [factor_1_33]; decide
      change (2 : ZMod 906046049813) ^ 24487731076 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (2 : ZMod 906046049813) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 906046049813) ^ 2 = 4 := by
        calc
          (2 : ZMod 906046049813) ^ 2 = (2 : ZMod 906046049813) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1 * (2 : ZMod 906046049813) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 906046049813) ^ 5 = 32 := by
        calc
          (2 : ZMod 906046049813) ^ 5 = (2 : ZMod 906046049813) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 2 * (2 : ZMod 906046049813) ^ 2) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 906046049813) ^ 11 = 2048 := by
        calc
          (2 : ZMod 906046049813) ^ 11 = (2 : ZMod 906046049813) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 5 * (2 : ZMod 906046049813) ^ 5) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 906046049813) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 906046049813) ^ 23 = (2 : ZMod 906046049813) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 11 * (2 : ZMod 906046049813) ^ 11) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 906046049813) ^ 46 = 603198342063 := by
        calc
          (2 : ZMod 906046049813) ^ 46 = (2 : ZMod 906046049813) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 23 * (2 : ZMod 906046049813) ^ 23 := by rw [pow_add]
          _ = 603198342063 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 906046049813) ^ 92 = 341866657721 := by
        calc
          (2 : ZMod 906046049813) ^ 92 = (2 : ZMod 906046049813) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 46 * (2 : ZMod 906046049813) ^ 46 := by rw [pow_add]
          _ = 341866657721 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 906046049813) ^ 184 = 334021298963 := by
        calc
          (2 : ZMod 906046049813) ^ 184 = (2 : ZMod 906046049813) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 92 * (2 : ZMod 906046049813) ^ 92 := by rw [pow_add]
          _ = 334021298963 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 906046049813) ^ 368 = 604685537656 := by
        calc
          (2 : ZMod 906046049813) ^ 368 = (2 : ZMod 906046049813) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 184 * (2 : ZMod 906046049813) ^ 184 := by rw [pow_add]
          _ = 604685537656 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 906046049813) ^ 736 = 51250781926 := by
        calc
          (2 : ZMod 906046049813) ^ 736 = (2 : ZMod 906046049813) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 368 * (2 : ZMod 906046049813) ^ 368 := by rw [pow_add]
          _ = 51250781926 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 906046049813) ^ 1472 = 528568396116 := by
        calc
          (2 : ZMod 906046049813) ^ 1472 = (2 : ZMod 906046049813) ^ (736 + 736) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 736 * (2 : ZMod 906046049813) ^ 736 := by rw [pow_add]
          _ = 528568396116 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 906046049813) ^ 2944 = 209195871613 := by
        calc
          (2 : ZMod 906046049813) ^ 2944 = (2 : ZMod 906046049813) ^ (1472 + 1472) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1472 * (2 : ZMod 906046049813) ^ 1472 := by rw [pow_add]
          _ = 209195871613 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 906046049813) ^ 5888 = 735189249018 := by
        calc
          (2 : ZMod 906046049813) ^ 5888 = (2 : ZMod 906046049813) ^ (2944 + 2944) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 2944 * (2 : ZMod 906046049813) ^ 2944 := by rw [pow_add]
          _ = 735189249018 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 906046049813) ^ 11776 = 511662422091 := by
        calc
          (2 : ZMod 906046049813) ^ 11776 = (2 : ZMod 906046049813) ^ (5888 + 5888) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 5888 * (2 : ZMod 906046049813) ^ 5888 := by rw [pow_add]
          _ = 511662422091 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 906046049813) ^ 23552 = 58887050498 := by
        calc
          (2 : ZMod 906046049813) ^ 23552 = (2 : ZMod 906046049813) ^ (11776 + 11776) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 11776 * (2 : ZMod 906046049813) ^ 11776 := by rw [pow_add]
          _ = 58887050498 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 906046049813) ^ 47104 = 234121770045 := by
        calc
          (2 : ZMod 906046049813) ^ 47104 = (2 : ZMod 906046049813) ^ (23552 + 23552) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 23552 * (2 : ZMod 906046049813) ^ 23552 := by rw [pow_add]
          _ = 234121770045 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 906046049813) ^ 94208 = 691511605274 := by
        calc
          (2 : ZMod 906046049813) ^ 94208 = (2 : ZMod 906046049813) ^ (47104 + 47104) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 47104 * (2 : ZMod 906046049813) ^ 47104 := by rw [pow_add]
          _ = 691511605274 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 906046049813) ^ 188417 = 373412880678 := by
        calc
          (2 : ZMod 906046049813) ^ 188417 = (2 : ZMod 906046049813) ^ (94208 + 94208 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 94208 * (2 : ZMod 906046049813) ^ 94208) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 373412880678 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 906046049813) ^ 376835 = 743888005529 := by
        calc
          (2 : ZMod 906046049813) ^ 376835 = (2 : ZMod 906046049813) ^ (188417 + 188417 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 188417 * (2 : ZMod 906046049813) ^ 188417) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 743888005529 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 906046049813) ^ 753671 = 742111067857 := by
        calc
          (2 : ZMod 906046049813) ^ 753671 = (2 : ZMod 906046049813) ^ (376835 + 376835 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 376835 * (2 : ZMod 906046049813) ^ 376835) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 742111067857 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 906046049813) ^ 1507343 = 426161648404 := by
        calc
          (2 : ZMod 906046049813) ^ 1507343 = (2 : ZMod 906046049813) ^ (753671 + 753671 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 753671 * (2 : ZMod 906046049813) ^ 753671) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 426161648404 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 906046049813) ^ 3014686 = 120075499282 := by
        calc
          (2 : ZMod 906046049813) ^ 3014686 = (2 : ZMod 906046049813) ^ (1507343 + 1507343) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1507343 * (2 : ZMod 906046049813) ^ 1507343 := by rw [pow_add]
          _ = 120075499282 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 906046049813) ^ 6029373 = 312601220731 := by
        calc
          (2 : ZMod 906046049813) ^ 6029373 = (2 : ZMod 906046049813) ^ (3014686 + 3014686 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 3014686 * (2 : ZMod 906046049813) ^ 3014686) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 312601220731 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 906046049813) ^ 12058747 = 717959993925 := by
        calc
          (2 : ZMod 906046049813) ^ 12058747 = (2 : ZMod 906046049813) ^ (6029373 + 6029373 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 6029373 * (2 : ZMod 906046049813) ^ 6029373) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 717959993925 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 906046049813) ^ 24117494 = 351035848148 := by
        calc
          (2 : ZMod 906046049813) ^ 24117494 = (2 : ZMod 906046049813) ^ (12058747 + 12058747) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 12058747 * (2 : ZMod 906046049813) ^ 12058747 := by rw [pow_add]
          _ = 351035848148 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 906046049813) ^ 48234989 = 712778275763 := by
        calc
          (2 : ZMod 906046049813) ^ 48234989 = (2 : ZMod 906046049813) ^ (24117494 + 24117494 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 24117494 * (2 : ZMod 906046049813) ^ 24117494) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 712778275763 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 906046049813) ^ 96469979 = 530843232293 := by
        calc
          (2 : ZMod 906046049813) ^ 96469979 = (2 : ZMod 906046049813) ^ (48234989 + 48234989 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 48234989 * (2 : ZMod 906046049813) ^ 48234989) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 530843232293 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 906046049813) ^ 192939959 = 543257301290 := by
        calc
          (2 : ZMod 906046049813) ^ 192939959 = (2 : ZMod 906046049813) ^ (96469979 + 96469979 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 96469979 * (2 : ZMod 906046049813) ^ 96469979) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 543257301290 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 906046049813) ^ 385879919 = 705952660533 := by
        calc
          (2 : ZMod 906046049813) ^ 385879919 = (2 : ZMod 906046049813) ^ (192939959 + 192939959 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 192939959 * (2 : ZMod 906046049813) ^ 192939959) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 705952660533 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 906046049813) ^ 771759838 = 345239386615 := by
        calc
          (2 : ZMod 906046049813) ^ 771759838 = (2 : ZMod 906046049813) ^ (385879919 + 385879919) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 385879919 * (2 : ZMod 906046049813) ^ 385879919 := by rw [pow_add]
          _ = 345239386615 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 906046049813) ^ 1543519676 = 506570560472 := by
        calc
          (2 : ZMod 906046049813) ^ 1543519676 = (2 : ZMod 906046049813) ^ (771759838 + 771759838) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 771759838 * (2 : ZMod 906046049813) ^ 771759838 := by rw [pow_add]
          _ = 506570560472 := by rw [factor_2_29]; decide
      change (2 : ZMod 906046049813) ^ 1543519676 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (2 : ZMod 906046049813) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 906046049813) ^ 2 = 4 := by
        calc
          (2 : ZMod 906046049813) ^ 2 = (2 : ZMod 906046049813) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1 * (2 : ZMod 906046049813) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 906046049813) ^ 5 = 32 := by
        calc
          (2 : ZMod 906046049813) ^ 5 = (2 : ZMod 906046049813) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 2 * (2 : ZMod 906046049813) ^ 2) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 906046049813) ^ 10 = 1024 := by
        calc
          (2 : ZMod 906046049813) ^ 10 = (2 : ZMod 906046049813) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 5 * (2 : ZMod 906046049813) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 906046049813) ^ 21 = 2097152 := by
        calc
          (2 : ZMod 906046049813) ^ 21 = (2 : ZMod 906046049813) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 10 * (2 : ZMod 906046049813) ^ 10) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 2097152 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 906046049813) ^ 42 = 773862311852 := by
        calc
          (2 : ZMod 906046049813) ^ 42 = (2 : ZMod 906046049813) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 21 * (2 : ZMod 906046049813) ^ 21 := by rw [pow_add]
          _ = 773862311852 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 906046049813) ^ 84 = 833057376421 := by
        calc
          (2 : ZMod 906046049813) ^ 84 = (2 : ZMod 906046049813) ^ (42 + 42) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 42 * (2 : ZMod 906046049813) ^ 42 := by rw [pow_add]
          _ = 833057376421 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 906046049813) ^ 169 = 633341027596 := by
        calc
          (2 : ZMod 906046049813) ^ 169 = (2 : ZMod 906046049813) ^ (84 + 84 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 84 * (2 : ZMod 906046049813) ^ 84) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 633341027596 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 906046049813) ^ 339 = 88024141657 := by
        calc
          (2 : ZMod 906046049813) ^ 339 = (2 : ZMod 906046049813) ^ (169 + 169 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 169 * (2 : ZMod 906046049813) ^ 169) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 88024141657 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 906046049813) ^ 678 = 569489906715 := by
        calc
          (2 : ZMod 906046049813) ^ 678 = (2 : ZMod 906046049813) ^ (339 + 339) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 339 * (2 : ZMod 906046049813) ^ 339 := by rw [pow_add]
          _ = 569489906715 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 906046049813) ^ 1357 = 513154517812 := by
        calc
          (2 : ZMod 906046049813) ^ 1357 = (2 : ZMod 906046049813) ^ (678 + 678 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 678 * (2 : ZMod 906046049813) ^ 678) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 513154517812 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 906046049813) ^ 2714 = 737855358749 := by
        calc
          (2 : ZMod 906046049813) ^ 2714 = (2 : ZMod 906046049813) ^ (1357 + 1357) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 1357 * (2 : ZMod 906046049813) ^ 1357 := by rw [pow_add]
          _ = 737855358749 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 906046049813) ^ 5429 = 420509776037 := by
        calc
          (2 : ZMod 906046049813) ^ 5429 = (2 : ZMod 906046049813) ^ (2714 + 2714 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 2714 * (2 : ZMod 906046049813) ^ 2714) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 420509776037 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 906046049813) ^ 10859 = 797645251760 := by
        calc
          (2 : ZMod 906046049813) ^ 10859 = (2 : ZMod 906046049813) ^ (5429 + 5429 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 5429 * (2 : ZMod 906046049813) ^ 5429) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 797645251760 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 906046049813) ^ 21719 = 483178936070 := by
        calc
          (2 : ZMod 906046049813) ^ 21719 = (2 : ZMod 906046049813) ^ (10859 + 10859 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = ((2 : ZMod 906046049813) ^ 10859 * (2 : ZMod 906046049813) ^ 10859) * (2 : ZMod 906046049813) := by rw [pow_succ, pow_add]
          _ = 483178936070 := by rw [factor_3_13]; decide
      have factor_3_15 : (2 : ZMod 906046049813) ^ 43438 = 519267248446 := by
        calc
          (2 : ZMod 906046049813) ^ 43438 = (2 : ZMod 906046049813) ^ (21719 + 21719) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 21719 * (2 : ZMod 906046049813) ^ 21719 := by rw [pow_add]
          _ = 519267248446 := by rw [factor_3_14]; decide
      have factor_3_16 : (2 : ZMod 906046049813) ^ 86876 = 728950942525 := by
        calc
          (2 : ZMod 906046049813) ^ 86876 = (2 : ZMod 906046049813) ^ (43438 + 43438) :=
            congrArg (fun n : ℕ => (2 : ZMod 906046049813) ^ n) (by norm_num)
          _ = (2 : ZMod 906046049813) ^ 43438 * (2 : ZMod 906046049813) ^ 43438 := by rw [pow_add]
          _ = 728950942525 := by rw [factor_3_15]; decide
      change (2 : ZMod 906046049813) ^ 86876 ≠ 1
      rw [factor_3_16]
      decide

#print axioms prime_lucas_906046049813

end TotientTailPeriodKiller
end Erdos249257
