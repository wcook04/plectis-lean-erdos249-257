import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime382775276171

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3062202209369 : Nat.Prime 3062202209369 := by
  apply lucas_primality 3062202209369 (3 : ZMod 3062202209369)
  ·
      have fermat_0 : (3 : ZMod 3062202209369) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 3062202209369) ^ 2 = 9 := by
        calc
          (3 : ZMod 3062202209369) ^ 2 = (3 : ZMod 3062202209369) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 1 * (3 : ZMod 3062202209369) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 3062202209369) ^ 5 = 243 := by
        calc
          (3 : ZMod 3062202209369) ^ 5 = (3 : ZMod 3062202209369) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 2 * (3 : ZMod 3062202209369) ^ 2) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 3062202209369) ^ 11 = 177147 := by
        calc
          (3 : ZMod 3062202209369) ^ 11 = (3 : ZMod 3062202209369) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 5 * (3 : ZMod 3062202209369) ^ 5) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 3062202209369) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 3062202209369) ^ 22 = (3 : ZMod 3062202209369) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 11 * (3 : ZMod 3062202209369) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 3062202209369) ^ 44 = 659387605077 := by
        calc
          (3 : ZMod 3062202209369) ^ 44 = (3 : ZMod 3062202209369) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 22 * (3 : ZMod 3062202209369) ^ 22 := by rw [pow_add]
          _ = 659387605077 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 3062202209369) ^ 89 = 2653308566310 := by
        calc
          (3 : ZMod 3062202209369) ^ 89 = (3 : ZMod 3062202209369) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 44 * (3 : ZMod 3062202209369) ^ 44) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2653308566310 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 3062202209369) ^ 178 = 1032930556326 := by
        calc
          (3 : ZMod 3062202209369) ^ 178 = (3 : ZMod 3062202209369) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 89 * (3 : ZMod 3062202209369) ^ 89 := by rw [pow_add]
          _ = 1032930556326 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 3062202209369) ^ 356 = 173269684931 := by
        calc
          (3 : ZMod 3062202209369) ^ 356 = (3 : ZMod 3062202209369) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 178 * (3 : ZMod 3062202209369) ^ 178 := by rw [pow_add]
          _ = 173269684931 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 3062202209369) ^ 712 = 1236761358793 := by
        calc
          (3 : ZMod 3062202209369) ^ 712 = (3 : ZMod 3062202209369) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 356 * (3 : ZMod 3062202209369) ^ 356 := by rw [pow_add]
          _ = 1236761358793 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 3062202209369) ^ 1425 = 169820485212 := by
        calc
          (3 : ZMod 3062202209369) ^ 1425 = (3 : ZMod 3062202209369) ^ (712 + 712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 712 * (3 : ZMod 3062202209369) ^ 712) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 169820485212 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 3062202209369) ^ 2851 = 1803237850273 := by
        calc
          (3 : ZMod 3062202209369) ^ 2851 = (3 : ZMod 3062202209369) ^ (1425 + 1425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 1425 * (3 : ZMod 3062202209369) ^ 1425) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1803237850273 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 3062202209369) ^ 5703 = 2345364333325 := by
        calc
          (3 : ZMod 3062202209369) ^ 5703 = (3 : ZMod 3062202209369) ^ (2851 + 2851 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 2851 * (3 : ZMod 3062202209369) ^ 2851) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2345364333325 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 3062202209369) ^ 11407 = 3039403455482 := by
        calc
          (3 : ZMod 3062202209369) ^ 11407 = (3 : ZMod 3062202209369) ^ (5703 + 5703 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 5703 * (3 : ZMod 3062202209369) ^ 5703) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 3039403455482 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 3062202209369) ^ 22815 = 2171542181801 := by
        calc
          (3 : ZMod 3062202209369) ^ 22815 = (3 : ZMod 3062202209369) ^ (11407 + 11407 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 11407 * (3 : ZMod 3062202209369) ^ 11407) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2171542181801 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 3062202209369) ^ 45630 = 13697901134 := by
        calc
          (3 : ZMod 3062202209369) ^ 45630 = (3 : ZMod 3062202209369) ^ (22815 + 22815) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 22815 * (3 : ZMod 3062202209369) ^ 22815 := by rw [pow_add]
          _ = 13697901134 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 3062202209369) ^ 91260 = 2276400887597 := by
        calc
          (3 : ZMod 3062202209369) ^ 91260 = (3 : ZMod 3062202209369) ^ (45630 + 45630) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 45630 * (3 : ZMod 3062202209369) ^ 45630 := by rw [pow_add]
          _ = 2276400887597 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 3062202209369) ^ 182521 = 2969873660553 := by
        calc
          (3 : ZMod 3062202209369) ^ 182521 = (3 : ZMod 3062202209369) ^ (91260 + 91260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 91260 * (3 : ZMod 3062202209369) ^ 91260) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2969873660553 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 3062202209369) ^ 365042 = 3011731819084 := by
        calc
          (3 : ZMod 3062202209369) ^ 365042 = (3 : ZMod 3062202209369) ^ (182521 + 182521) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 182521 * (3 : ZMod 3062202209369) ^ 182521 := by rw [pow_add]
          _ = 3011731819084 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 3062202209369) ^ 730085 = 330448533225 := by
        calc
          (3 : ZMod 3062202209369) ^ 730085 = (3 : ZMod 3062202209369) ^ (365042 + 365042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 365042 * (3 : ZMod 3062202209369) ^ 365042) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 330448533225 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 3062202209369) ^ 1460171 = 2297468681476 := by
        calc
          (3 : ZMod 3062202209369) ^ 1460171 = (3 : ZMod 3062202209369) ^ (730085 + 730085 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 730085 * (3 : ZMod 3062202209369) ^ 730085) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2297468681476 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 3062202209369) ^ 2920343 = 961195047659 := by
        calc
          (3 : ZMod 3062202209369) ^ 2920343 = (3 : ZMod 3062202209369) ^ (1460171 + 1460171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 1460171 * (3 : ZMod 3062202209369) ^ 1460171) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 961195047659 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 3062202209369) ^ 5840687 = 1060974600454 := by
        calc
          (3 : ZMod 3062202209369) ^ 5840687 = (3 : ZMod 3062202209369) ^ (2920343 + 2920343 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 2920343 * (3 : ZMod 3062202209369) ^ 2920343) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1060974600454 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 3062202209369) ^ 11681374 = 1158722924219 := by
        calc
          (3 : ZMod 3062202209369) ^ 11681374 = (3 : ZMod 3062202209369) ^ (5840687 + 5840687) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 5840687 * (3 : ZMod 3062202209369) ^ 5840687 := by rw [pow_add]
          _ = 1158722924219 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 3062202209369) ^ 23362748 = 1933018849853 := by
        calc
          (3 : ZMod 3062202209369) ^ 23362748 = (3 : ZMod 3062202209369) ^ (11681374 + 11681374) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 11681374 * (3 : ZMod 3062202209369) ^ 11681374 := by rw [pow_add]
          _ = 1933018849853 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 3062202209369) ^ 46725497 = 2737051080940 := by
        calc
          (3 : ZMod 3062202209369) ^ 46725497 = (3 : ZMod 3062202209369) ^ (23362748 + 23362748 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 23362748 * (3 : ZMod 3062202209369) ^ 23362748) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2737051080940 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 3062202209369) ^ 93450995 = 1586239710995 := by
        calc
          (3 : ZMod 3062202209369) ^ 93450995 = (3 : ZMod 3062202209369) ^ (46725497 + 46725497 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 46725497 * (3 : ZMod 3062202209369) ^ 46725497) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1586239710995 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 3062202209369) ^ 186901990 = 1735133776136 := by
        calc
          (3 : ZMod 3062202209369) ^ 186901990 = (3 : ZMod 3062202209369) ^ (93450995 + 93450995) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 93450995 * (3 : ZMod 3062202209369) ^ 93450995 := by rw [pow_add]
          _ = 1735133776136 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 3062202209369) ^ 373803980 = 2172369532860 := by
        calc
          (3 : ZMod 3062202209369) ^ 373803980 = (3 : ZMod 3062202209369) ^ (186901990 + 186901990) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 186901990 * (3 : ZMod 3062202209369) ^ 186901990 := by rw [pow_add]
          _ = 2172369532860 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 3062202209369) ^ 747607961 = 2770546922940 := by
        calc
          (3 : ZMod 3062202209369) ^ 747607961 = (3 : ZMod 3062202209369) ^ (373803980 + 373803980 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 373803980 * (3 : ZMod 3062202209369) ^ 373803980) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2770546922940 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 3062202209369) ^ 1495215922 = 1319070214577 := by
        calc
          (3 : ZMod 3062202209369) ^ 1495215922 = (3 : ZMod 3062202209369) ^ (747607961 + 747607961) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 747607961 * (3 : ZMod 3062202209369) ^ 747607961 := by rw [pow_add]
          _ = 1319070214577 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 3062202209369) ^ 2990431845 = 2371148925846 := by
        calc
          (3 : ZMod 3062202209369) ^ 2990431845 = (3 : ZMod 3062202209369) ^ (1495215922 + 1495215922 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 1495215922 * (3 : ZMod 3062202209369) ^ 1495215922) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2371148925846 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 3062202209369) ^ 5980863690 = 1419774617258 := by
        calc
          (3 : ZMod 3062202209369) ^ 5980863690 = (3 : ZMod 3062202209369) ^ (2990431845 + 2990431845) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 2990431845 * (3 : ZMod 3062202209369) ^ 2990431845 := by rw [pow_add]
          _ = 1419774617258 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 3062202209369) ^ 11961727380 = 2109479971014 := by
        calc
          (3 : ZMod 3062202209369) ^ 11961727380 = (3 : ZMod 3062202209369) ^ (5980863690 + 5980863690) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 5980863690 * (3 : ZMod 3062202209369) ^ 5980863690 := by rw [pow_add]
          _ = 2109479971014 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 3062202209369) ^ 23923454760 = 2876189569209 := by
        calc
          (3 : ZMod 3062202209369) ^ 23923454760 = (3 : ZMod 3062202209369) ^ (11961727380 + 11961727380) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 11961727380 * (3 : ZMod 3062202209369) ^ 11961727380 := by rw [pow_add]
          _ = 2876189569209 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 3062202209369) ^ 47846909521 = 2184396699939 := by
        calc
          (3 : ZMod 3062202209369) ^ 47846909521 = (3 : ZMod 3062202209369) ^ (23923454760 + 23923454760 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 23923454760 * (3 : ZMod 3062202209369) ^ 23923454760) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2184396699939 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 3062202209369) ^ 95693819042 = 2863978830104 := by
        calc
          (3 : ZMod 3062202209369) ^ 95693819042 = (3 : ZMod 3062202209369) ^ (47846909521 + 47846909521) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 47846909521 * (3 : ZMod 3062202209369) ^ 47846909521 := by rw [pow_add]
          _ = 2863978830104 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 3062202209369) ^ 191387638085 = 1936807925307 := by
        calc
          (3 : ZMod 3062202209369) ^ 191387638085 = (3 : ZMod 3062202209369) ^ (95693819042 + 95693819042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 95693819042 * (3 : ZMod 3062202209369) ^ 95693819042) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1936807925307 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 3062202209369) ^ 382775276171 = 1957991011979 := by
        calc
          (3 : ZMod 3062202209369) ^ 382775276171 = (3 : ZMod 3062202209369) ^ (191387638085 + 191387638085 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 191387638085 * (3 : ZMod 3062202209369) ^ 191387638085) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1957991011979 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 3062202209369) ^ 765550552342 = 283647441283 := by
        calc
          (3 : ZMod 3062202209369) ^ 765550552342 = (3 : ZMod 3062202209369) ^ (382775276171 + 382775276171) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 382775276171 * (3 : ZMod 3062202209369) ^ 382775276171 := by rw [pow_add]
          _ = 283647441283 := by rw [fermat_38]; decide
      have fermat_40 : (3 : ZMod 3062202209369) ^ 1531101104684 = 3062202209368 := by
        calc
          (3 : ZMod 3062202209369) ^ 1531101104684 = (3 : ZMod 3062202209369) ^ (765550552342 + 765550552342) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 765550552342 * (3 : ZMod 3062202209369) ^ 765550552342 := by rw [pow_add]
          _ = 3062202209368 := by rw [fermat_39]; decide
      have fermat_41 : (3 : ZMod 3062202209369) ^ 3062202209368 = 1 := by
        calc
          (3 : ZMod 3062202209369) ^ 3062202209368 = (3 : ZMod 3062202209369) ^ (1531101104684 + 1531101104684) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 1531101104684 * (3 : ZMod 3062202209369) ^ 1531101104684 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (382775276171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (382775276171, 1)] : List FactorBlock).map factorBlockValue).prod = 3062202209369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_382775276171) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 3062202209369) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 3062202209369) ^ 2 = 9 := by
        calc
          (3 : ZMod 3062202209369) ^ 2 = (3 : ZMod 3062202209369) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 1 * (3 : ZMod 3062202209369) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 3062202209369) ^ 5 = 243 := by
        calc
          (3 : ZMod 3062202209369) ^ 5 = (3 : ZMod 3062202209369) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 2 * (3 : ZMod 3062202209369) ^ 2) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 3062202209369) ^ 11 = 177147 := by
        calc
          (3 : ZMod 3062202209369) ^ 11 = (3 : ZMod 3062202209369) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 5 * (3 : ZMod 3062202209369) ^ 5) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 177147 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 3062202209369) ^ 22 = 31381059609 := by
        calc
          (3 : ZMod 3062202209369) ^ 22 = (3 : ZMod 3062202209369) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 11 * (3 : ZMod 3062202209369) ^ 11 := by rw [pow_add]
          _ = 31381059609 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 3062202209369) ^ 44 = 659387605077 := by
        calc
          (3 : ZMod 3062202209369) ^ 44 = (3 : ZMod 3062202209369) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 22 * (3 : ZMod 3062202209369) ^ 22 := by rw [pow_add]
          _ = 659387605077 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 3062202209369) ^ 89 = 2653308566310 := by
        calc
          (3 : ZMod 3062202209369) ^ 89 = (3 : ZMod 3062202209369) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 44 * (3 : ZMod 3062202209369) ^ 44) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2653308566310 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 3062202209369) ^ 178 = 1032930556326 := by
        calc
          (3 : ZMod 3062202209369) ^ 178 = (3 : ZMod 3062202209369) ^ (89 + 89) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 89 * (3 : ZMod 3062202209369) ^ 89 := by rw [pow_add]
          _ = 1032930556326 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 3062202209369) ^ 356 = 173269684931 := by
        calc
          (3 : ZMod 3062202209369) ^ 356 = (3 : ZMod 3062202209369) ^ (178 + 178) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 178 * (3 : ZMod 3062202209369) ^ 178 := by rw [pow_add]
          _ = 173269684931 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 3062202209369) ^ 712 = 1236761358793 := by
        calc
          (3 : ZMod 3062202209369) ^ 712 = (3 : ZMod 3062202209369) ^ (356 + 356) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 356 * (3 : ZMod 3062202209369) ^ 356 := by rw [pow_add]
          _ = 1236761358793 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 3062202209369) ^ 1425 = 169820485212 := by
        calc
          (3 : ZMod 3062202209369) ^ 1425 = (3 : ZMod 3062202209369) ^ (712 + 712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 712 * (3 : ZMod 3062202209369) ^ 712) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 169820485212 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 3062202209369) ^ 2851 = 1803237850273 := by
        calc
          (3 : ZMod 3062202209369) ^ 2851 = (3 : ZMod 3062202209369) ^ (1425 + 1425 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 1425 * (3 : ZMod 3062202209369) ^ 1425) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1803237850273 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 3062202209369) ^ 5703 = 2345364333325 := by
        calc
          (3 : ZMod 3062202209369) ^ 5703 = (3 : ZMod 3062202209369) ^ (2851 + 2851 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 2851 * (3 : ZMod 3062202209369) ^ 2851) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2345364333325 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 3062202209369) ^ 11407 = 3039403455482 := by
        calc
          (3 : ZMod 3062202209369) ^ 11407 = (3 : ZMod 3062202209369) ^ (5703 + 5703 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 5703 * (3 : ZMod 3062202209369) ^ 5703) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 3039403455482 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 3062202209369) ^ 22815 = 2171542181801 := by
        calc
          (3 : ZMod 3062202209369) ^ 22815 = (3 : ZMod 3062202209369) ^ (11407 + 11407 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 11407 * (3 : ZMod 3062202209369) ^ 11407) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2171542181801 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 3062202209369) ^ 45630 = 13697901134 := by
        calc
          (3 : ZMod 3062202209369) ^ 45630 = (3 : ZMod 3062202209369) ^ (22815 + 22815) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 22815 * (3 : ZMod 3062202209369) ^ 22815 := by rw [pow_add]
          _ = 13697901134 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 3062202209369) ^ 91260 = 2276400887597 := by
        calc
          (3 : ZMod 3062202209369) ^ 91260 = (3 : ZMod 3062202209369) ^ (45630 + 45630) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 45630 * (3 : ZMod 3062202209369) ^ 45630 := by rw [pow_add]
          _ = 2276400887597 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 3062202209369) ^ 182521 = 2969873660553 := by
        calc
          (3 : ZMod 3062202209369) ^ 182521 = (3 : ZMod 3062202209369) ^ (91260 + 91260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 91260 * (3 : ZMod 3062202209369) ^ 91260) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2969873660553 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 3062202209369) ^ 365042 = 3011731819084 := by
        calc
          (3 : ZMod 3062202209369) ^ 365042 = (3 : ZMod 3062202209369) ^ (182521 + 182521) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 182521 * (3 : ZMod 3062202209369) ^ 182521 := by rw [pow_add]
          _ = 3011731819084 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 3062202209369) ^ 730085 = 330448533225 := by
        calc
          (3 : ZMod 3062202209369) ^ 730085 = (3 : ZMod 3062202209369) ^ (365042 + 365042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 365042 * (3 : ZMod 3062202209369) ^ 365042) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 330448533225 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 3062202209369) ^ 1460171 = 2297468681476 := by
        calc
          (3 : ZMod 3062202209369) ^ 1460171 = (3 : ZMod 3062202209369) ^ (730085 + 730085 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 730085 * (3 : ZMod 3062202209369) ^ 730085) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2297468681476 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 3062202209369) ^ 2920343 = 961195047659 := by
        calc
          (3 : ZMod 3062202209369) ^ 2920343 = (3 : ZMod 3062202209369) ^ (1460171 + 1460171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 1460171 * (3 : ZMod 3062202209369) ^ 1460171) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 961195047659 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 3062202209369) ^ 5840687 = 1060974600454 := by
        calc
          (3 : ZMod 3062202209369) ^ 5840687 = (3 : ZMod 3062202209369) ^ (2920343 + 2920343 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 2920343 * (3 : ZMod 3062202209369) ^ 2920343) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1060974600454 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 3062202209369) ^ 11681374 = 1158722924219 := by
        calc
          (3 : ZMod 3062202209369) ^ 11681374 = (3 : ZMod 3062202209369) ^ (5840687 + 5840687) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 5840687 * (3 : ZMod 3062202209369) ^ 5840687 := by rw [pow_add]
          _ = 1158722924219 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 3062202209369) ^ 23362748 = 1933018849853 := by
        calc
          (3 : ZMod 3062202209369) ^ 23362748 = (3 : ZMod 3062202209369) ^ (11681374 + 11681374) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 11681374 * (3 : ZMod 3062202209369) ^ 11681374 := by rw [pow_add]
          _ = 1933018849853 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 3062202209369) ^ 46725497 = 2737051080940 := by
        calc
          (3 : ZMod 3062202209369) ^ 46725497 = (3 : ZMod 3062202209369) ^ (23362748 + 23362748 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 23362748 * (3 : ZMod 3062202209369) ^ 23362748) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2737051080940 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 3062202209369) ^ 93450995 = 1586239710995 := by
        calc
          (3 : ZMod 3062202209369) ^ 93450995 = (3 : ZMod 3062202209369) ^ (46725497 + 46725497 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 46725497 * (3 : ZMod 3062202209369) ^ 46725497) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1586239710995 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 3062202209369) ^ 186901990 = 1735133776136 := by
        calc
          (3 : ZMod 3062202209369) ^ 186901990 = (3 : ZMod 3062202209369) ^ (93450995 + 93450995) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 93450995 * (3 : ZMod 3062202209369) ^ 93450995 := by rw [pow_add]
          _ = 1735133776136 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 3062202209369) ^ 373803980 = 2172369532860 := by
        calc
          (3 : ZMod 3062202209369) ^ 373803980 = (3 : ZMod 3062202209369) ^ (186901990 + 186901990) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 186901990 * (3 : ZMod 3062202209369) ^ 186901990 := by rw [pow_add]
          _ = 2172369532860 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 3062202209369) ^ 747607961 = 2770546922940 := by
        calc
          (3 : ZMod 3062202209369) ^ 747607961 = (3 : ZMod 3062202209369) ^ (373803980 + 373803980 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 373803980 * (3 : ZMod 3062202209369) ^ 373803980) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2770546922940 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 3062202209369) ^ 1495215922 = 1319070214577 := by
        calc
          (3 : ZMod 3062202209369) ^ 1495215922 = (3 : ZMod 3062202209369) ^ (747607961 + 747607961) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 747607961 * (3 : ZMod 3062202209369) ^ 747607961 := by rw [pow_add]
          _ = 1319070214577 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 3062202209369) ^ 2990431845 = 2371148925846 := by
        calc
          (3 : ZMod 3062202209369) ^ 2990431845 = (3 : ZMod 3062202209369) ^ (1495215922 + 1495215922 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 1495215922 * (3 : ZMod 3062202209369) ^ 1495215922) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2371148925846 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 3062202209369) ^ 5980863690 = 1419774617258 := by
        calc
          (3 : ZMod 3062202209369) ^ 5980863690 = (3 : ZMod 3062202209369) ^ (2990431845 + 2990431845) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 2990431845 * (3 : ZMod 3062202209369) ^ 2990431845 := by rw [pow_add]
          _ = 1419774617258 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 3062202209369) ^ 11961727380 = 2109479971014 := by
        calc
          (3 : ZMod 3062202209369) ^ 11961727380 = (3 : ZMod 3062202209369) ^ (5980863690 + 5980863690) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 5980863690 * (3 : ZMod 3062202209369) ^ 5980863690 := by rw [pow_add]
          _ = 2109479971014 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 3062202209369) ^ 23923454760 = 2876189569209 := by
        calc
          (3 : ZMod 3062202209369) ^ 23923454760 = (3 : ZMod 3062202209369) ^ (11961727380 + 11961727380) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 11961727380 * (3 : ZMod 3062202209369) ^ 11961727380 := by rw [pow_add]
          _ = 2876189569209 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 3062202209369) ^ 47846909521 = 2184396699939 := by
        calc
          (3 : ZMod 3062202209369) ^ 47846909521 = (3 : ZMod 3062202209369) ^ (23923454760 + 23923454760 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 23923454760 * (3 : ZMod 3062202209369) ^ 23923454760) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 2184396699939 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 3062202209369) ^ 95693819042 = 2863978830104 := by
        calc
          (3 : ZMod 3062202209369) ^ 95693819042 = (3 : ZMod 3062202209369) ^ (47846909521 + 47846909521) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 47846909521 * (3 : ZMod 3062202209369) ^ 47846909521 := by rw [pow_add]
          _ = 2863978830104 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 3062202209369) ^ 191387638085 = 1936807925307 := by
        calc
          (3 : ZMod 3062202209369) ^ 191387638085 = (3 : ZMod 3062202209369) ^ (95693819042 + 95693819042 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 95693819042 * (3 : ZMod 3062202209369) ^ 95693819042) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1936807925307 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 3062202209369) ^ 382775276171 = 1957991011979 := by
        calc
          (3 : ZMod 3062202209369) ^ 382775276171 = (3 : ZMod 3062202209369) ^ (191387638085 + 191387638085 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = ((3 : ZMod 3062202209369) ^ 191387638085 * (3 : ZMod 3062202209369) ^ 191387638085) * (3 : ZMod 3062202209369) := by rw [pow_succ, pow_add]
          _ = 1957991011979 := by rw [factor_0_37]; decide
      have factor_0_39 : (3 : ZMod 3062202209369) ^ 765550552342 = 283647441283 := by
        calc
          (3 : ZMod 3062202209369) ^ 765550552342 = (3 : ZMod 3062202209369) ^ (382775276171 + 382775276171) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 382775276171 * (3 : ZMod 3062202209369) ^ 382775276171 := by rw [pow_add]
          _ = 283647441283 := by rw [factor_0_38]; decide
      have factor_0_40 : (3 : ZMod 3062202209369) ^ 1531101104684 = 3062202209368 := by
        calc
          (3 : ZMod 3062202209369) ^ 1531101104684 = (3 : ZMod 3062202209369) ^ (765550552342 + 765550552342) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 765550552342 * (3 : ZMod 3062202209369) ^ 765550552342 := by rw [pow_add]
          _ = 3062202209368 := by rw [factor_0_39]; decide
      change (3 : ZMod 3062202209369) ^ 1531101104684 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (3 : ZMod 3062202209369) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 3062202209369) ^ 2 = 9 := by
        calc
          (3 : ZMod 3062202209369) ^ 2 = (3 : ZMod 3062202209369) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 1 * (3 : ZMod 3062202209369) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 3062202209369) ^ 4 = 81 := by
        calc
          (3 : ZMod 3062202209369) ^ 4 = (3 : ZMod 3062202209369) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 2 * (3 : ZMod 3062202209369) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 3062202209369) ^ 8 = 6561 := by
        calc
          (3 : ZMod 3062202209369) ^ 8 = (3 : ZMod 3062202209369) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 3062202209369) ^ n) (by norm_num)
          _ = (3 : ZMod 3062202209369) ^ 4 * (3 : ZMod 3062202209369) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_1_2]; decide
      change (3 : ZMod 3062202209369) ^ 8 ≠ 1
      rw [factor_1_3]
      decide

#print axioms prime_lucas_3062202209369

end TotientTailPeriodKiller
end Erdos249257
