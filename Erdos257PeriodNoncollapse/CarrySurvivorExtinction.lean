import Erdos257PeriodNoncollapse.TotientTailPeriodKiller

/-!
# Wave 22: carry-survivor extinction and the multiple-period collapse

Wave 21 reduced #249 to a certified kill supply: for every period `h ≥ 1` and
every threshold `N₀`, some `(N ≥ N₀, L)` with the endpoint residue certificate
`certifiedKill h N L`.  This file spends two further consequences of
rationality that the wave-21 socket left on the table.

**1. The multiple-period collapse.**  If `h₀` is an eventual binary period,
every multiple `m·h₀` is too, by pure telescoping:

  `D_{m·h}(N) = ∑_{i<m} D_h(N + i·h)`,   `D_h(N) = R_{N+h} - R_N`.

So the supply obligation weakens from *kill every `h`* to *kill one multiple
per divisibility ray* (`irrational_totient_series_of_multiple_survivor_supply`)
— and further collapses onto the ONE-PARAMETER family `lcm(1..t)`, since every
`h₀ ≤ t` divides `lcm(1..t)`
(`irrational_totient_series_of_lcm_survivor_supply`).  The throat of #249
narrows from a ∀h family of targets to a single ℕ-indexed ray.

**2. The carry-survivor certificate.**  The wave-21 note called the
bounded-orbit reformulation advisory.  Here it is machine-checked: doubling
the tail shifts the window by one and expels the head totient
(`totientTail_succ`), so an integer tail difference `d = D_h(N)` launches the
exact integer orbit

  `orbit 0 = d`,  `orbit (i+1) = 2·orbit i - (φ(N+i+1+h) - φ(N+i+1))`,

which tracks `D_h(N+i)` forever (`carryOrbit_eq_tail_diff`) and is therefore
trapped in the strip `|·| < N+i+h+2` (`abs_tail_diff_lt`).  The certificate
`survivorKill h N K` checks — finitely, decidably — that every integer
candidate in the initial box escapes the strip within `K` steps; soundness is
`tail_diff_notMem_int_of_survivorKill`.  The survivor predicate is strictly
stronger than the endpoint certificate at equal depth
(`survivor_strict_at_equal_budget`, a `decide` witness at `(1, 57, 8)`), but
the wave-22 probe measures the two families as near-equivalent in minimal
kill depth — the deepest scale dominates.  The probe's honest summary: the
multiple-period loosening is the logical gain; the survivor form is the
bounded-orbit lane made kernel-checkable.

**Deposits.**  `certifiedKill_all_upto_sixteen` machine-checks kills for every
`h ≤ 16` at `(N, L) = (14, 9)` — twice the wave-21 period range in a smaller
window — giving the extended exclusion
`totient_series_ne_rat_of_den_dvd_upto_sixteen`: `S` is no rational whose
denominator divides `2¹⁴·(2ʰ-1)` for any `h ≤ 16`.

Everything remains elementary: `φ(n) ≤ n`, geometric tails, integer orbit
arithmetic.  No q-Padé, no Stern–Brocot, no unformalised citations.
-/

set_option maxRecDepth 10000

namespace Erdos257PeriodNoncollapse
namespace TotientTailPeriodKiller

open Finset

/-! ## Tail bounds: the strip that traps every integer carry orbit -/

/-- The local totient tail is strictly positive. -/
lemma totientTail_pos (M : ℕ) : 0 < totientTail M := by
  have hle : (Nat.totient (M + 1 + 0) : ℝ) / 2 ^ (0 + 1) ≤ totientTail M :=
    (summable_totientTail_terms M).le_tsum 0 fun j _ => by positivity
  have h1 : 0 < Nat.totient (M + 1 + 0) := Nat.totient_pos.mpr (by omega)
  have h1' : (0 : ℝ) < (Nat.totient (M + 1 + 0) : ℝ) := by exact_mod_cast h1
  have hpos : (0 : ℝ) < (Nat.totient (M + 1 + 0) : ℝ) / 2 ^ (0 + 1) := by positivity
  linarith

/-- `R_M ≤ M + 2`: the window bound at depth `0`. -/
lemma totientTail_le (M : ℕ) : totientTail M ≤ (M : ℝ) + 2 := by
  have h := tail_after_le M 0
  simp only [add_zero, pow_zero, Nat.cast_zero, div_one] at h
  exact h

/-- The tail difference `D_h(N) = R_{N+h} - R_N` is trapped in the open strip
`|D_h(N)| < N + h + 2`. -/
lemma abs_tail_diff_lt (h N : ℕ) :
    |totientTail (N + h) - totientTail N| < (N : ℝ) + h + 2 := by
  have h1 := totientTail_pos (N + h)
  have h2 := totientTail_pos N
  have h3 := totientTail_le (N + h)
  have h4 := totientTail_le N
  push_cast at h3
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  rw [abs_lt]
  constructor <;> linarith

/-! ## The carry recurrence -/

/-- **Carry recurrence.**  `R_{M+1} = 2·R_M - φ(M+1)`: doubling the tail shifts
the window by one and expels the head totient. -/
lemma totientTail_succ (M : ℕ) :
    totientTail (M + 1) = 2 * totientTail M - (Nat.totient (M + 1) : ℝ) := by
  have hsum := summable_totientTail_terms M
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hhead : ∑ j ∈ Finset.range 1, (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1)
      = (Nat.totient (M + 1) : ℝ) / 2 := by
    rw [Finset.sum_range_one]
    norm_num
  have htail : ∑' j : ℕ, (Nat.totient (M + 1 + (j + 1)) : ℝ) / 2 ^ ((j + 1) + 1)
      = totientTail (M + 1) / 2 := by
    unfold totientTail
    rw [← tsum_div_const]
    exact tsum_congr fun j => by
      rw [show M + 1 + (j + 1) = M + 1 + 1 + j from by omega, div_div, ← pow_succ]
  have hkey : (Nat.totient (M + 1) : ℝ) / 2 + totientTail (M + 1) / 2 = totientTail M := by
    calc (Nat.totient (M + 1) : ℝ) / 2 + totientTail (M + 1) / 2
        = (∑ j ∈ Finset.range 1, (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1))
          + ∑' j : ℕ, (Nat.totient (M + 1 + (j + 1)) : ℝ) / 2 ^ ((j + 1) + 1) := by
          rw [hhead, htail]
      _ = totientTail M := hsplit
  linarith

/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. -/
def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

/-- The tail difference obeys the exact carry recurrence
`D_h(M+1) = 2·D_h(M) - a_{M+1}`. -/
lemma tail_diff_succ (h M : ℕ) :
    totientTail (M + 1 + h) - totientTail (M + 1)
      = 2 * (totientTail (M + h) - totientTail M) - (deltaTotient h (M + 1) : ℝ) := by
  have e1 := totientTail_succ (M + h)
  have e2 := totientTail_succ M
  rw [show M + 1 + h = M + h + 1 from by omega, e1, e2]
  unfold deltaTotient
  push_cast
  rw [show M + 1 + h = M + h + 1 from by omega]
  ring

/-! ## The integer carry orbit and the survivor certificate -/

/-- The integer carry orbit launched from candidate `d` at position `N`:
`orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`.  If `D_h(N)` is the
integer `d`, this orbit equals `D_h(N+i)` forever. -/
def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)

/-- **Orbit tracking.**  If the tail difference at `N` is the integer `d`, the
carry orbit computes the exact tail-difference sequence: `orbit i = D_h(N+i)`. -/
lemma carryOrbit_eq_tail_diff {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N d i : ℝ) = totientTail (N + i + h) - totientTail (N + i) := by
  induction i with
  | zero => simpa using hd
  | succ i ih =>
      have hrec := tail_diff_succ h (N + i)
      have hstep : carryOrbit h N d (i + 1)
          = 2 * carryOrbit h N d i - deltaTotient h (N + i + 1) := rfl
      rw [hstep]
      push_cast
      rw [ih, show N + (i + 1) + h = N + i + 1 + h from by omega,
        show N + (i + 1) = N + i + 1 from by omega, hrec]

/-- The **carry-survivor certificate**: every integer candidate in the initial
box `|d| ≤ N+h+1` — enumerated as `d = j - (N+h+1)` for `j < 2·(N+h+1)+1` —
provably escapes the strip `|·| ≤ N+i+h+1` within `K` steps (escape stated as
a two-sided disjunction).  Finitely many candidates, finitely many steps:
decidable. -/
def survivorKill (h N K : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (N + h + 1) + 1),
    ∃ i ∈ Finset.range (K + 1),
      carryOrbit h N ((j : ℤ) - (N + h + 1)) i ≤ -(N + i + h + 2 : ℤ)
        ∨ (N + i + h + 2 : ℤ) ≤ carryOrbit h N ((j : ℤ) - (N + h + 1)) i

instance (h N K : ℕ) : Decidable (survivorKill h N K) := by
  unfold survivorKill
  infer_instance

/-- **Survivor soundness.**  A survivor kill proves the tail difference is not
an integer: an integer value `d` would launch an integer carry orbit equal to
the true tail-difference sequence, which stays inside the strip
`|D_h(N+i)| < N+i+h+2` forever — but the certificate says every candidate
provably escapes within `K` steps.  This is the machine-checked form of the
wave-21 bounded-orbit reformulation. -/
theorem tail_diff_notMem_int_of_survivorKill {h N K : ℕ} (hkill : survivorKill h N K) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  have hboxR : |(d : ℝ)| < (N : ℝ) + h + 2 := by
    rw [hd]
    exact abs_tail_diff_lt h N
  have habs : |d| < (N : ℤ) + h + 2 := by exact_mod_cast hboxR
  have hlohi := abs_lt.mp habs
  have hmem : (d + ((N : ℤ) + h + 1)).toNat ∈ Finset.range (2 * (N + h + 1) + 1) := by
    rw [Finset.mem_range]
    omega
  obtain ⟨i, _, hesc⟩ := hkill (d + ((N : ℤ) + h + 1)).toNat hmem
  have hcand : (((d + ((N : ℤ) + h + 1)).toNat : ℤ)) - ((N : ℤ) + h + 1) = d := by omega
  rw [hcand] at hesc
  have htrack := carryOrbit_eq_tail_diff hd i
  have hstrip := abs_tail_diff_lt h (N + i)
  push_cast at hstrip
  rw [abs_lt] at hstrip
  rcases hesc with hlo | hhi
  · have hR : (carryOrbit h N d i : ℝ) ≤ -((N : ℝ) + i + h + 2) := by exact_mod_cast hlo
    rw [htrack] at hR
    linarith [hstrip.1]
  · have hR : ((N : ℝ) + i + h + 2) ≤ (carryOrbit h N d i : ℝ) := by exact_mod_cast hhi
    rw [htrack] at hR
    linarith [hstrip.2]

/-! ## The multiple-period collapse -/

/-- **Period-ray telescoping.**  The `m·h` tail difference is the sum of `m`
translated `h` tail differences: integrality flows down every multiple. -/
lemma tail_diff_mul (h N m : ℕ) :
    totientTail (N + m * h) - totientTail N
      = ∑ i ∈ Finset.range m,
          (totientTail (N + i * h + h) - totientTail (N + i * h)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih,
        show N + (m + 1) * h = N + m * h + h from by rw [Nat.succ_mul]; omega]
      ring

/-- Integrality propagates down every period ray: if every `h`-difference from
`N₀` on is an integer, so is every `m·h`-difference. -/
lemma tail_diff_mul_mem_int {h N₀ : ℕ}
    (hint : ∀ N, N₀ ≤ N → totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (m N : ℕ) (hN : N₀ ≤ N) :
    totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := hint (N + m * h) (hN.trans (Nat.le_add_right _ _))
      refine ⟨b + a, ?_⟩
      rw [show N + (m + 1) * h = N + m * h + h from by rw [Nat.succ_mul]; omega]
      push_cast
      rw [ha, hb]
      ring

/-- **The wave-22 reduction: multiple-period survivor supply.**  The weakest
supply hypothesis in the ladder so far: for every primitive period `h₀` it
suffices to certify a survivor kill along ANY multiple `m·h₀`, at arbitrarily
large `N`.  Rationality forces integrality along the whole period ray, so one
dead multiple kills the primitive. -/
theorem irrational_totient_series_of_multiple_survivor_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (m * h₀) N K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨m, _, N, hN, K, hkill⟩ := hsupply h hpos N₀
  exact tail_diff_notMem_int_of_survivorKill hkill (tail_diff_mul_mem_int hint m N hN)

/-- The endpoint-certificate variant of the multiple-period reduction: one
certified window kill along any multiple of each primitive period suffices. -/
theorem irrational_totient_series_of_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨m, _, N, hN, L, hkill⟩ := hsupply h hpos N₀
  exact tail_diff_notMem_int_of_certifiedKill hkill (tail_diff_mul_mem_int hint m N hN)

/-! ## The one-parameter collapse: `lcm(1..t)` is a universal period ray -/

/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`.  Every
primitive period `h₀ ≤ t` divides it. -/
def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

lemma periodLcm_pos (t : ℕ) : 0 < periodLcm t := by
  induction t with
  | zero => exact Nat.one_pos
  | succ t ih =>
      exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero ih.ne' (Nat.succ_ne_zero t))

lemma dvd_periodLcm {h t : ℕ} (h1 : 1 ≤ h) (ht : h ≤ t) : h ∣ periodLcm t := by
  induction t with
  | zero => omega
  | succ t ih =>
      show h ∣ Nat.lcm (periodLcm t) (t + 1)
      rcases Nat.lt_or_ge h (t + 1) with hlt | hge
      · exact dvd_trans (ih (by omega)) (Nat.dvd_lcm_left _ _)
      · have heq : h = t + 1 := by omega
        subst heq
        exact Nat.dvd_lcm_right _ _

/-- **One-parameter collapse of the throat.**  Survivor kills along the single
family `lcm(1..t)` — arbitrarily large `t`, arbitrarily large `N` — prove #249.
Rationality would give SOME period `h₀`; every `h₀ ≤ t` divides `lcm(1..t)`,
so the whole `∀ h₀` obligation lands on one ℕ-indexed ray. -/
theorem irrational_totient_series_of_lcm_survivor_supply
    (hsupply : ∀ t₀ N₀ : ℕ,
      ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (periodLcm t) N K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_multiple_survivor_supply fun h₀ hpos N₀ => ?_
  obtain ⟨t, ht, N, hN, K, hkill⟩ := hsupply h₀ N₀
  have hdvd : h₀ ∣ periodLcm t := dvd_periodLcm hpos ht
  refine ⟨periodLcm t / h₀,
    Nat.div_pos (Nat.le_of_dvd (periodLcm_pos t) hdvd) hpos, N, hN, K, ?_⟩
  rwa [Nat.div_mul_cancel hdvd]

/-! ## Unconditional deposits (kernel-decided) -/

/-- Machine-checked survivor kill: period `1` dies at `N = 12` within `K = 7`
steps — every integer candidate in `|d| ≤ 14` escapes the strip. -/
theorem survivorKill_example : survivorKill 1 12 7 := by decide

/-- Period `1` has no integer tail difference at `N = 12` — re-derived through
the orbit certificate rather than the endpoint residue. -/
theorem tail_diff_not_int_survivor_example :
    totientTail (12 + 1) - totientTail 12 ∉ Set.range ((↑) : ℤ → ℝ) :=
  tail_diff_notMem_int_of_survivorKill survivorKill_example

/-- The survivor certificate is STRICTLY stronger than the endpoint certificate
at equal depth budget: at `(h, N) = (1, 57)` the survivor interval dies at
`K = 8` while every endpoint window `L ≤ 8` fails.  (The wave-22 probe measures
the two families as near-equivalent in minimal kill depth — this witness pins
down exactly the strictness that remains.) -/
theorem survivor_strict_at_equal_budget :
    survivorKill 1 57 8 ∧ ∀ L ∈ Finset.Icc 1 8, ¬ certifiedKill 1 57 L := by decide

/-- Extended endpoint deposit: every period `h ≤ 16` is certified dead at
`(N, L) = (14, 9)` — twice the wave-21 period range in a smaller window than
its `(12, 16)`. -/
theorem certifiedKill_all_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 := by decide

/-- No shifted tail difference with period `h ≤ 16` is an integer at `N = 14`. -/
theorem tail_diff_not_int_upto_sixteen (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16) :
    totientTail (14 + h) - totientTail 14 ∉ Set.range ((↑) : ℤ → ℝ) :=
  tail_diff_notMem_int_of_certifiedKill
    (certifiedKill_all_upto_sixteen h (Finset.mem_Icc.mpr ⟨h1, h16⟩))

/-- **Extended denominator exclusion.**  The totient series equals no rational
whose denominator divides `2¹⁴·(2ʰ-1)` for some `1 ≤ h ≤ 16`: no dyadic
rational with denominator up to `2¹⁴`, and no odd part whose multiplicative
order of `2` is at most `16`.  Subsumes the wave-21 lattice on both axes. -/
theorem totient_series_ne_rat_of_den_dvd_upto_sixteen (r : ℚ) (h : ℕ)
    (h1 : 1 ≤ h) (h16 : h ≤ 16) (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := fun hS =>
  tail_diff_not_int_upto_sixteen h h1 h16 (tail_diff_int_of_den_dvd r hS h 14 hdvd)

end TotientTailPeriodKiller
end Erdos257PeriodNoncollapse
