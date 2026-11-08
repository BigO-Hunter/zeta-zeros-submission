/-
Copyright (c) 2026 MultiAgency swarm. Released under Apache 2.0 license as described
in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Submission
import Submission.H269
import Submission.H269Sharp

/-!
# ReadyRaceBound — the row ready for the day the critical-line-zeros route opens

The board row for bigospeedrun.com/other/critical-line-zeros is currently CLOSED (maintainer-run
only; the verified row is Anthropic's `montgomery_taylor_simple_on_critical_line_mult_cumulative`
at `2 − 1/cMT`). The maintainer has stated that when the route opens, submissions follow the
normal rules. This module is our staged submission:

1. The COMPLETE trusted definition layer of the challenge is inlined CHARACTER-FOR-CHARACTER
   from `bigospeedrun/verifier`, `challenges/critical-line-zeros/Challenge.lean` (fetched
   2026-11-07): the `section` below reproduces its definition layer — `IsNontrivialZero`,
   `zeroMult`, `zerosIn`, `Ncount`, `Ndist`, `N0star`, `N0simple`, the Dirichlet block, and
   `cMT` — so that every auxiliary definition the comparator might diff elaborates identically.

2. `Race.ready_bound_of_le` is the DEMAND-FORM: any constant `c ≤ 2 − 1/cMT` (the challenge's
   own constant) yields the race statement at `c` in exactly the ε-shape of the challenge's
   `2 − 1/cMT` theorems:

       ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ N₀ˢ(T).

3. Two instances are staged and proved, by delegation to the axiom-clean library:
   * `Race.ready_bound_269_400` at `c = 269/400 = 0.6725`;
   * `Race.ready_bound_sharp` at `c = 3/2 − 4414041/5334191 = 7174491/10668382 ≈ 0.672500385`
     (the exact N = 4 ceiling of the rational series; strictly better than 269/400).

PASTE INSTRUCTIONS (when the route opens): the verifier already owns the definition layer —
paste only the `namespace Race` block, renaming `ready_bound_of_le` / the instance to whatever
the route's `Race.bound` convention demands, and keep the chosen instance's constant. The
delegation needs the solution side to carry `Submission/Zeta23` (Anthropic's library, Apache-2.0)
plus `Submission/H269.lean` and `Submission/H269Sharp.lean`; all reached theorems print
`[propext, Classical.choice, Quot.sound]` only. Filing steps: see scripts/route_watch.sh output
and the checklist in this file's bottom comment.
-/

/-! ## The challenge's own definition layer (verbatim from Challenge.lean) -/

section
open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

/-- ρ is a nontrivial zero of the Riemann zeta function: ζ(ρ) = 0 with 0 < Re ρ < 1 (the open
critical strip). Every zero in the strip is "nontrivial" in the usual sense (it is neither a trivial
zero −2(n+1), of real part ≤ −2, nor the pole s = 1); the converse — that every zero other than the
trivial ones lies in the open strip — is classical and is not needed to state the theorems. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ, the multiplicity of ρ: the order of vanishing of ζ at ρ, via Mathlib's `analyticOrderAt`
(ℕ∞-valued; `toNat` sends ⊤ to 0, so `1 ≤ zeroMult ρ` encodes both "ζ is not locally identically
zero at ρ" and "ρ is a zero"). -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The nontrivial zeros with ordinate in the window (T₁, T₂]: {ρ | ζ(ρ) = 0, 0 < Re ρ < 1,
T₁ < Im ρ ≤ T₂}. (Positive-ordinate window, not |Im ρ|.) -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂, counted WITH multiplicity
(`∑ᶠ` is Mathlib's finite sum; that the window contains finitely many zeros is proved on the
solution side, not assumed). -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N_d(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂, each distinct zero counted
once. -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N₀*(T₁,T₂): the number of DISTINCT zeros ON the critical line Re ρ = 1/2 with
T₁ < Im ρ ≤ T₂. This is what Theorems A and D bound from below. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- N₀ˢ(T₁,T₂): the number of SIMPLE zeros (multiplicity exactly 1) ON the critical line with
T₁ < Im ρ ≤ T₂. -/
def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

section Dirichlet

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- ρ is a nontrivial zero of L(s,χ): L(ρ,χ) = 0 with 0 < Re ρ < 1. -/
def IsNontrivialZeroL (ρ : ℂ) : Prop := χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ: the order of vanishing of L(·,χ) at ρ (via `analyticOrderAt`, as for ζ). -/
def zeroMultL (ρ : ℂ) : ℕ := (analyticOrderAt χ.LFunction ρ).toNat

/-- the nontrivial zeros of L(·,χ) with T₁ < Im ρ ≤ T₂. -/
def zerosInL (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZeroL χ ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N_χ(T₁,T₂): nontrivial zeros of L(s,χ) with T₁ < Im ρ ≤ T₂, with multiplicity. -/
def NcountL (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosInL χ T₁ T₂, zeroMultL χ ρ
/-- N_{d,χ}(T₁,T₂): distinct zeros. -/
def NdistL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂).ncard
/-- N*_{0,χ}(T₁,T₂): on the line, distinct. -/
def N0starL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard
/-- N^s_{0,χ}(T₁,T₂): on the line and simple. -/
def N0simpleL (T₁ T₂ : ℝ) : ℕ :=
  (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMultL χ ρ = 1}).ncard

end Dirichlet

/-- c₁* := √2·tan ϑ / (1 + ϑ·tan ϑ) at ϑ = 1/√2 — the paper's closed form for the optimal-window
constant c*_λ = √2·tan ϑ/(1 + ϑ·tan ϑ), ϑ = λ/√2, at λ = 1. Numerically c₁* = 0.7532960…
(= 2·tan(1/√2)/(√2 + tan(1/√2)); 1/c₁* = 1/2 + 2^{-1/2}·cot(2^{-1/2}) is the Montgomery–Taylor
constant). Theorem D's proportions here are 2 − 1/c₁* = 0.67250… (for N₀* and N₀ˢ) and
(3 − 1/c₁*)/2 = 0.83625… (for N_d); the decimals are NOT part of the formal statements. -/
def cMT : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

end
end

/-! ## Bridges: the challenge layer is our library layer, by `rfl` -/

/-- The challenge's `Ncount` IS the library's (character-identical definition layers). -/
theorem Ncount_ready_defeq :
    Ncount = BigOSpeedrun.CriticalLineZeros.Ncount := rfl

/-- Ditto for `N0simple`. -/
theorem N0simple_ready_defeq :
    N0simple = BigOSpeedrun.CriticalLineZeros.N0simple := rfl

/-- The challenge's `cMT` is `Zeta23.ThmD.cStar 1` (Anthropic's division-safe constant at λ = 1). -/
theorem cMT_ready_eq_cStar_one : cMT = Zeta23.ThmD.cStar 1 := by
  rw [BigOSpeedrun.CriticalLineZeros.H269.cStar_one_eq_cMT]
  rfl

/-! ## The delegation and the ready rows -/

/-- The Anthropic Theorem D result — `montgomery_taylor_simple_on_critical_line_mult_cumulative`,
at `HD 1 = 2 − 1/cMT`, simple zeros, cumulative windows, with multiplicity — transferred to the
challenge's own inlined definitions. -/
theorem ready_thmD :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.ThmD.thmD₀_simple_mult_cumulative ε hε
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- **The demand-form of any rational row**: `c ≤ 2 − 1/cMT` (the challenge's own constant)
yields the race statement at `c`, in exactly the ε-shape of the challenge's
`montgomery_taylor_*_cumulative` theorems. -/
theorem ready_bound_of_le {c : ℝ} (hc : c ≤ 2 - 1 / cMT) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := ready_thmD ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0:ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  have hHD : Zeta23.ThmD.HD 1 = 2 - 1 / cMT := by
    show 2 - 1 / Zeta23.ThmD.cStar 1 = 2 - 1 / cMT
    rw [cMT_ready_eq_cStar_one]
  have hle : (c - ε) ≤ (Zeta23.ThmD.HD 1 - ε) := by linarith [hc, hHD]
  have hmul := mul_le_mul_of_nonneg_right hle hN
  linarith [hT₀ T hT, hmul]

/-- **Ready row 1**: `κ* ≥ 269/400 = 0.6725`. -/
theorem ready_bound_269_400 :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((269:ℝ)/400 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  ready_bound_of_le BigOSpeedrun.CriticalLineZeros.H269.two_sub_one_div_cMT_ge

/-- **Ready row 2 (sharper)**: `κ* ≥ 3/2 − 4414041/5334191 = 7174491/10668382 ≈ 0.672500385`,
the exact N = 4 ceiling of our rational-series machinery (strictly above 269/400, strictly
below H = 0.67250070…). -/
theorem ready_bound_sharp :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3:ℝ)/2 - 4414041/5334191 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  refine ready_bound_of_le ?_
  have hHD : Zeta23.ThmD.HD 1 = 2 - 1 / cMT := by
    show 2 - 1 / Zeta23.ThmD.cStar 1 = 2 - 1 / cMT
    rw [cMT_ready_eq_cStar_one]
  linarith [BigOSpeedrun.CriticalLineZeros.H269Sharp.h_ge_sharp,
    BigOSpeedrun.CriticalLineZeros.H_eq_HD, hHD]

/-! ## Filing checklist for the moment the route opens (do not post before then)

1. `bash scripts/route_watch.sh` — confirm a TRIGGER line (board announcement or challenges/
   addition) and read the maintainer's exact demand (parameter form, toolchain pin).
2. Choose the constant: `269/400` (small denominator, clean) or the sharper
   `3/2 − 4414041/5334191 ≈ 0.672500385`. Both are proven; file the one the route's format wants.
3. Submit: solution module = this file's `namespace Race` block (renamed to the route's
   `Race.bound` convention) delegating to the Zeta23 library + H269/H269Sharp; the challenge
   side keeps its own definition layer (already identical to the inlined block above).
4. Re-run the axiom audit: every reached theorem must print only
   `[propext, Classical.choice, Quot.sound]` — verified today for both rows.
5. Our `Race.bound` at exact `H` (Submission.lean) stays staged as the maintainer-row match;
   `673/1000 = 0.673 > H` is NOT filable by this machinery (ceiling note in H269Sharp.lean).
-/

#print axioms ready_bound_of_le
#print axioms ready_bound_269_400
#print axioms ready_bound_sharp
#print axioms ready_thmD
