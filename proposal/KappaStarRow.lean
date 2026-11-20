import Mathlib

/-!
Trusted target for the Big O Speedrun zeta zeros race,
https://bigospeedrun.com/other/critical-line-zeros.

This file is the proposed verifier challenge statement (the analogue of
`challenges/directed-sssp/CHDRow.lean`). It imports only Mathlib and
assumes no estimate, hypothesis, or proof of any bound (in particular it
does not assume RH).

Race statement (from the board): the nontrivial zeros of ζ are its zeros ρ
with 0 < Re ρ < 1; the critical line is Re s = 1/2; a zero of multiplicity
m counts m times; N(T) is the number of nontrivial zeros with
0 < Im ρ ≤ T; N₀ˢ(T) is the number of those that are simple (multiplicity
exactly 1) and on the critical line; and
κ* = liminf_{T→∞} N₀ˢ(T)/N(T). A result is κ* ≥ c, unconditional,
higher c is better. This file fixes c = H := 3/2 − cot(1/√2)/√2
≈ 0.6725007, the Montgomery–Taylor constant, and states κ* ≥ H in the
equivalent ε-form. Because H is irrational, the constant is pinned in this
trusted file rather than passed as a rational parameter (policy question
for the maintainer; see PROPOSAL.md).

The counting definitions are taken, with negligible adaptation, from
Anthropic's trusted `ChallengeDeps.lean` / `Challenge.lean` in
anthropics/formal-math (folder zeta23, Apache-2.0), so that the submitted
proof can reuse Anthropic's library with a minimal adapter. Definition
credits: Anthropic (Claude), Levent Alpöge, Ralph Furman. Proof credit:
same. Verification and submission packaging: MultiAgency swarm.

The expected solution is a delegation to
`Zeta23.ThmD.thmD₀_simple_mult_cumulative` (statement
`montgomery_taylor_simple_on_critical_line_mult_cumulative` in
zeta23/Challenge.lean), after the one-line algebraic identification
H = 2 − 1/cMT, cMT = √2·tan ϑ/(1+ϑ·tan ϑ), ϑ = 1/√2 (cot x = 1/tan x).
-/

namespace BigOSpeedrun.CriticalLineZeros

open scoped BigOperators

noncomputable section

/-- ρ is a nontrivial zero of the Riemann zeta function: ζ(ρ) = 0 with
0 < Re ρ < 1 (the board defines "nontrivial zero" exactly as a zero in the
open critical strip). -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ, the multiplicity of ρ: the order of vanishing of ζ at ρ, via
Mathlib's `analyticOrderAt` (ℕ∞-valued; `toNat` sends ⊤ to 0, so
`1 ≤ zeroMult ρ` encodes both "ζ is not locally identically zero at ρ" and
"ρ is a zero"). A simple zero is one with `zeroMult ρ = 1`. -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The nontrivial zeros with ordinate in the window (T₁, T₂]:
{ρ | ζ(ρ) = 0, 0 < Re ρ < 1, T₁ < Im ρ ≤ T₂}. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂, counted
WITH multiplicity (`∑ᶠ` is Mathlib's finite sum; that the window contains
finitely many zeros is proved on the solution side, not assumed). -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N₀ˢ(T₁,T₂): the number of SIMPLE zeros (multiplicity exactly 1) ON the
critical line Re ρ = 1/2 with T₁ < Im ρ ≤ T₂. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-- The race constant H = 3/2 − cot(1/√2)/√2 ≈ 0.6725007 (the
Montgomery–Taylor constant), written as 3/2 − 1/(√2·tan(1/√2)) since
cot x = 1/tan x. This equals 2 − 1/cMT for
cMT = √2·tan ϑ/(1 + ϑ·tan ϑ) at ϑ = 1/√2, Anthropic's closed form. -/
def H : ℝ := 3 / 2 - 1 / (Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

/-- κ* ≥ H in the ε-form of liminf: for every ε > 0, for all sufficiently
large T, (H − ε)·N(T) ≤ N₀ˢ(T), with N(T) = Ncount 0 T (window (0, T],
multiplicity counted) and N₀ˢ(T) = N0simple 0 T. Unconditional: no
hypotheses. -/
theorem Race.bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (H - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry

end

-- Big O Speedrun zeta zeros target; exact constant fixed in this file.
-- Board: κ* = liminf N₀ˢ(T)/N(T) ≥ 3/2 − cot(1/√2)/√2 = 0.6725007…
