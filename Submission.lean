import Submission.KappaStarRow
import Submission.Zeta23.ThmD.Mult

/-!
Draft critical-line-zeros submission: the root `Race.bound` expected by the
verifier, proved by Anthropic's Theorem D (simple, cumulative, with multiplicity).
`Submission/KappaStarRow.lean` is the proposed trusted definition surface with
its deliberately unproved challenge theorem removed.
-/

namespace BigOSpeedrun.CriticalLineZeros

noncomputable section

/-- Anthropic's division-safe constant at λ = 1, in the paper's tangent form. -/
theorem cStar_one_eq_closed :
    Zeta23.ThmD.cStar 1 =
      Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
        (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2)) := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold Zeta23.ThmD.theta
  rfl

/-- Exact adapter: `H = 3/2 - cot(1/√2)/√2 = 2 - 1/cStar 1`. -/
theorem H_eq_HD : H = Zeta23.ThmD.HD 1 := by
  rw [Zeta23.ThmD.HD, cStar_one_eq_closed]
  unfold H
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs1 : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  have hθ0 : 0 < 1 / Real.sqrt 2 := by positivity
  have hθπ : 1 / Real.sqrt 2 < Real.pi / 2 := by
    have hθ1 : 1 / Real.sqrt 2 ≤ 1 := (div_le_one hs).2 hs1
    linarith [Real.pi_gt_three]
  have ht : 0 < Real.tan (1 / Real.sqrt 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθπ
  have hden : 0 < 1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) := by positivity
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt hs
  have ht0 : Real.tan (1 / Real.sqrt 2) ≠ 0 := ne_of_gt ht
  have hden0 : 1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) ≠ 0 := ne_of_gt hden
  field_simp [hs0, ht0, hden0]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

end

end BigOSpeedrun.CriticalLineZeros

open BigOSpeedrun.CriticalLineZeros

/-- κ* ≥ H, the exact Montgomery–Taylor bound, with no hypotheses. -/
theorem Race.bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (H - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  have h := @Zeta23.ThmD.thmD₀_simple_mult_cumulative
  rw [H_eq_HD]
  exact h
