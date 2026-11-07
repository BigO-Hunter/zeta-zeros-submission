/-
Copyright (c) 2026 MultiAgency swarm. Released under Apache 2.0 license as described
in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Submission
import Submission.H269

/-!
# The board row at the rational constant `269/400`

`Race.bound` (in `Submission.lean`) is the race statement at this package's `H`, in the
eventual multiplied ε-form

    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ N₀ˢ(T).

`Submission/H269.lean` proves `269/400 ≤ H`. This file composes the two: the same ε works
unchanged (the multipliers are compared pointwise against `N(T) ≥ 0`), giving the row at
the exact rational `269/400 = 0.6725`:

    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (269/400 − ε)·N(T) ≤ N₀ˢ(T).

`h_ge_269_400_via_HD` re-derives `269/400 ≤ H` through `H_eq_HD` and the Montgomery–Taylor
form `HD 1 = 2 − 1/cStar 1 ≥ 269/400`, as an independent cross-check of the adapter.
-/
noncomputable section

open BigOSpeedrun.CriticalLineZeros

namespace Race

/-- **The board row at `269/400`**, in the ε-form of `Race.bound`. -/
theorem bound_269_400 :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((269 : ℝ) / 400 - ε) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := bound ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0 : ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  have hle : (269 : ℝ) / 400 - ε ≤ H - ε := by
    have h := H269.h_ge_269_400
    linarith
  have hmul := mul_le_mul_of_nonneg_right hle hN
  linarith [hT₀ T hT]

/-- `269/400 ≤ H` again, this time through the adapter identity `H = HD 1` and the
Montgomery–Taylor form `HD 1 ≥ 269/400`. -/
theorem h_ge_269_400_via_HD : (269 : ℝ) / 400 ≤ H := by
  rw [H_eq_HD]
  exact H269.hD_one_ge

#print axioms bound_269_400
#print axioms h_ge_269_400_via_HD

end Race
