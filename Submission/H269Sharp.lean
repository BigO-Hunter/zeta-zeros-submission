/-
Copyright (c) 2026 MultiAgency swarm. Released under Apache 2.0 license as described
in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Submission
import Submission.H269

/-!
# The sharpened rational row: `κ* ≥ 3/2 − 4414041/5334191 = 7174491/10668382 ≈ 0.672500385`

`H269.lean` certifies `s := u·tan u ≥ 200/331` via `400·cos u ≤ 331·(sin u/u)`, whose exact
`N = 4` margin is `821/5806080`. That margin is slack: the largest rational the SAME `N = 4`
plugs certify for `tan u/u` is

    tan u/u ≥ A_low / B_up = 5334191 / 4414041

where `A_low = 37043/40320 − 1/5806080` (sin-series lower plug) and
`B_up = 4379/5760 + 1/645120` (cos-series upper plug), with `p·B_up = q·A_low` holding with
EQUALITY — the certification is exact, no arithmetic is thrown away. This lifts the row from

    269/400            = 0.6725
    3/2 − 4414041/5334191 = 7174491/10668382 ≈ 0.6725003848   (gain 3.85·10⁻⁷)

while staying below `H = 0.67250070…` (the method's ceiling; see the ceiling note in
PROGRESS/commit history: `673/1000 = 0.673 > H` is NOT reachable by this machinery, and the
claimed leader 0.673113 exceeds H — beating it needs mathematics beyond the Montgomery–Taylor
λ = 1 window, not better rational packaging).

Method ceiling, for the record: as the series cut N grows the plugs tighten (cos tail:
1.6·10⁻⁶ at N = 4, 8.6·10⁻⁹ at N = 5, 3.3·10⁻¹¹ at N = 6), so the certified threshold
`A_low/B_up → tan u/u` and the row `c → 3/2 − 1/(2s) = H` from below, identically. E.g. the
denominator-10⁷ rational `6725007/10⁷ = 0.6725007 < H` becomes certifiable around N = 6
(it is NOT certifiable at N = 4: it needs `tan u/u ≥ 1.20846035` but N = 4 only reaches
`1.20845978`). No rational of this chain can ever exceed H.
-/

noncomputable section

namespace BigOSpeedrun.CriticalLineZeros
namespace H269Sharp

/-- The exact `N = 4` certification of `5334191·B ≤ 4414041·A`: `p·B_up = q·A_low` (equality —
the choice `p/q = A_low/B_up` leaves no slack on the table). -/
theorem margin_sharp :
    (5334191:ℝ) * (4379 / 5760 + 1 / 645120)
      = 4414041 * (37043 / 40320 - 1 / 5806080) := by
  norm_num

/-- **The sharp target inequality** `5334191·cos u ≤ 4414041·(sin u / u)`. -/
theorem key_ineq_sharp :
    (5334191:ℝ) * Real.cos H269.u ≤ 4414041 * (Real.sin H269.u / H269.u) := by
  have hA : 37043 / 40320 - 1 / 5806080 ≤ Real.sin H269.u / H269.u :=
    by linarith [(abs_le.1 H269.A_bound_N4).1]
  have hB : Real.cos H269.u ≤ 4379 / 5760 + 1 / 645120 :=
    by linarith [(abs_le.1 H269.cos_bound_N4).2]
  nlinarith [hA, hB, margin_sharp]

/-- **Step (c), sharpened**: `s = u·tan u ≥ 5334191/8828082`, from `key_ineq_sharp`. -/
theorem s_ge_sharp : H269.sval ≥ (5334191:ℝ) / (2 * 4414041) := by
  have hu0 : H269.u ≠ 0 := ne_of_gt H269.u_pos
  have hsin : H269.u * (Real.sin H269.u / H269.u) = Real.sin H269.u := by field_simp
  have hmul1 : (5334191:ℝ) * (H269.u * Real.cos H269.u) ≤ 4414041 * Real.sin H269.u := by
    have hm : H269.u * (5334191 * Real.cos H269.u)
        ≤ H269.u * (4414041 * (Real.sin H269.u / H269.u)) :=
      mul_le_mul_of_nonneg_left key_ineq_sharp (le_of_lt H269.u_pos)
    calc (5334191:ℝ) * (H269.u * Real.cos H269.u)
        = H269.u * (5334191 * Real.cos H269.u) := by ring
      _ ≤ H269.u * (4414041 * (Real.sin H269.u / H269.u)) := hm
      _ = 4414041 * (H269.u * (Real.sin H269.u / H269.u)) := by ring
      _ = 4414041 * Real.sin H269.u := by rw [hsin]
  have hmul2 : (5334191:ℝ) / 2 * Real.cos H269.u ≤ 4414041 * H269.sval * Real.cos H269.u := by
    have hm : H269.u * (5334191 * (H269.u * Real.cos H269.u))
        ≤ H269.u * (4414041 * Real.sin H269.u) :=
      mul_le_mul_of_nonneg_left hmul1 (le_of_lt H269.u_pos)
    calc (5334191:ℝ) / 2 * Real.cos H269.u
        = 5334191 * H269.u ^ 2 * Real.cos H269.u := by rw [H269.u_sq]; norm_num
      _ = H269.u * (5334191 * (H269.u * Real.cos H269.u)) := by ring
      _ ≤ H269.u * (4414041 * Real.sin H269.u) := hm
      _ = 4414041 * (H269.sval * Real.cos H269.u) := by rw [H269.sval_cos]; ring
      _ = 4414041 * H269.sval * Real.cos H269.u := by ring
  have h3 : (5334191:ℝ) / 2 ≤ 4414041 * H269.sval :=
    le_of_mul_le_mul_right hmul2 H269.cos_pos
  linarith

/-- `1/(2s) ≤ 4414041/5334191` — the reciprocal form. -/
theorem inv_two_sval_le_sharp : 1 / (2 * H269.sval) ≤ 4414041 / 5334191 := by
  have hs2 : (5334191:ℝ) / 4414041 ≤ 2 * H269.sval := by linarith [s_ge_sharp]
  have hpos : (0:ℝ) < 2 * H269.sval := by linarith [s_ge_sharp]
  have hmul : (1:ℝ) ≤ (4414041 / 5334191) * (2 * H269.sval) := by
    have hm := mul_le_mul_of_nonneg_left hs2 (by norm_num : (0:ℝ) ≤ 4414041 / 5334191)
    have hone : (4414041 / 5334191:ℝ) * (5334191 / 4414041) = 1 := by field_simp
    linarith [hm, hone]
  rw [div_le_iff₀ hpos]
  linarith

/-- **The sharpened board bound**: `3/2 − 4414041/5334191 = 7174491/10668382 ≈ 0.672500385 ≤ H`. -/
theorem h_ge_sharp : ((3:ℝ)/2 - 4414041/5334191 : ℝ) ≤ H := by
  rw [H269.H_eq_two_sub]
  linarith [inv_two_sval_le_sharp]

end H269Sharp

end BigOSpeedrun.CriticalLineZeros

open BigOSpeedrun.CriticalLineZeros

namespace Race

/-- **The sharpened rational row**: κ* ≥ 3/2 − 4414041/5334191 = 7174491/10668382
≈ 0.672500385, strictly above 269/400 = 0.6725 and strictly below H. -/
theorem bound_sharp :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((3:ℝ)/2 - 4414041/5334191 - ε) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := bound ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0:ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  have hle : ((3:ℝ)/2 - 4414041/5334191 : ℝ) - ε ≤ H - ε := by
    linarith [H269Sharp.h_ge_sharp]
  have hmul := mul_le_mul_of_nonneg_right hle hN
  linarith [hT₀ T hT, hmul]

/-- The sharpened constant is strictly better than `269/400`. -/
example : ((269:ℝ)/400 : ℝ) < (3:ℝ)/2 - 4414041/5334191 := by norm_num

#print axioms Race.bound_sharp
#print axioms H269Sharp.h_ge_sharp

end Race
