/-
Copyright (c) 2026 MultiAgency swarm. Released under Apache 2.0 license as described
in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Submission.KappaStarRow
import Submission.Zeta23.ThmD.Functional

/-!
# H269: the board constant `H` bounded below by the exact rational `269/400`

This file proves, inside this package's own formulation of the race constant
(`BigOSpeedrun.CriticalLineZeros.H`, `Submission/KappaStarRow.lean`):

    H = 3/2 − 1/(√2·tan(1/√2)) ≥ 269/400        (H ≈ 0.6725007, margin 7.04e-7)

together with the Montgomery–Taylor forms it is equivalent to
(`cStar 1 ≥ 400/531`, `1/cStar 1 ≤ 531/400`, `HD 1 ≥ 269/400`).

## The reduction

`u = 1/√2` makes `u² = 1/2` exact, so `sin u = u·A` and `cos u = B` where `A` and `B`
are pure rational alternating series ((1/2)^k/(2k+1)! and (1/2)^k/(2k)!). Everything
below is exact:

    331·A ≥ 400·B  ⟹  s = u·tan u ≥ 200/331  ⟹  H = 3/2 − 1/(2s) ≥ 269/400
                                              ⟹  cStar 1 = 2s/(1+s) ≥ 400/531

The only analytic inputs are Mathlib's Leibniz alternating-series bounds at N = 4 terms:

    |sin u / u − 37043/40320| ≤ 1/5806080        (A bound)
    |cos u     − 4379/5760 | ≤ 1/645120          (B bound)

and they enter with the exact margin
`331·(A_part − A_err) − 400·(B_part + B_err) = 821/5806080 > 0`. Everything else is
field algebra plus `norm_num`; no `sorry`, no `native_decide`, no new axioms.

Provenance: the κ* ≥ H mathematics is Anthropic's (Levent Alpöge, Ralph Furman,
`anthropics/formal-math` zeta23 @ `16a5ce41`, Apache-2.0). The rational bridge
`H ≥ 269/400` and its rational-series reduction: MultiAgency swarm
(`darkhipo/critical-line-269-400`, files `HGe269.lean` / `P2Plugs.lean`, ported here
into this package's `H`).
-/


noncomputable section

namespace BigOSpeedrun.CriticalLineZeros
namespace H269

open Finset

/-- `u = 1/√2`, the window parameter `ϑ = λ/√2` at `λ = 1`. -/
abbrev u : ℝ := 1 / Real.sqrt 2

theorem u_sq : u ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]

theorem u_pos : 0 < u := by positivity

theorem u_pow : ∀ n : ℕ, u ^ (2 * n) = (1 / 2 : ℝ) ^ n := by
  intro n
  rw [pow_mul, u_sq]

/-- `√2 = 2·u`: this is what turns `√2·tan u` into `2s`. -/
theorem sqrt2_eq_two_mul_u : Real.sqrt 2 = 2 * u := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  unfold u
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-! ## The two analytic plugs: Leibniz partial-sum bounds at `N = 4` (`k = 0..3`)

`A = sin u / u` and `B = cos u` are alternating series with terms
`a_k = (1/2)^k/(2k+1)!` and `b_k = (1/2)^k/(2k)!`; both sequences are antitone, so
Mathlib's `Antitone.alternating_series_le_tendsto` / `Antitone.tendsto_le_alternating_series`
sandwich the sums between the 4-term and 5-term partial sums.
-/

/-- `k`-th term of the rational series for `B = cos u`. -/
def bterm (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n / (2 * n).factorial

/-- The rational series for `cos u` (from `Real.hasSum_cos` and `u^(2n) = (1/2)^n`). -/
theorem hasSum_cos_rational : HasSum (fun n => (-1) ^ n * bterm n) (Real.cos u) := by
  have h := Real.hasSum_cos u
  have hfun : (fun n => (-1) ^ n * u ^ (2 * n) / (2 * n).factorial)
            = (fun n => (-1) ^ n * bterm n) := by
    funext n
    simp only [bterm]
    rw [u_pow n, mul_div_assoc]
  rwa [hfun] at h

theorem bterm_antitone : Antitone bterm := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hfac : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
  have hB : ((2 * (n + 1)).factorial : ℝ) = ((2 * n + 2) * (2 * n + 1)) * (2 * n).factorial := by
    rw [hfac, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hsplit : ((1 / 2 : ℝ) ^ n / (2 * n).factorial) * (((2 * n + 2) * (2 * n + 1)) * (2 * n).factorial)
      = (1 / 2 : ℝ) ^ n * ((2 * n + 2) * (2 * n + 1)) := by
    field_simp
  simp only [bterm]
  rw [hB, div_le_iff₀ (by positivity), hsplit, pow_succ]
  have hp : (0:ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hge : (1 / 2 : ℝ) ≤ ((2 * n + 2) * (2 * n + 1) : ℝ) := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  nlinarith

theorem cos_lower : ∑ i ∈ range 4, (-1) ^ i * bterm i ≤ Real.cos u :=
  Antitone.alternating_series_le_tendsto hasSum_cos_rational.tendsto_sum_nat bterm_antitone 2

theorem cos_upper : Real.cos u ≤ ∑ i ∈ range 5, (-1) ^ i * bterm i :=
  Antitone.tendsto_le_alternating_series hasSum_cos_rational.tendsto_sum_nat bterm_antitone 2

theorem bsum4 : ∑ i ∈ range 4, (-1) ^ i * bterm i = 4379 / 5760 := by
  simp [bterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

theorem bsum5 : ∑ i ∈ range 5, (-1) ^ i * bterm i = 4379 / 5760 + 1 / 645120 := by
  simp [bterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

/-- **Plug B**: `|cos u − 4379/5760| ≤ 1/645120`. -/
theorem cos_bound_N4 : |Real.cos u - 4379 / 5760| ≤ 1 / 645120 := by
  have h1 : 4379 / 5760 ≤ Real.cos u := by rw [← bsum4]; exact cos_lower
  have h2 : Real.cos u ≤ 4379 / 5760 + 1 / 645120 := by rw [← bsum5]; exact cos_upper
  rw [abs_le]
  constructor <;> linarith

/-- `k`-th term of the rational series for `A = sin u / u`. -/
def aterm (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n / (2 * n + 1).factorial

/-- The rational series for `sin u / u` (divide `Real.hasSum_sin` by `u ≠ 0`). -/
theorem hasSum_sin_rational : HasSum (fun n => (-1) ^ n * aterm n) (Real.sin u / u) := by
  have h := (Real.hasSum_sin u).div_const u
  have hfun : (fun n => (-1) ^ n * u ^ (2 * n + 1) / (2 * n + 1).factorial / u)
            = (fun n => (-1) ^ n * aterm n) := by
    funext n
    simp only [aterm]
    rw [pow_succ, u_pow n]
    field_simp
  rwa [hfun] at h

theorem aterm_antitone : Antitone aterm := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have hfac : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
  have hB : ((2 * (n + 1) + 1).factorial : ℝ) = ((2 * n + 3) * (2 * n + 2)) * (2 * n + 1).factorial := by
    rw [hfac, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hsplit : ((1 / 2 : ℝ) ^ n / (2 * n + 1).factorial) * (((2 * n + 3) * (2 * n + 2)) * (2 * n + 1).factorial)
      = (1 / 2 : ℝ) ^ n * ((2 * n + 3) * (2 * n + 2)) := by
    field_simp
  simp only [aterm]
  rw [hB, div_le_iff₀ (by positivity), hsplit, pow_succ]
  have hp : (0:ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hge : (1 / 2 : ℝ) ≤ ((2 * n + 3) * (2 * n + 2) : ℝ) := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  nlinarith

theorem sin_lower : ∑ i ∈ range 4, (-1) ^ i * aterm i ≤ Real.sin u / u :=
  Antitone.alternating_series_le_tendsto hasSum_sin_rational.tendsto_sum_nat aterm_antitone 2

theorem sin_upper : Real.sin u / u ≤ ∑ i ∈ range 5, (-1) ^ i * aterm i :=
  Antitone.tendsto_le_alternating_series hasSum_sin_rational.tendsto_sum_nat aterm_antitone 2

theorem asum4 : ∑ i ∈ range 4, (-1) ^ i * aterm i = 37043 / 40320 := by
  simp [aterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

theorem asum5 : ∑ i ∈ range 5, (-1) ^ i * aterm i = 37043 / 40320 + 1 / 5806080 := by
  simp [aterm, Finset.sum_range_succ, Nat.factorial]
  norm_num

/-- **Plug A**: `|sin u / u − 37043/40320| ≤ 1/5806080`. -/
theorem A_bound_N4 : |Real.sin u / u - 37043 / 40320| ≤ 1 / 5806080 := by
  have h1 : 37043 / 40320 ≤ Real.sin u / u := by rw [← asum4]; exact sin_lower
  have h2 : Real.sin u / u ≤ 37043 / 40320 + 1 / 5806080 := by rw [← asum5]; exact sin_upper
  rw [abs_le]
  constructor <;> linarith

/-! ## The rational margin and the target inequality `331·A ≥ 400·B` -/

/-- The exact `N = 4` margin: `331·(A_part − A_err) > 400·(B_part + B_err)`. -/
theorem margin :
    400 * (4379 / 5760 + 1 / 645120 : ℝ) < 331 * (37043 / 40320 - 1 / 5806080 : ℝ) := by
  norm_num

/-- Certificate value: `331·(A_part − A_err) − 400·(B_part + B_err) = 821/5806080`. -/
theorem margin_exact :
    331 * (37043 / 40320 - 1 / 5806080 : ℝ) - 400 * (4379 / 5760 + 1 / 645120 : ℝ) =
      821 / 5806080 := by
  norm_num

/-- **The target inequality** `400·cos u ≤ 331·(sin u / u)` (`331·A ≥ 400·B`). -/
theorem key_ineq : 400 * Real.cos u ≤ 331 * (Real.sin u / u) := by
  have hA : 37043 / 40320 - 1 / 5806080 ≤ Real.sin u / u := by
    linarith [(abs_le.1 A_bound_N4).1]
  have hB : Real.cos u ≤ 4379 / 5760 + 1 / 645120 := by
    linarith [(abs_le.1 cos_bound_N4).2]
  nlinarith [hA, hB]

/-- Positivity of `cos u`, free from the plug (no π bounds needed anywhere). -/
theorem cos_pos : 0 < Real.cos u := by
  have hB : Real.cos u ≤ 4379 / 5760 + 1 / 645120 := by
    linarith [(abs_le.1 cos_bound_N4).2]
  have h : (4379 / 5760 - 1 / 645120 : ℝ) ≤ Real.cos u := by
    linarith [(abs_le.1 cos_bound_N4).1]
  linarith

theorem sin_pos : 0 < Real.sin u := by
  have hu0 : u ≠ 0 := ne_of_gt u_pos
  have hA : (37043 / 40320 - 1 / 5806080 : ℝ) ≤ Real.sin u / u := by
    linarith [(abs_le.1 A_bound_N4).1]
  have hq : 0 < Real.sin u / u := by linarith
  have heq : Real.sin u = u * (Real.sin u / u) := by field_simp
  rw [heq]
  exact mul_pos u_pos hq

/-! ## The chain `s = u·tan u ≥ 200/331` -/

/-- `s = u·tan u`, the quantity the Montgomery–Taylor constant is written through. -/
def sval : ℝ := u * Real.tan u

theorem sval_eq : sval = u * Real.sin u / Real.cos u := by
  unfold sval
  rw [Real.tan_eq_sin_div_cos]
  ring

theorem sval_cos : sval * Real.cos u = u * Real.sin u := by
  have hcos_ne : Real.cos u ≠ 0 := ne_of_gt cos_pos
  rw [sval_eq]
  field_simp

/-- **Step (c)**: `s = u·tan u ≥ 200/331`, from `key_ineq` divided by `2·cos u`. -/
theorem s_ge : sval ≥ 200 / 331 := by
  have hu0 : u ≠ 0 := ne_of_gt u_pos
  have hsin : u * (Real.sin u / u) = Real.sin u := by field_simp
  have hmul1 : 400 * (u * Real.cos u) ≤ 331 * Real.sin u := by
    have hm : u * (400 * Real.cos u) ≤ u * (331 * (Real.sin u / u)) :=
      mul_le_mul_of_nonneg_left key_ineq (le_of_lt u_pos)
    calc 400 * (u * Real.cos u) = u * (400 * Real.cos u) := by ring
      _ ≤ u * (331 * (Real.sin u / u)) := hm
      _ = 331 * (u * (Real.sin u / u)) := by ring
      _ = 331 * Real.sin u := by rw [hsin]
  have hmul2 : 200 * Real.cos u ≤ 331 * sval * Real.cos u := by
    have hm : u * (400 * (u * Real.cos u)) ≤ u * (331 * Real.sin u) :=
      mul_le_mul_of_nonneg_left hmul1 (le_of_lt u_pos)
    calc 200 * Real.cos u = 400 * u ^ 2 * Real.cos u := by rw [u_sq]; norm_num
      _ = u * (400 * (u * Real.cos u)) := by ring
      _ ≤ u * (331 * Real.sin u) := hm
      _ = 331 * (sval * Real.cos u) := by rw [sval_cos]; ring
      _ = 331 * sval * Real.cos u := by ring
  have h3 : 200 ≤ 331 * sval := le_of_mul_le_mul_right hmul2 cos_pos
  linarith

theorem sval_pos : 0 < sval := by
  have h : (0 : ℝ) < 200 / 331 := by norm_num
  linarith [s_ge]

/-! ## The board constant `H` in terms of `s`, and the bound -/

/-- `√2·tan u = 2s` — the `√2 = 2u` step. -/
theorem sqrt2_mul_tan : Real.sqrt 2 * Real.tan u = 2 * sval := by
  unfold sval
  rw [sqrt2_eq_two_mul_u]
  ring

/-- The package's `H`, written through `s`. -/
theorem H_eq_two_sub : H = 3 / 2 - 1 / (2 * sval) := by
  unfold H
  have hu : (1 : ℝ) / Real.sqrt 2 = u := rfl
  rw [hu, sqrt2_mul_tan]

theorem inv_two_sval_le : 1 / (2 * sval) ≤ 331 / 400 := by
  have hs2 : (400 : ℝ) / 331 ≤ 2 * sval := by linarith [s_ge]
  have hpos : (0 : ℝ) < 2 * sval := by linarith [sval_pos]
  have hmul : (1 : ℝ) ≤ (331 / 400) * (2 * sval) := by
    have h := mul_le_mul_of_nonneg_left hs2 (by norm_num : (0:ℝ) ≤ 331 / 400)
    have hone : (331 / 400 : ℝ) * (400 / 331) = 1 := by norm_num
    linarith [h, hone]
  rw [div_le_iff₀ hpos]
  linarith

/-- **The board bound, in this package's own formulation**:
`H = 3/2 − 1/(√2·tan(1/√2)) ≥ 269/400`. -/
theorem h_ge_269_400 : (269 : ℝ) / 400 ≤ H := by
  rw [H_eq_two_sub]
  linarith [inv_two_sval_le]

/-! ## The equivalent Montgomery–Taylor forms (`cMT` = `Zeta23.ThmD.cStar 1`) -/

/-- `cStar 1 = 2s/(1+s)` — the `cMT` of the paper at `λ = 1`, in the `s` parameterisation. -/
theorem cStar_one_eq : Zeta23.ThmD.cStar 1 = 2 * sval / (1 + sval) := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold Zeta23.ThmD.theta sval
  have hu : (1 : ℝ) / Real.sqrt 2 = u := rfl
  rw [hu, sqrt2_mul_tan]
  simp only [sval]

theorem one_add_sval_pos : 0 < 1 + sval := by linarith [sval_pos]

/-- **`cMT ≥ 400/531`**, i.e. `cStar 1 ≥ 400/531`. -/
theorem cStar_one_ge : (400 : ℝ) / 531 ≤ Zeta23.ThmD.cStar 1 := by
  rw [cStar_one_eq]
  have hnum : (0 : ℝ) ≤ 662 * sval - 400 := by linarith [s_ge]
  have hden : (0 : ℝ) < 531 * (1 + sval) :=
    mul_pos (by norm_num) one_add_sval_pos
  have h1 : (1 + sval) ≠ 0 := ne_of_gt one_add_sval_pos
  have heq : 2 * sval / (1 + sval) - (400 : ℝ) / 531
      = (662 * sval - 400) / (531 * (1 + sval)) := by
    field_simp
    ring
  have hnn : 0 ≤ 2 * sval / (1 + sval) - (400 : ℝ) / 531 := by
    rw [heq]
    exact div_nonneg hnum (le_of_lt hden)
  linarith

/-- **`1/cMT ≤ 531/400`** — the reciprocal form of the same statement. -/
theorem one_div_cStar_one_le : 1 / Zeta23.ThmD.cStar 1 ≤ 531 / 400 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (400 : ℝ) / 531) cStar_one_ge
  have he : (1 : ℝ) / ((400 : ℝ) / 531) = 531 / 400 := by norm_num
  linarith [h, he]

/-- **`HD 1 = 2 − 1/cMT ≥ 269/400`** — the Theorem-D form of the same bound. -/
theorem hD_one_ge : (269 : ℝ) / 400 ≤ Zeta23.ThmD.HD 1 := by
  unfold Zeta23.ThmD.HD
  linarith [one_div_cStar_one_le]

/-- `cStar 1` is verbatim the verifier challenge's `cMT` (its §3 definition, quoted here so the
bridge can be read against the trusted statement without importing it):

`cMT := √2·tan(1/√2) / (1 + (1/√2)·tan(1/√2))`. -/
theorem cStar_one_eq_cMT :
    Zeta23.ThmD.cStar 1 =
      Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
        (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2)) := by
  rw [cStar_one_eq]
  have hu : (1 : ℝ) / Real.sqrt 2 = u := rfl
  rw [hu, sqrt2_mul_tan]
  simp only [sval]

/-- **`1/cMT ≤ 531/400`** in the verifier challenge's own expression. -/
theorem one_div_cMT_le :
    1 / (Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
        (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))) ≤ 531 / 400 := by
  rw [← cStar_one_eq_cMT]
  exact one_div_cStar_one_le

/-- **`2 − 1/cMT ≥ 269/400`** — the challenge's Theorem-D proportion, at the exact rational. -/
theorem two_sub_one_div_cMT_ge :
    (269 : ℝ) / 400 ≤
      2 - 1 / (Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
        (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))) := by
  rw [← cStar_one_eq_cMT]
  linarith [one_div_cStar_one_le]

/-- The `≥`-oriented restatement, matching the wording of the reduction notes. -/
example : H ≥ (269 : ℝ) / 400 := h_ge_269_400

/-! ## Axiom audit -/

#print axioms H269.h_ge_269_400
#print axioms H269.key_ineq
#print axioms H269.s_ge
#print axioms H269.cStar_one_ge
#print axioms H269.one_div_cStar_one_le
#print axioms H269.hD_one_ge
#print axioms H269.cStar_one_eq_cMT
#print axioms H269.one_div_cMT_le
#print axioms H269.two_sub_one_div_cMT_ge

end H269

end BigOSpeedrun.CriticalLineZeros
