# H ≥ 269/400 — build receipt

`Submission/H269.lean` and `Submission/H269Row.lean`, added on branch `h269-port`
(2026-11-07). Pins unchanged: Lean v4.33.0-rc2, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`.

## What is proved

In this package's own formulation (`BigOSpeedrun.CriticalLineZeros.H`,
`Submission/KappaStarRow.lean`):

| declaration | statement |
|---|---|
| `H269.h_ge_269_400` | `(269 : ℝ) / 400 ≤ H`, i.e. `3/2 − 1/(√2·tan(1/√2)) ≥ 269/400` |
| `H269.cStar_one_ge` | `400/531 ≤ Zeta23.ThmD.cStar 1` (the `cMT` of the paper at λ = 1) |
| `H269.one_div_cStar_one_le` | `1 / Zeta23.ThmD.cStar 1 ≤ 531/400` (the `1/cMT` form) |
| `H269.hD_one_ge` | `269/400 ≤ Zeta23.ThmD.HD 1` (the Theorem-D form `2 − 1/cMT`) |
| `H269.cStar_one_eq_cMT` | `cStar 1` **is** the verifier challenge's `cMT` (its §3 expression, quoted) |
| `H269.one_div_cMT_le` | `1/cMT ≤ 531/400` in the challenge's own expression |
| `H269.two_sub_one_div_cMT_ge` | `269/400 ≤ 2 − 1/cMT` — the challenge's Theorem-D proportion |
| `Race.bound_269_400` | `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (269/400 − ε)·N(T) ≤ N₀ˢ(T)` |
| `Race.h_ge_269_400_via_HD` | `269/400 ≤ H` again through `H_eq_HD` + `hD_one_ge` |

`H ≈ 0.67250070367941164573…`, so the margin is `7.0368e-7`: the certificate is
genuinely marginal and the rational proof is exact, not numeric.

## How

`u = 1/√2` gives `u² = 1/2` exactly, so `A = sin u / u` and `B = cos u` are rational
alternating series. The only analytic inputs are Mathlib's Leibniz partial-sum bounds
(`Antitone.alternating_series_le_tendsto`, `Antitone.tendsto_le_alternating_series`) at
N = 4 terms:

```
|sin u / u − 37043/40320| ≤ 1/5806080      (A bound)
|cos u     − 4379/5760 | ≤ 1/645120        (B bound)
331·(37043/40320 − 1/5806080) − 400·(4379/5760 + 1/645120) = 821/5806080 > 0
```

hence `400·cos u ≤ 331·(sin u / u)`, hence `s = u·tan u ≥ 200/331`, hence
`H = 3/2 − 1/(2s) ≥ 269/400` and `cStar 1 = 2s/(1+s) ≥ 400/531`. Everything else is
field algebra plus `norm_num`. No `Real.pi` bounds are used anywhere: `sin u` and
`cos u` are positive by the plugs themselves.

## Axiom audit

Every declaration above reports exactly `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`, no `native_decide`, no custom axioms. `Submission/H269.lean` imports only
`Mathlib`, `Submission.KappaStarRow` and `Submission.Zeta23.ThmD.Functional`, so the
bound itself carries no dependency on Theorem D.

## Build

```
cd <repo> && lake build Submission          # 9018 jobs, "Build completed successfully"
lake env lean Submission.lean               # rc 0 (root target unchanged)
lake env lean Submission/H269.lean          # rc 0
lake env lean Submission/H269Row.lean       # rc 0
```

## Provenance

κ* ≥ H mathematics: Anthropic (Claude), Levent Alpöge, Ralph Furman —
`anthropics/formal-math` `zeta23` @ `16a5ce41`, Apache-2.0. The rational bridge
`H ≥ 269/400` and its rational-series reduction: MultiAgency swarm, ported from
`darkhipo/critical-line-269-400` (`HGe269.lean`, `P2Plugs.lean`) into this package's
`H`. AI-authored, disclosed.
