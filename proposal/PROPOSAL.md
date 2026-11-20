# Proposal: Lean Verified row for zeta zeros on the critical line

**Board:** https://bigospeedrun.com/other/critical-line-zeros (no Lean Verified row exists)
**Result:** κ* ≥ H, H = 3/2 − cot(1/√2)/√2 ≈ 0.6725007 (Montgomery–Taylor constant)
**Credits:** Proof and trusted definitions — Anthropic (Claude; paper by Levent Alpöge and
Ralph Furman, arXiv:2608.13637), from anthropics/formal-math, folder `zeta23`, Apache-2.0.
Independent build verification, statement comparison, and submission package — MultiAgency
swarm.

## Statement match: exact

`KappaStarRow.lean` (this directory) is the proposed trusted challenge file, in the style of
`challenges/directed-sssp/CHDRow.lean`. Against the board's informal statement:

| Board | Lean | Match |
|---|---|---|
| nontrivial zero = zero ρ with 0 < Re ρ < 1 | `IsNontrivialZero` | exact |
| zero of multiplicity m counts m times | `Ncount` sums `zeroMult` (`analyticOrderAt`) | exact |
| simple = multiplicity 1 | `zeroMult ρ = 1` | exact |
| N(T): 0 < Im ρ ≤ T | `Ncount 0 T` = `zerosIn 0 T` | exact |
| N₀ˢ(T): simple + on line Re s = 1/2 | `N0simple 0 T` | exact |
| κ* ≥ c, unconditional, higher better | ε-form of liminf, no hypotheses | exact |
| c = H ≈ 0.6725007 | `H = 3/2 − 1/(√2·tan(1/√2))` | exact (cot x = 1/tan x) |

Anthropic's `montgomery_taylor_simple_on_critical_line_mult_cumulative` (zeta23/Challenge.lean,
Theorem D cumulative, simple) states `(2 − 1/cMT − ε)·N(0,T] ≤ N₀ˢ(0,T]`, and
2 − 1/cMT = H is an exact algebraic identity (verified numerically to 61 digits; one-line
`field_simp`-level adapter, tan treated opaquely). So the submitted theorem is a **3-line
delegation** to `Zeta23.ThmD.thmD₀_simple_mult_cumulative`, exactly as zeta23's own
Solution.lean does.

## Submission package (issue route recommended)

The verifier has no `critical-line-zeros` problem yet — a maintainer must first land the
trusted statement (this proposal) plus a profile entry. Sketch of the profile:

```json
"critical-line-zeros": {
  "challenge_file": "challenges/other-critical-line-zeros/KappaStarRow.lean",
  "lean_toolchain": "leanprover/lean4:v4.33.0-rc2",
  "manifest_file": "profiles/zeta23-lake-manifest.json",
  "solution_module": "Submission",
  "theorem_names": ["Race.bound"],
  "upstream_commit": "<anthropics/formal-math commit>"
}
```

Public repository layout (issue route): `Submission.lean` at root exporting
`BigOSpeedrun.CriticalLineZeros.Race.bound` (statement copied byte-for-byte from the
challenge file), the 316-file `Zeta23/` library vendored under `Submission/Zeta23/`
(~5.8 MB, Apache-2.0, NOTICE preserved), Lake config pinning Mathlib `51e6992e`
(v4.33.0-rc2 tag). Expect a **split build** (Catalan-style): the library is 316 modules on
top of full Mathlib.

**Policy question for the maintainer:** the manifest `bound` field convention is an exact
rational, but H is irrational. Proposal: fix H inside the trusted file (as done here) and
record the bound as the exact expression string + decimal for ranking; a rational-parameter
form (`Race.bound r` with rational r < H) would silently downgrade the verified constant.

## Gate expectations

- Axioms: only `propext, Classical.choice, Quot.sound` permitted — matches zeta23's audit.
- `sorry` count: 33 in zeta23, all in their two *trusted* challenge files (by design); the
  vendored library and Solution have none. Submission should exclude their Challenge files
  to avoid sorry-warnings confusion, or keep them unused.
- No RH or any hypothesis anywhere in the chain (top-level theorems are hypothesis-free).
- Board rule check: with no Lean Verified row on the board, any in-range bound runs; ours
  (0.6725007) beats the classic 0.407511 and ties the two top Claimed rows' constant.

## Verification status (MultiAgency, this machine)

See REPORT (final report): clone, `lake exe cache get` (8681/8681 files), `lake build`,
`lake env lean scripts/PrintAxioms.lean`.
