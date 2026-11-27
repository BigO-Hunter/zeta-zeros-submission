# Critical-line zeros — draft Lean submission

Root target: `Race.bound`, proving κ* ≥ H with
`H = 3/2 - 1/(√2 * tan(1/√2)) = 3/2 - cot(1/√2)/√2`.
The proof delegates to `Zeta23.ThmD.thmD₀_simple_mult_cumulative`; the only new
mathematics is the exact constant adapter `H_eq_HD`.

> Board (Nov 26 2026): the critical-line race is OPEN, currently led by H. M. Bui + 2 more's claimed κ* ≥ 0.703703 (Nov 20); this repo is a draft replay of Anthropic's κ* ≥ 3/2 − cot(1/√2)/√2 — see [bigospeedrun.com](https://bigospeedrun.com).

## Status

**Draft, not submitted.** On 2026-11-04 the maintainer wrote in
[verifier #146](https://github.com/bigospeedrun/verifier/issues/146) that the
critical-line-zeros route does not accept outside submissions yet. Maintainers
will write the trusted statement, choose pins, and rerun Anthropic's proof first.
This package therefore vendors the proposed statement surface for local replay;
its definitions-only copy excludes the deliberate `sorry` challenge theorem.
When the route opens, replace `Submission/KappaStarRow.lean` with the official
statement minus its target and recheck `Submission.lean`.

## Contents

- `Submission/` — 318 modules: the complete Zeta23 library plus the proposed
  definitions (only import paths prefixed with `Submission.`).
- `proposal/` — the original `zeta-zeros-proposal` repository at source commit
  `9d711e2659768c34e4d9b1c49a9a5a94f4f2a70d` (full history): design background for
  the draft submission.

## Provenance and build

Proof and counting definitions: Anthropic (Claude), Levent Alpöge and Ralph
Furman, [`anthropics/formal-math`](https://github.com/anthropics/formal-math)
commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, directory `zeta23`,
Licensed under the CFSF License (see `LICENSE` and `NOTICE`; [github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf)). Packaging and independent replay:
MultiAgency swarm.

Native pins: Lean **v4.33.0-rc2**, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`.

```sh
lake exe cache get
lake build Submission
lake env lean Submission.lean
```

## Verification receipt (2026-11-04)

- `lake build Submission`: **9016 jobs, completed successfully** on Lean v4.33.0-rc2.
- `lake env lean Submission.lean`: exit 0, no warnings.
- `#print axioms Race.bound`: exactly `[propext, Classical.choice, Quot.sound]`.
- The proposed trusted `KappaStarRow.lean` also elaborates independently against the
  same toolchain (its intentional challenge `sorry` is the only warning).

No RH assumption and no `sorry` occurs in the proof chain. The official verifier
has not run this draft; its final statement and pins may differ.

## What work can be done here

Route not open (verifier#146). Open work: swap the statement surface when the route opens and recheck; local replay of the 9016-job build meanwhile.

Part of [BigO-Hunter](https://github.com/BigO-Hunter) — independent verification and packaging for [Big O Speedrun](https://bigospeedrun.com) · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).
