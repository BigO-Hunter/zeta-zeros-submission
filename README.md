# Critical-line zeros — draft Lean submission

Root target: `Race.bound`, proving κ* ≥ H with
`H = 3/2 - 1/(√2 * tan(1/√2)) = 3/2 - cot(1/√2)/√2`.
The proof delegates to `Zeta23.ThmD.thmD₀_simple_mult_cumulative`; the only new
mathematics is the exact constant adapter `H_eq_HD`.

## Status

**Draft, not submitted.** On 2026-11-04 the maintainer wrote in
[verifier #146](https://github.com/bigospeedrun/verifier/issues/146) that the
critical-line-zeros route does not accept outside submissions yet. Maintainers
will write the trusted statement, choose pins, and rerun Anthropic's proof first.
This package therefore vendors the proposed statement surface for local replay;
its definitions-only copy excludes the deliberate `sorry` challenge theorem.
When the route opens, replace `Submission/KappaStarRow.lean` with the official
statement minus its target and recheck `Submission.lean`.

## Provenance and build

Proof and counting definitions: Anthropic (Claude), Levent Alpöge and Ralph
Furman, [`anthropics/formal-math`](https://github.com/anthropics/formal-math)
commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, directory `zeta23`,
Licensed under the CFSF License (see `LICENSE` and `NOTICE`; ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf))). Packaging and independent replay:
MultiAgency swarm.

Native pins: Lean **v4.33.0-rc2**, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`. The 318 modules under
`Submission/` are the complete Zeta23 library plus the proposed definitions;
only import paths were prefixed with `Submission.`.

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
