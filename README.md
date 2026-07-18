# Toffoli 1981 formalization

This repository is developing a reusable Lean 4 formalization of Tommaso Toffoli's paper
“Bicontinuous Extensions of Invertible Combinatorial Functions” (*Mathematical Systems Theory*
14, 13–23, 1981).

The paper is treated as a mathematical source rather than a formal specification. The project
will verify its finite permutation, decomposition, parity, universality, and smooth-extension
claims independently; corrections and strengthened hypotheses are recorded in
[`goal-1/0-plan.md`](goal-1/0-plan.md). Informal claims about gears, energy, or physical
realizability are outside the verified core unless a physical model is added explicitly.

## Status

Stages 1 through 4 are complete: the source/setup audit, finite Boolean/component API,
generalized Toffoli/AND-NAND permutations, and exact Gray/atomic decomposition all build and have
recorded axiom audits. Parity, qualified universality, and smooth extension remain in progress.

## Lean setup

The Lean project is isolated in `formal/` and pins Lean 4.32.0 plus an exact mathlib commit.

```text
cd formal
lake update
lake build Toffoli.Smoke
lake build Toffoli.Bool
lake build Toffoli.Gate
lake build Toffoli.Decomposition
lake build Toffoli
```

Development follows [`BUILD-PLAN.md`](BUILD-PLAN.md): use narrow imports and focused leaf builds,
keep expensive proofs and diagnostics outside high-fanout modules, and reserve full builds for
configuration changes, public milestones, and final integration.

## Sources and operating documents

- `toffoli-1981/`: supplied PDF, Markdown transcription, and figures.
- `goal-1/0-plan.md`: authoritative staged plan, paper map, correction log, and dependencies.
- `goal-1/0-loop.md`: repeatable implementation and verification protocol.
- `goal-1/1-SOURCE-AUDIT.md`: source/setup evidence and results.
- `goal-1/2-FINITE-CORE.md`: finite API design and verification evidence.
- `goal-1/3-TOFFOLI.md`: generalized-gate design and verification evidence.
- `goal-1/4-GRAY-DECOMP.md`: exact Gray-palindrome and finite-permutation decomposition evidence.
