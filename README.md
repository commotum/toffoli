# Toffoli 1981 formalization

This repository contains a reusable Lean 4 formalization of Tommaso Toffoli's paper
“Bicontinuous Extensions of Invertible Combinatorial Functions” (*Mathematical Systems Theory*
14, 13–23, 1981).

The paper is treated as a mathematical source rather than a formal specification. The project
verifies its finite permutation, decomposition, parity, universality, and smooth-extension
claims independently; corrections and strengthened hypotheses are recorded in
[`goal-1/0-plan.md`](goal-1/0-plan.md). Informal claims about gears, energy, or physical
realizability are outside the verified core unless a physical model is added explicitly.

## Status

Stages 1 through 8 are complete.  The library includes the finite Boolean/component API,
generalized Toffoli permutations, exact Gray/atomic decomposition, corrected lower-arity
obstruction, clean resource-qualified three-bit universality, the corrected circle-valued smooth
gate, a diffeomorphic circle extension of every finite Boolean permutation, and a qualified smooth
three-bit realization with an explicitly stable auxiliary face.  Main-result axiom audits report
only standard Lean/mathlib foundations.  Final integration and reproducibility review is in
progress.

## Lean setup

The Lean project is isolated in `formal/` and pins Lean 4.32.0 plus an exact mathlib commit.

```text
cd formal
lake update
lake build Toffoli.Smoke
lake build Toffoli.Bool
lake build Toffoli.Gate
lake build Toffoli.Decomposition
lake build Toffoli.Parity
lake build Toffoli.Synthesis
lake build Toffoli
lake build Toffoli.Smooth
lake build Toffoli.Audit.Axioms.SmoothExtension
lake build Toffoli.Audit.Axioms.SmoothSynthesis
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
- `goal-1/5-PARITY.md`: corrected lower-arity parity and low-arity obstruction evidence.
- `goal-1/6-UNIVERSALITY.md`: clean three-bit synthesis, resources, restriction/deletion, and
  low-arity correction evidence.
- `goal-1/7-CIRCLE-EXT.md`: recursive circle products, corrected smooth gate, and interpolation
  evidence.
- `goal-1/8-MANIFOLD-EXT.md`: arbitrary-permutation diffeomorphic extension, smooth three-bit
  fixed-face stability, qualified restriction/deletion, and axiom-audit evidence.
