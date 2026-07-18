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

All nine stages are complete.  The library includes the finite Boolean/component API,
generalized Toffoli permutations, exact Gray/atomic decomposition, corrected lower-arity
obstruction, clean resource-qualified three-bit universality, the corrected circle-valued smooth
gate, a diffeomorphic circle extension of every finite Boolean permutation, and a qualified smooth
three-bit realization with an explicitly stable auxiliary face.  Main-result axiom audits report
only standard Lean/mathlib foundations. The final integration, structural, correction, and
reproducibility audits pass.

## Main entry points

- `Toffoli` is the lightweight discrete facade: Boolean permutations, component APIs, generalized
  gates, Gray decomposition, parity, and qualified three-bit synthesis.
- `Toffoli.Smooth` is deliberately separate: direct circle-valued extensions and qualified smooth
  three-bit realization. Importing the discrete facade does not pull in manifold dependencies.
- `Toffoli.CircleExtension.exists_extension` extends every finite Boolean permutation to a
  diffeomorphism of a finite product of the connected complex circle.
- `Toffoli.Synthesis.ThreeBitUniversal.circuit_cleanRealizes` and
  `Toffoli.CircleExtension.ThreeBitUniversal.exists_qualified_smooth_realization` expose the
  constants, returned auxiliaries, restriction, deletion, and exact resource qualification.

## Lean setup

The Lean project is isolated in `formal/` and pins Lean 4.32.0 plus an exact mathlib commit.  Fetch
the pinned dependencies once with:

```text
cd formal
lake update
```

Development follows [`BUILD-PLAN.md`](BUILD-PLAN.md): use narrow imports and focused leaf builds,
keep expensive proofs and diagnostics outside high-fanout modules, and reserve full builds for
configuration changes, public milestones, and final integration.

### Routine focused builds

Build the leaf being edited first, then only its adjacent public consumer.  Common targets are:

```text
cd formal
lake build Toffoli.Smoke
lake build Toffoli.Bool.Finite
lake build Toffoli.Gate.Toffoli
lake build Toffoli.Perm.Decomposition
lake build Toffoli.Synthesis.Universality
lake build Toffoli.Smooth.Extension
lake build Toffoli.Smooth.Synthesis.Universality
lake build Toffoli.Audit.PaperCircleOperation
```

Use `lake build Toffoli` for the discrete facade or `lake build Toffoli.Smooth` for the smooth
facade when that public surface changes.  Do not run `lake clean` during routine development: a
warm focused build is the intended feedback loop, while cleaning also forces the large mathlib
dependency graph to be rebuilt.

### Final all-surfaces milestone

The explicit final target set covers both public facades, every boundary audit, and every axiom
audit; the default Lake target covers only the discrete facade.  Reserve this cold command for a
release or final integration milestone:

```text
cd formal
lake clean
lake build \
  Toffoli.Smoke \
  Toffoli \
  Toffoli.Smooth \
  Toffoli.Audit.FiniteBoundary \
  Toffoli.Audit.GateBoundary \
  Toffoli.Audit.GrayBoundary \
  Toffoli.Audit.ParityBoundary \
  Toffoli.Audit.UniversalityBoundary \
  Toffoli.Audit.CircleBoundary \
  Toffoli.Audit.PaperCircleOperation \
  Toffoli.Audit.SmoothExtensionBoundary \
  Toffoli.Audit.SmoothSynthesisBoundary \
  Toffoli.Audit.Axioms.Finite \
  Toffoli.Audit.Axioms.Gate \
  Toffoli.Audit.Axioms.Decomposition \
  Toffoli.Audit.Axioms.Parity \
  Toffoli.Audit.Axioms.Universality \
  Toffoli.Audit.Axioms.Circle \
  Toffoli.Audit.Axioms.PaperCircleOperation \
  Toffoli.Audit.Axioms.SmoothExtension \
  Toffoli.Audit.Axioms.SmoothSynthesis
```

The recorded clean milestone completed 2607 jobs in 1099.53 s wall time (16568.58 s user,
1714.06 s system; maximum RSS 3009048 KiB). The final correction leaf was then added without
repeating that dependency rebuild: its focused and axiom builds took 5.05 s and 4.56 s, and the
final warm all-surface set above took 3.38 s. Across all main-result and correction axiom audits,
the only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

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
- `goal-1/9-INTEGRATE-AUDIT.md`: final build, import-graph, correction, hygiene, and axiom-audit
  evidence.
