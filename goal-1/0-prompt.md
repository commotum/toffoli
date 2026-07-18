# Goal 1 Maintenance/Extension Prompt

```text
The planned Goal 1 formalization is complete. Read `goal-1/0-plan.md` and its recorded audit
evidence before making a maintenance change or adding an explicitly requested new stage; use the
execution protocol in `goal-1/0-loop.md` for that work.

The objective is to build a correct, reusable Lean 4 library that independently verifies and, where necessary, corrects the mathematical claims in “Bicontinuous Extensions of Invertible Combinatorial Functions”: finite Boolean permutations, one-to-one component composition and reindexing, generalized Toffoli gates, Gray-code/atomic-flip decomposition, parity obstructions, qualified three-bit Toffoli universality, reusable restriction/extension operations, and smooth circle/manifold extensions.

Treat the paper as a source rather than a formal specification. Preserve the distinctions between finite permutations and smooth extensions; ordinary and one-to-one composition; fixed-input restriction and dummy deletion; diffeomorphic existence and physical realizability; and unrestricted versus constants/ancillas-based universality. Pin Lean/mathlib, cover empty and low arities, verify quotient well-definedness and smooth inverses, count all universality resources, use no `sorry` or unexplained project-specific axioms, and keep the paper map, correction log, dependency notes, and axiom audit current. Follow repository-root `BUILD-PLAN.md`: keep cheap definitions in low-dependency modules, heavy proofs and diagnostics in leaves, public APIs thin, imports narrow, and high-fanout edits rare and intentional.

For each future session: sync actual files and tests; preserve the completed claim map and
correction log; identify the narrowest owner module and focused build; add a new stage only when
the requested scope requires one; run focused leaf and necessary adjacent-consumer checks, using
full builds only for `BUILD-PLAN.md` triggers or milestones; and record any changed evidence.

Completion means the original objective is genuinely achieved with a reproducible clean build and audited main theorems. Do not redefine success as an easier subset. Corrections, decisive disproofs, and genuinely unresolved issues must be documented and carried forward as explicit next work.
```
