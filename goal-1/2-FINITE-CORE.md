# 2-FINITE-CORE

Status: complete.

## Current Facts

- Stage 1 is complete. Lean 4.32.0 and exact mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997` are pinned and build successfully.
- `formal/Toffoli/Smoke.lean` imports only `Mathlib.Logic.Equiv.Basic`; no mathematical project definition exists yet.
- The finite paper layer uses Boolean powers, invertible maps, coordinate reindexing, no-fanout one-to-one composition, restriction with both source and target faces, and deletion of singleton-valued factors.
- Mathlib supplies `Equiv.Perm`, Pi/product equivalences, `Function.update`, finite-function cardinalities, and permutation composition. Its permutation multiplication convention is `(f * g) x = f (g x)`; this project should prefer named serial composition/equivalence `trans` at public boundaries.
- The paper's “componentwise” condition preserves separately indexed product factors; it does not say output coordinate `i` depends only on input coordinate `i`.
- Canonical deletion of a singleton factor after restriction and projection/deletion of a semantically constant Boolean output are different operations.

## Updated Assumptions

- Start with `BoolWord ι := ι → Bool` and `BoolPerm ι := Equiv.Perm (BoolWord ι)`, plus `Fin n` aliases. Generic finite index types make reindexing and disjoint component sums cleaner than arithmetic casts.
- Coordinate reindexing is an equivalence of word spaces induced by `ι ≃ κ`; permutation placement is conjugation by that word equivalence.
- Resource-free one-to-one circuits should be represented by a generated derivation closed under identity, serial composition, coordinate reindexing, and tensor/parallel composition on disjoint index sums. Its semantic permutation is explicit in the judgment, so it cannot be confused with a new kind of function composition.
- A face should be a predicate/subtype of words with selected coordinates fixed. Restriction of an equivalence requires an exact source/target membership equivalence (or an equivalent two-sided stability proof).
- Fixing/deleting a right index summand should be exposed as an explicit equivalence between retained words and the corresponding face subtype.
- Semantic dummy deletion should carry a certificate that the removed output coordinates are constant on the domain in question; arbitrary projection is not certified deletion.

## Big Picture Objective

Freeze a low-dependency finite API that represents Boolean words/permutations, reindexes and tensors their components, expresses resource-free one-to-one circuit construction, restricts equivalences to stable faces, and distinguishes identity extension, face-factor deletion, and semantic dummy-output deletion. The API must handle empty and low arities without nonempty assumptions.

## Detailed Implementation Plan

- Add `Toffoli.Bool.Defs` with generic and `Fin n` aliases, cardinality lemmas, and arity-zero facts.
- Add `Toffoli.Bool.Reindex` with word reindexing, permutation conjugation, identity/transitivity laws, and explicit application lemmas.
- Add `Toffoli.Component.Tensor` with parallel permutations over disjoint index sums and identity extension as a special case.
- Add `Toffoli.Component.OneToOne` with the resource-free generated circuit derivation and sound semantic constructors for identity, serial composition, tensor, and reindexing.
- Add `Toffoli.Component.Face` with fixed-coordinate face predicates and subtypes.
- Add `Toffoli.Component.Restriction` that turns an ambient equivalence plus exact face-image evidence into a face equivalence.
- Add `Toffoli.Component.Dummy` with fixed-right insertion/deletion equivalences and a separate semantic right-dummy certificate/projection API.
- Add `Toffoli.Audit.FiniteBoundary` with compile-time examples for arity zero, reindexing, tensor identity, face insertion/deletion, and dummy reconstruction. The audit leaf must remain outside public imports.
- Add thin finite public facade `Toffoli.Bool` only after the leaf APIs stabilize; do not import it internally.

## Build Structure

- Low/high-fanout definitions: `Bool/Defs`, `Bool/Reindex`, `Component/Tensor`, `Component/Face`, and the minimal certificate vocabulary in `Component/Dummy`. These should be kept small and frozen deliberately.
- Proof/derivation leaves: `Component/OneToOne` and `Component/Restriction`.
- Diagnostic leaf: `Audit/FiniteBoundary`; it is not imported by any public facade.
- Public facade: `Toffoli/Bool.lean`, imports/re-exports only.
- High-fanout files intentionally avoided: `Toffoli.lean` remains unchanged during leaf development and is updated only after focused builds pass.
- Initial focused commands use `lake build +Toffoli.<Leaf>:olean`; adjacent consumers are built only after their dependencies compile.
- A full build trigger applies only when the new public facade/root import is intentionally promoted at stage end.

## No-Cheating Checks

- Do not identify a restricted map with a permutation unless exact source-to-target face behavior supplies a two-sided inverse.
- Do not call arbitrary coordinate projection “dummy deletion.” Require and use a constancy certificate.
- Do not encode one-to-one composition as unrestricted function substitution or an API that permits fan-out silently.
- Do not hide coordinate casts with unproved propositions or assume `n > 0` for definitions intended to cover arity zero.
- Do not add later-stage Toffoli gates, Gray decomposition, parity, synthesis constants, or manifold definitions here.

## Boundary Checks

- Internal leaves import exact dependencies and never `Toffoli.lean` or the finite facade.
- Finite modules import no manifold, topology, sign/parity, or heavy permutation-factorization modules.
- No broad global notation, instance, or simp attribute is added without a demonstrated consumer.
- Ordinary `Equiv.trans`/permutation multiplication conventions are documented separately from the one-to-one generated derivation.
- Singleton-factor deletion and semantic Boolean-output deletion have distinct names and types.

## Completion Requirements

- Every planned finite declaration has a documented owner module and builds without `sorry`, `admit`, or project axioms.
- Reindexing and tensor laws, exact face restriction, fixed-right insertion/deletion, and semantic dummy reconstruction are proved.
- The one-to-one derivation admits only identity, primitive, bare coordinate wiring, serial,
  tensor, and circuit-reindexing steps and exposes the resulting ordinary permutation.
- Arity-zero word cardinality and permutation uniqueness are proved; low-arity audit examples compile.
- Focused builds pass for every touched leaf and the audit leaf; the finite facade and necessary root adjacent target pass after promotion.
- Project proof-hole/axiom scans, forbidden-import scans, trailing-whitespace checks, and `git diff --check` pass.
- Public finite declarations have a recorded axiom audit; expected foundational/classical axioms, if any, are explained.
- `0-plan.md` and this stage file record exact module paths, theorem names, commands, timings, and any changed assumptions.

## Stage Results

- Representation is frozen as `BoolWord ι := ι → Bool`, `BoolVec n := BoolWord (Fin n)`,
  `BoolPerm ι := Equiv.Perm (BoolWord ι)`, and `BoolPermN n := BoolPerm (Fin n)`.
- `Toffoli.Bool.Defs` owns only the aliases. `Toffoli.Bool.Finite` isolates the materially heavier
  cardinality imports and proves `card_boolWord`, `card_boolVec_zero`, arity-zero word uniqueness,
  and `boolPermN_zero_eq_refl`.
- `Toffoli.Bool.Reindex` defines word-space reindexing, permutation conjugation, bare coordinate
  wiring, and identity/transitivity/serial laws. The two wiring notions have deliberately distinct
  definitions and types.
- `Toffoli.Component.Tensor` defines disjoint parallel composition and identity extension, with
  pointwise and serial laws. `Toffoli.Component.OneToOne` defines the resource-free circuit syntax
  and evaluator. `eval_serial_apply` pins the convention: the first circuit acts first.
- `Toffoli.Component.Face` and `Toffoli.Component.Restriction` define partial-assignment faces and
  exact source-to-target restrictions. `Toffoli.Component.Dummy` separately defines fixed-face
  factor insertion/deletion and certificate-driven semantic dummy deletion; no arbitrary
  projection is exported as certified deletion.
- `Toffoli.Audit.FiniteBoundary` checks arity zero, reindexing, tensoring, face round trips, dummy
  reconstruction, and empty-atom circuits. It is outside the public import graph.
- The thin `Toffoli.Bool` facade imports the finite leaves only. The root `Toffoli` import was
  promoted from the Stage 1 smoke leaf to `Toffoli.Bool` only after focused builds passed.
- Focused builds passed on 2026-07-17: `Bool.Finite` (759 jobs, 1.4 s),
  `Component.Restriction` (394 jobs, 1.1 s), `Component.OneToOne` (312 jobs, 1.1 s),
  `Audit.FiniteBoundary` (766 jobs, 1.4 s), and `Toffoli.Bool` (766 jobs, 1.4 s). The final
  pointwise-law/facade promotion was rechecked before stage closure.
- `Toffoli.Audit.Axioms.Finite` builds and reports only Lean's standard `propext`,
  `Classical.choice`, and `Quot.sound`; it reports no project-specific axiom. The audit leaf took
  3.05 s for 766 jobs and remains non-public.
- Scans found no `sorry`, `admit`, `sorryAx`, project `axiom`, `unsafe` declaration, broad
  `import Mathlib`, manifold import, or synthesis import in the finite modules. `git diff --check`
  passed.
