# 3-TOFFOLI

Status: in progress.

## Current Facts

- Stage 2 freezes `BoolWord ι := ι → Bool` and `BoolPerm ι := Equiv.Perm (BoolWord ι)`.
- `BoolPerm.reindex` is conjugation along an index equivalence; `BoolPerm.coordinatePerm` is bare
  coordinate wiring. `BoolPerm.extendRight` tensors a permutation with identity on a disjoint
  right summand.
- The paper's order-`n` AND/NAND function fixes the first `n - 1` bits and complements the final
  bit exactly when all controls are true; for order one, the empty control conjunction is true.
- The later Gray proof needs both the standard all-true-controlled gate and an exact statement that
  a fully controlled gate swaps one cube edge and fixes every other vertex.

## Updated Assumptions

- Represent a generalized gate by a target coordinate, a finite set of positive controls, and a
  proof that the target is not a control. This gives meaningful gates without requiring the whole
  index type to be finite; paper-order specializations add `Fintype` only where needed.
- Define the word update first, prove that it preserves the control predicate and is involutive,
  then package the same map in both directions as `BoolPerm`.
- Keep arbitrary zero/one control patterns for the later atomic layer rather than silently calling
  them standard AND/NAND gates. Zero-controls will be obtained by explicit NOT conjugation.

## Big Picture Objective

Formalize generalized Toffoli/AND-NAND gates as explicit self-inverse Boolean permutations, prove
their component semantics and boundary cases, and make their behavior under reindexing and unused
coordinates reusable by decomposition, parity, and synthesis.

## Detailed Implementation Plan

- Add a narrow `Toffoli.Gate.Toffoli` leaf owning the gate specification, enabled predicate, word
  update, involution, and permutation packaging.
- Prove target/control/non-control evaluation laws, exact support behavior, and the empty-control
  NOT case.
- Define coordinate reindexing of gate specifications and prove that its permutation agrees with
  `BoolPerm.reindex`.
- Define placement into a disjoint left summand and prove agreement with `BoolPerm.extendRight`.
- Add paper-order and named NOT/CNOT/three-bit specializations only after the generic leaf builds.
- Put low-arity truth-table checks and edge-swap checks in `Toffoli.Audit.GateBoundary`, not in the
  public gate module.
- Add `Toffoli.Audit.Axioms.Gate`, then expose a thin `Toffoli.Gate` facade after all leaf checks.

## Build Structure

- Low-dependency public definition/proof leaf: `Toffoli/Gate/Toffoli.lean`, importing only finite
  sets/functions and the exact Boolean reindex/tensor leaves.
- Diagnostic leaf: `Toffoli/Audit/GateBoundary.lean`; it is never publicly imported.
- Diagnostic axiom leaf: `Toffoli/Audit/Axioms/Gate.lean`; it is never publicly imported.
- Public facade: `Toffoli/Gate.lean`, imports only stable gate leaves.
- `Toffoli.lean` remains untouched during development and changes once, after facade validation.
- Focused command: `lake build +Toffoli.Gate.Toffoli:olean`; adjacent checks are the boundary and
  axiom leaves, then `+Toffoli.Gate:olean`. A root/full build is triggered only at facade promotion.

## No-Cheating Checks

- A gate permutation must be packaged from a proved two-sided inverse, not finite cardinality.
- Target/control overlap is rejected by data rather than erased by simplification.
- Reindexing and extension are proved equal to existing component operations, not merely tested.
- Truth-table evaluation is diagnostic evidence; it does not replace generic involution proofs.

## Boundary Checks

- The gate leaf imports no Gray decomposition, sign/parity, synthesis, topology, or manifold code.
- The standard gate has positive controls only; arbitrary control patterns remain a separate later
  construction so the AND/NAND name retains the paper's convention.
- Order one uses the empty-control truth convention deliberately. There is no order-zero paper gate
  because a target coordinate is part of the gate specification.
- No new global notation, instance, or broad simp set is introduced.

## Completion Requirements

- The generic update and packaged permutation are proved involutive without `sorry` or local axioms.
- Target, controls, non-target coordinates, enabled/disabled behavior, and exact changed-word
  characterization are proved.
- Empty-, one-, and two-control special cases match NOT, CNOT, and the three-bit Toffoli convention.
- Reindexing and unused-coordinate extension laws compile.
- Focused leaf, boundary, facade, root, and axiom-audit builds pass; scans and `git diff --check` pass.
- `0-plan.md`, the paper map, dependency notes, and correction log are updated with final names.

## Stage Results

- Pending.
