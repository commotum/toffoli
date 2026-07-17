# 3-TOFFOLI

Status: complete.

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

- Add a narrow `Toffoli.Gate.Toffoli` leaf owning the gate specification, active predicate, word
  update, involution, and permutation packaging.
- Prove target/control/non-control evaluation laws, exact support behavior, and the empty-control
  NOT case.
- Add `Toffoli.Gate.Wiring` for coordinate reindexing and disjoint-left placement, proving agreement
  with `BoolPerm.reindex` and `BoolPerm.extendRight`.
- Add `Toffoli.Gate.AndNand` for paper-order and named NOT/CNOT/three-bit specializations only after
  the generic leaf builds.
- Put low-arity truth-table checks and edge-swap checks in `Toffoli.Audit.GateBoundary`, not in the
  public gate module.
- Add `Toffoli.Audit.Axioms.Gate`, then expose a thin `Toffoli.Gate` facade after all leaf checks.

## Build Structure

- Low-dependency public definition/proof leaf: `Toffoli/Gate/Toffoli.lean`, importing only
  `Mathlib.Data.Finset.Basic` and `Toffoli.Bool.Defs`.
- Paper-family leaf: `Toffoli/Gate/AndNand.lean`, adding only finite-index facts.
- Wiring leaf: `Toffoli/Gate/Wiring.lean`, adding exact Boolean reindex/tensor dependencies without
  making them dependencies of the gate core.
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

- `ToffoliGate ι` stores a finite positive-control set, target, and target-not-a-control proof. The
  specification has no `DecidableEq` parameter; equality is required only by executable `run` and
  `perm`, avoiding an unnecessary instance choice in the mathematical data.
- `Toffoli.Gate.Toffoli` proves control invariance under target update, `run_involutive`,
  self-inverse permutation packaging, target/control/non-target evaluation, exact fixed-word and
  changed-coordinate characterizations, and the AND/NAND truth convention with fixed target bits.
- `notAt`, `cnot`, and `ccnot` expose zero-, one-, and two-control specializations with all required
  distinctness hypotheses. The empty control conjunction is formally true.
- `Toffoli.Gate.AndNand` defines `andNandSpec` using every non-target coordinate and
  `AndNand.thetaSucc n : BoolPermN (n + 1)`. The parameter counts controls: `thetaSucc 0` is NOT,
  `thetaSucc 1` is CNOT, and `thetaSucc 2` is three-bit Toffoli. `thetaSucc_active_iff` and component
  laws pin the final-coordinate convention.
- `Toffoli.Gate.Wiring` defines embedding-based specification mapping. `perm_map_equiv` proves it
  equals permutation conjugation along an equivalence; `perm_inl` proves left placement equals
  tensor extension by identity on unused right coordinates.
- `Toffoli.Audit.GateBoundary` proves no target-bearing gate exists on `Fin 0` and uses kernel
  `decide` checks for NOT, CNOT, all four relevant three-bit control cases, and the empty-control
  convention. No `native_decide` or external evaluator is trusted.
- Focused builds passed on 2026-07-17: core `Toffoli.Gate.Toffoli` (602 jobs, 2.1 s), paper family
  and wiring together (636 jobs, 1.5 s maximum), boundary audit (639 jobs, 1.5 s), axiom audit
  (638 jobs, 1.3 s), and facade (637 jobs, 1.3 s).
- `Toffoli.Audit.Axioms.Gate` reports only the standard `propext`, `Classical.choice`, and
  `Quot.sound` dependencies. Scans found no proof hole, project axiom, unsafe declaration, broad
  umbrella import, or reverse dependency on Gray/parity/synthesis/manifold code. `git diff
  --check` passed.
- The thin root import was promoted once, after validation, to expose both `Toffoli.Bool` and
  `Toffoli.Gate`. The promoted root built in 1.3 s (771 jobs; command wall time 2.78 s), and the
  warm milestone full build passed in 1.51 s (772 jobs).
