# 5-PARITY

Status: complete.

## Current Facts

- `BoolPerm.extendRight p κ` is the product permutation that repeats `p` independently for every
  Boolean assignment on the unused coordinate type `κ`.
- `Equiv.Perm.sign_permCongr`, `sign_prodCongrLeft`, and `sign_mul` are available in the pinned
  `Mathlib.GroupTheory.Perm.Sign` leaf.
- An atomic edge and every full-arity AND/NAND gate is one literal transposition and hence odd.
- A proper-arity lift repeats its local permutation `2 ^ card κ` times; this exponent is even when
  the unused coordinate type is nonempty.
- Bare coordinate wiring is distinct from conjugating/placing a gate. A coordinate swap on two
  bits is odd, so the paper's parity proof does not cover free wiring at ambient arity two.

## Updated Assumptions

- First prove a reusable exact sign formula for identity extension, then derive evenness from a
  witnessed nonempty unused factor. Do not bake AND/NAND-specific facts into the lift theorem.
- Represent a proper-arity generator by an explicit local permutation, unused coordinate type,
  and coordinate equivalence into the ambient type. This states placement and resource counts
  without arithmetic casts.
- State the source-faithful serial-generation obstruction separately from any stronger result that
  admits bare coordinate permutations as generators. Settle arities zero, one, and two explicitly;
  do not hide the two-bit wiring exception behind `n ≥ 3` without recording it.

## Big Picture Objective

Derive the exact sign of a lifted finite Boolean permutation and use it to prove the strongest
correct lower-arity non-generation theorem, with the scope of coordinate wiring and every
low-arity exception made explicit.

## Detailed Implementation Plan

- Add a proof-side parity lift leaf over `Component.Tensor` and mathlib sign, proving the exact
  exponent/cardinality formula and invariance under coordinate reindexing.
- Define a low-dependency serial-generation predicate or bundled proper lift whose constructors
  expose local/unused coordinate types and placement equivalences.
- Prove that every nontrivial proper lift is even and that serial closure preserves evenness.
- Exhibit a full-arity atomic/AND-NAND permutation of sign `-1`, yielding non-generation.
- Analyze bare coordinate wiring separately, including the odd two-bit coordinate swap and the
  corrected ambient-arity hypotheses for any wiring-inclusive theorem.
- Add low-arity computations and an axiom audit under `Toffoli.Audit`; expose only a thin parity
  facade after the focused leaves pass.

## Build Structure

- `Parity/Lift`: reusable sign formula; imports exact sign and tensor/reindex dependencies only.
- `Parity/Generated`: data/inductive serial closure, below the final obstruction proof.
- `Parity/Obstruction`: heavy final theorem and source comparison.
- `Audit/ParityBoundary` and `Audit/Axioms/Parity`: diagnostic leaves, never public imports.
- Internal parity leaves do not import `Toffoli.Decomposition`, a public facade, synthesis, or
  smooth modules. Focused leaf builds precede any facade/root milestone build.

## No-Cheating Checks

- Computed signs are diagnostics only; the extension exponent and generation obstruction are
  proved for arbitrary finite coordinate types.
- “Lower arity” carries an explicit nonempty unused factor or a proved strict-cardinality
  equivalent; it is not an unverified natural-number inequality attached to an arbitrary map.
- Coordinate placement by conjugation and a bare wiring permutation remain different constructors
  and receive different parity arguments.

## Boundary Checks

- The empty Boolean cube has one point and no odd permutation.
- A one-bit full gate is odd; there are no positive-order proper AND/NAND generators.
- A two-bit coordinate swap is odd even though every proper gate lift is even.
- The sign exponent uses the number of unused Boolean assignments, not merely the number of unused
  coordinates.
- Sign/group imports remain above all finite, cube, and gate-core leaves.

## Completion Requirements

- The identity-extension sign formula and nonempty-unused evenness theorem compile.
- The exact generator closure and an odd excluded permutation are named in the final theorem.
- Bare-wiring and arity `0`, `1`, and `2` cases have proved or decisively audited dispositions.
- C-007, C-008, and C-020 are updated with Lean evidence.
- Focused, adjacent-consumer, audit, axiom, scan, diff, facade/root, and proportional milestone
  builds pass and are recorded.

## Stage Results

- Added `Parity.Lift` with
  `sign_extendRight p = sign(p) ^ card (BoolWord unused)` and its `2 ^ card unused` corollary.
  A nonempty unused coordinate factor therefore makes every lifted local permutation even.
- Added `ProperLift` and `ProperlyGenerated`. This placement/conjugation-only closure permits an
  arbitrary local permutation, not merely AND/NAND, and `exists_not_properlyGenerated` excludes a
  full atomic edge on every nonempty finite ambient cube.
- Added `Parity.Wiring`. A coordinate transposition on `2 + k` bits has sign
  `(-1) ^ (2 ^ k)`; permutation induction proves every bare coordinate wiring even when `0 < k`.
- Added the exact paper generator subgroup in `Parity.Paper`: proper-order AND/NAND placements plus
  bare coordinate wirings. For `n ≥ 3` it lies in the even subgroup, so a full atomic edge is not
  generated.
- Settled all exceptional arities. At `n=0`, `paperGenerated_zero_eq_top` proves there is no
  obstruction. At `n=1`, the generator subgroup is trivial and NOT is excluded. At `n=2`, the
  coordinate swap is odd, so the printed parity proof is invalid; nevertheless every generator
  commutes with global bitwise complement while CNOT does not, proving
  `thetaSucc_one_not_mem_paperGenerated`.
- `ParityBoundary` checks the repetition exponent and the odd/even two-/three-bit wiring examples.
  `Axioms.Parity` reports only `propext`, `Classical.choice`, and `Quot.sound` for the exported
  results.
- Focused leaves, paper/root/audit promotion (952 jobs), and the warm milestone full build
  (950 jobs, 1.38 s) passed without warnings. Placeholder, broad-import, and whitespace scans
  passed. Sign and subgroup infrastructure remains entirely above finite/gate/decomposition core.
