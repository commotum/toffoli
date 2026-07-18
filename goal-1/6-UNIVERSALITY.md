# 6-UNIVERSALITY

Status: in progress.

## Current Facts

- `AtomicWord.exists_eval_eq` reduces every finite Boolean permutation to a serial word of literal
  cube-edge atoms, with list-head-first evaluation.
- `Component.fixRightEquiv`, `restrictFaces`, and `RightDummy` already distinguish face
  restriction, deletion of singleton factors, and certified semantic output deletion.
- A three-bit Toffoli can implement NOT with two fixed-`true` controls, CNOT with one fixed-`true`
  control, and itself with no fixed controls.
- The checked Figure 7 circuit is
  `T(x₁,x₂;x₅); T(x₅,x₃;x₄); T(x₁,x₂;x₅)`. On `x₅=false` it realizes the four-bit AND/NAND gate
  and returns `x₅` to `false`.
- For order `n ≥ 4`, a forward prefix-conjunction chain in `n-3` zero work bits, one target gate,
  and the reversed chain realizes the full positive-control gate and restores all work bits.
- Reusing two persistent true enable bits and `n-3` zero work bits across the entire atomic word
  gives `2 + (n-3)` clean auxiliary wires: two for `n=1,2,3`, and `n-1` for `n≥3`.

## Updated Assumptions

- State the main theorem in a clean-face normal form: one ambient one-to-one circuit maps the
  source face with fixed auxiliary word exactly to the target face with the same word, and the
  retained data output is the requested permutation.
- A placed three-bit instruction must carry enough distinct-coordinate evidence to be lowered to
  the single canonical `AndNand.thetaSucc 2` using identity extension and coordinate reindexing.
- The full construction may use one final restriction and certified deletion, but no garbage:
  every auxiliary component is returned to its initial constant.
- The paper's `2n-3` bound is asserted only for `n≥3`; it is loose relative to the verified
  `n-1` construction there and is false at `n=1,2`. Zero arity is a separate identity theorem.

## Big Picture Objective

Prove that the canonical three-bit Toffoli gate is universal for finite Boolean permutations under
the explicitly qualified operations of one-to-one composition, fixed constants/face restriction,
and certified dummy deletion, with a checked clean auxiliary bank and exact resource accounting.

## Detailed Implementation Plan

- Add a cheap `FaceRealizes`/`CleanRealizes` semantic certificate with serial composition, exact
  face-membership, `restrictFaces`, and `RightDummy.deleteRight` bridges.
- Define placed three-bit instructions and a left-to-right list evaluator. Prove each instruction
  is a reindexed identity extension of the canonical three-bit gate and can be lowered to
  `OneToOneCircuit`.
- Prove clean NOT and CNOT gadgets from the two persistent true enables.
- Implement the prefix-conjunction compiler for generalized positive-control gates, including
  Figure 7 as the first nontrivial case, and prove work restoration and target behavior.
- Compile arbitrary atomic edges using two-sided data NOT masks around the positive-control gate;
  prove the shared constant bank is restored.
- Fold atomic realizations over `AtomicWord.exists_eval_eq` in the only leaf importing heavy
  decomposition, yielding the main clean universality theorem and the restriction/deletion
  corollaries.
- Prove auxiliary-cardinality formulas and the corrected comparison with `2n-3`.
- Prove a structural one-clean-auxiliary obstruction at two data bits (for example via the
  at-most-one-true invariant), rather than relying only on exhaustive enumeration.

## Build Structure

- `Synthesis/FaceRealization`: low-dependency semantic certificate over component operations.
- `Circuit/ThreeBit`: placed canonical gate, serial word, and evaluator.
- `Circuit/ThreeBitLowering`: proof-side range/complement lowering into `OneToOneCircuit`.
- `Synthesis/MultiControl`: prefix computation/uncomputation and resource proof.
- `Synthesis/Atomic`: polarity masks and clean atomic realization.
- `Synthesis/Universality`: heavy leaf importing `Perm.Decomposition` and folding witnesses.
- `Synthesis/Obstruction`: low-weight no-go result, independent of heavy decomposition.
- `Audit/UniversalityBoundary` and `Audit/Axioms/Universality`: diagnostics only.
- Only final glue imports decomposition; no synthesis, parity, or smooth dependency flows downward
  into finite, gate, cube, or component cores.

## No-Cheating Checks

- The main result returns an actual circuit made from placed canonical three-bit gates, not merely
  an ambient permutation asserted to exist.
- Fixed inputs and returned constant outputs are both named; deletion requires a `RightDummy`
  certificate.
- Exhaustive Figure 7/low-arity checks validate conventions but do not replace the all-arity clean
  compiler proof.
- The auxiliary count is proved from the index types used by the circuit and is not inferred from
  a diagram.
- “Universal” is always qualified by constants, restriction, and deletion; no ancilla-free result
  is implied.

## Boundary Checks

- Arity zero uses the unique identity permutation and no auxiliary wires.
- Arity one and two use two true enables, contradicting the paper's literal low-arity bound.
- Arity three may use the uniform two-enable bank even when a particular gate needs none; the
  theorem states a sufficient shared bank, not minimality.
- Every prefix work coordinate is distinct from data, target, enables, and other work coordinates.
- Serial composition order agrees with `AtomicWord.eval` and `Equiv.trans`.

## Completion Requirements

- Clean realization and lowering of placed three-bit circuits compile.
- Generalized gates and arbitrary atoms have proved clean circuits with an explicit auxiliary
  word.
- Every `BoolPermN n` has the stated qualified realization, including a separate `n=0` result.
- Restriction and certified-deletion corollaries expose the paper's permitted operations.
- Exact auxiliary cardinality and corrected `2n-3` comparison compile; C-009, C-015, C-016, and
  C-017 are updated with evidence.
- Figure 7, low arities, axiom audit, scans, diff checks, focused/adjacent builds, and the finite-
  block milestone full build all pass and are recorded.

## Stage Results

- Pending.
