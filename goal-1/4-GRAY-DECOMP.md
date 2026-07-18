# 4-GRAY-DECOMP

Status: complete.

## Current Facts

- `BoolPerm ι` is `Equiv.Perm (BoolWord ι)`, and serial composition uses `Equiv.trans`: the left
  permutation acts first.
- `AndNand.thetaSucc n` is the all-other-controls gate on `Fin (n + 1)` and is self-inverse.
- Mathlib supplies literal swaps `Equiv.swap`, finite-permutation induction/factorization, and list
  products, but the source audit found no ready-made hypercube path endpoint-swap theorem.
- The paper omits the exact palindromic edge-swap word. A correct path
  `v₀,v₁,...,vₖ` exchanges the endpoints with
  `s₀; s₁; ...; sₖ₋₁; sₖ₋₂; ...; s₀`, where `sᵢ` swaps `vᵢ,vᵢ₊₁` and semicolon means first-then-second.
- `Cube.Basic` now owns cheap bit flips, masked componentwise NOTs, and adjacency. `Cube.Path`
  proves connectivity by induction on the finite difference-set cardinality without importing the
  generalized gate family.
- `IsEndpointWord` records the exact recursive palindrome, and `AtomicWord.eval` makes list-head-
  first serial order part of the public theorem statement.

## Updated Assumptions

- Define an atomic Boolean edge permutation as the literal swap of a word and that word with one
  target bit flipped. This makes support and involution cheap and gives Gray decomposition a stable
  interface independent of gate synthesis.
- Construct the needed path by decreasing the finite set of differing coordinates. A canonical
  ordered vertex list and a no-duplication theorem were not added because neither is consumed by
  endpoint transposition or arbitrary-permutation decomposition; this keeps the public dependency
  surface smaller under `BUILD-PLAN.md`.
- Keep the cheap atomic-word witness/interface below heavy permutation factorization. Executable
  low-arity checks stay in audit leaves.

## Big Picture Objective

Prove that every finite Boolean permutation is an explicitly ordered finite serial product of
atomic edge transpositions, including exact endpoint-swap and low-arity behavior, and connect the
standard all-other-controls Toffoli gate to one such atom.

## Detailed Implementation Plan

- Add `Toffoli.Gate.Atomic` with word bit-flip, cube adjacency, literal edge swap, endpoint/support
  laws, and the all-true AND/NAND bridge.
- Add a narrow cube-path module defining the canonical differing-coordinate path and proving its
  endpoints, adjacency, and no-duplication properties required downstream.
- Add `Toffoli.Perm.AtomicWord` for an explicit serial word/list evaluator and the palindromic
  endpoint-transposition word.
- Add `Toffoli.Perm.Decomposition` as the heavy leaf combining finite-permutation transposition
  factorization with the endpoint construction.
- Add low-arity direction/exhaustive checks and an axiom audit under `Toffoli.Audit`; keep them out
  of all public imports.
- Expose a thin `Toffoli.Decomposition` facade only after focused leaves pass.

## Build Structure

- Cheap leaf: `Gate/Atomic`, importing the gate family plus literal-swap basics.
- Path leaf: `Cube/Path`, importing only finite sets/lists and Boolean definitions.
- Word evaluator/proof leaf: `Perm/AtomicWord`, importing the two cheap leaves.
- Heavy proof leaf: `Perm/Decomposition`, importing exact finite-permutation factorization APIs.
- Diagnostic leaves: `Audit/GrayBoundary` and `Audit/Axioms/Decomposition`.
- Internal leaves never import `Toffoli.Gate`, `Toffoli.Decomposition`, or root facades.
- Build in the order above with `+Module:olean`. A milestone root/full build is required at facade
  promotion because the decomposition is a major dependency boundary.

## No-Cheating Checks

- Small exhaustive evaluation may validate word direction but cannot replace the general proof.
- The endpoint theorem must state the actual list/product and serial-composition convention.
- Atomic means a literal two-vertex swap; a lower-control gate replicated across unused fibers is
  not silently classified as one atom.
- The arbitrary-permutation theorem must derive from a checked finite-permutation induction or
  factorization theorem, not an asserted generating-set axiom.

## Boundary Checks

- Arity zero yields only the identity permutation and an empty atomic word.
- A bit flip requires an actual target coordinate, so there is no atom on an empty index type.
- Path construction handles equal endpoints separately and never assumes a nonempty difference set.
- No parity, synthesis, topology, manifold, or smooth import enters this stage.
- Heavy factorization and exhaustive checks do not flow back into gate or finite core modules.

## Completion Requirements

- Atomic edge endpoints, fixed points, symmetry, and Toffoli interpretation are proved.
- The canonical path has checked endpoints/adjacency and the endpoint word has exact evaluation.
- Every finite Boolean permutation has a finite atomic decomposition with documented order.
- Arity `0`, `1`, and `2` results/checks compile.
- Focused leaf/audit/axiom builds, facade/root milestone builds, scans, and `git diff --check` pass.
- C-005 and C-021 are resolved or revised with exact Lean evidence, and the paper map is updated.

## Stage Results

- Added `Toffoli.Cube.Basic`, `Toffoli.Cube.Path`, `Toffoli.Gate.Atomic`,
  `Toffoli.Perm.AtomicWord`, and the heavy leaf `Toffoli.Perm.Decomposition`.
- `atomicEdge x target` is the literal swap of `x` and `x.flipAt target`; endpoint, support,
  involution, orientation, and adjacency laws are proved.
- `IsEndpointWord.eval_eq_swap` verifies the exact palindrome. `AtomicWord.exists_eval_eq` then
  uses `Equiv.Perm.swap_induction_on` to decompose every finite Boolean permutation, with list
  entries acting from left to right. The chosen `AtomicWord.decompose` has correctness theorem
  `eval_decompose`.
- C-021 is resolved by `edgeNormalizer_permCongr_atomicEdge` and
  `atomicEdge_eq_edgeNormalizer_permCongr_andNand`: arbitrary zero/one-pattern atoms require the
  same componentwise NOT mask both before and after the canonical AND/NAND atom.
- `Toffoli.Audit.GrayBoundary` checks arity zero, one-bit atoms, and every input to the explicit
  two-bit palindrome `00 → 10 → 11`; it also instantiates the general theorem at arities one and
  two.
- Focused builds passed. The promoted facade/root/audit build passed with 943 jobs, and the warm
  milestone `lake build` passed with 940 jobs in 1.41 s. Separating `Cube.Basic` reduced the cheap
  cube leaf to 314 jobs; only `Perm.Decomposition` imports `Mathlib.GroupTheory.Perm.Sign`.
- `Toffoli.Audit.Axioms.Decomposition` reports only `propext`, `Classical.choice`, and
  `Quot.sound`. Placeholder, broad-import, and whitespace scans passed.
