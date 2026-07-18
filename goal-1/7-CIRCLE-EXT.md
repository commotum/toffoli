# 7-CIRCLE-EXT

Status: complete.

## Current Facts

- Pinned mathlib supplies complex unit `Circle` as an analytic one-manifold and Lie group, with
  smooth inversion, multiplication, coercion to `ℂ`, and `Circle.exp : ℝ → Circle`.
- The source circle `ℝ/(2πℤ)` can be represented without choosing angle representatives: the
  complex unit-circle point `Circle.exp x` depends only on the angle modulo `2π`.
- The non-public `Audit.PaperCircleOperation` leaf proves that the paper's binary operation is
  invariant under independent `2πℤ` changes of angle representative and smooth, but neither
  associative nor left/right unital. Its iterated expression is therefore ambiguous; only the
  direct finite product of selector signals is used publicly.
- Pinned mathlib has robust binary product manifolds but no turnkey finite-Pi manifold and
  diffeomorphism API.  A right-nested product with a singleton zero-fold product avoids assuming
  missing infrastructure.
- Foundational implementation already exists in the narrow leaves `Smooth.CircleModel` and
  `Smooth.CircleGate`; focused builds and an axiom audit pass.

## Updated Assumptions

- Boolean `false` and `true` are embedded as complex-circle points `1` and `-1`, corresponding to
  angles `0` and `π`.
- For `n` controls, use the direct selector
  `controlProduct = ∏ i, (1 - re zᵢ)/2`; the empty product is `1`.
- The target formula is `z⁻¹ * Circle.exp (π * controlProduct)`.  Controls are unchanged, so
  the same formula is its inverse.
- This stage proves the canonical-last AND/NAND family only.  Arbitrary-coordinate assembly,
  atomic smooth gates, and composition into the main extension theorem belong to Stage 8.

## Big Picture Objective

Formalize a robust corrected version of the paper's explicit circle-valued smooth gate, proving
the precise Boolean convention, smoothness, involution/bijection, diffeomorphism packaging,
component preservation, and interpolation for every positive gate order including NOT.

## Detailed Implementation Plan

- Package the smooth carrier/model data for `Circle`, a singleton base, and recursive binary
  products.
- Define the Boolean embedding and prove coordinate recovery and injectivity.
- Define the representative-free selector on complex `Circle`; pull it back along `Circle.exp` to
  recover the paper's `(1-cos x)/2` formula.
- Define and prove smooth the corrected direct finite control product, including its empty fold and
  Boolean values.
- Define the target update, prove it involutive, smooth, bijective, and a diffeomorphism, and prove
  all controls remain fixed.
- Prove exact interpolation of `AndNand.thetaSucc` on the embedded Boolean cube.
- Add a diagnostic boundary leaf for zero controls/NOT and the `0,π` conventions, retain the
  axiom audit outside the public graph, and expose a thin `Toffoli.Smooth` facade.

## Build Structure

- `Smooth/CircleModel`: low-level recursive manifold products, Boolean embedding, selector, and
  direct control product.  It does not import finite decomposition, parity, or synthesis.
- `Smooth/CircleGate`: proof leaf importing the finite AND/NAND specification and diffeomorphism
  API; owns the smooth map and interpolation theorem.
- `Smooth.lean`: thin public facade importing only `CircleGate` at this stage.
- `Audit/CircleBoundary` and `Audit/Axioms/Circle`: diagnostic leaves, never publicly imported.
- Focused command:
  `lake build Toffoli.Smooth.CircleModel Toffoli.Smooth.CircleGate`.
- Adjacent commands:
  `lake build Toffoli.Smooth Toffoli.Audit.CircleBoundary Toffoli.Audit.Axioms.Circle`.
- Do not add `Toffoli.Smooth` to the root umbrella until the main smooth block is integrated; this
  avoids putting the 2500-job manifold graph on every discrete root build.  No full build trigger
  applies to this isolated facade.

## No-Cheating Checks

- No quotient representative or unchecked quotient lift appears in the implementation.
- The paper's nonassociative binary operation is not iterated or presented as a ring operation.
- `ContMDiff`, involution, and interpolation are separate proved obligations; smoothness is not
  treated as evidence of invertibility.
- The Boolean permutation and smooth diffeomorphism remain distinct objects linked only by an
  explicit embedding/interpolation theorem.
- No physical mechanism or realizability claim is derived.

## Boundary Checks

- `CirclePower 0` is the singleton zero-dimensional Euclidean space; the first actual gate has
  one target and zero controls.
- The zero-control direct product is `1`, so the smooth gate implements Boolean NOT.
- `signal (Circle.exp 0)=0` and `signal (Circle.exp π)=1`; the target convention is checked at
  both Boolean points.
- Recursive product order is controls first and target last, matching `Fin.castSucc`/`Fin.last` in
  `AndNand.thetaSucc`.
- Smooth imports must not appear in finite, gate, cube, permutation, parity, or synthesis leaves.

## Completion Requirements

- Recursive product, Boolean embedding, selector, and direct product definitions compile.
- Smoothness, involution, bijectivity, diffeomorphism packaging, and component laws compile.
- Generic Boolean interpolation and explicit zero-control boundary checks compile.
- The chosen complex-circle relationship to the paper's angular circle is documented by proved
  `Circle.exp` equations; no quotient well-definedness is assumed.
- Focused model/gate, public facade, boundary audit, and axiom audit builds pass.
- Axiom output contains no project-specific axioms; proof-hole/import-direction/diff scans pass.
- Results and corrections C-001, C-002, C-003, and C-023 are folded into `0-plan.md`.

## Stage Results

### Recursive model and corrected formula

- `CircleExtension.ManifoldSpace.circlePower` packages a singleton zero-fold product and
  right-nested binary products of complex unit circles.  It uses only manifold instances present
  in the pinned mathlib version and assumes no finite-Pi manifold API.
- `boolPoint`, `embed`, `coord`, and `embed_injective` implement the convention
  `false ↦ Circle.exp 0 = 1` and `true ↦ Circle.exp π = -1` and prove that the Boolean cube
  embeds injectively.
- `signal z = (1-re z)/2` is defined on the circle point itself, so representative independence is
  built in.  `signal_exp` proves that its angular pullback is exactly `(1-cos x)/2`.
- `controlProduct` is the corrected direct finite selector product, with empty product `1`.
  `contMDiff_controlProduct`, `controlProduct_eq_prod_signal`, and `controlProduct_embed` prove
  smoothness, its finite-product meaning, and the exact Boolean conjunction semantics.  The
  paper's nonassociative/unital binary-operation claim is not used.

### Smooth gate and interpolation

- `gate n` updates only the last target by
  `z⁻¹ * Circle.exp (π * controlProduct controls)`.  `gate_controls` and the coordinate laws
  prove component preservation.
- `gate_involutive`, `contMDiff_gate`, `gate_bijective`, and `gateDiffeomorph` prove the full
  inverse, smoothness, bijectivity, and diffeomorphism obligations separately.
- `gate_interpolates_thetaSucc` and its diffeomorphism-level wrapper prove exact equality with
  `AndNand.thetaSucc` after the Boolean embedding for every control count.  In particular, zero
  controls gives the one-bit NOT gate.

### Verification and dependency boundary

- `Toffoli.Audit.CircleBoundary` checks the singleton empty product, empty control product, both
  Boolean angle/signal conventions, NOT at both Boolean values, controls-first/final-target order,
  and the generic interpolation signature.
- Focused model/gate build passed through 2531 jobs; the new thin `Toffoli.Smooth` facade and
  boundary audit passed through 2533 jobs; the axiom audit passed through 2532 jobs.  The root
  `Toffoli.lean` was deliberately not changed, so ordinary discrete root builds remain on the
  962-job path until the main smooth theorem is integrated.
- `Toffoli.Audit.Axioms.Circle` reports only `propext`, `Classical.choice`, and `Quot.sound` for the
  embedding, direct product, smoothness, inverse, diffeomorphism, and interpolation results.
  Proof-hole/project-axiom/unsafe scans, reverse-import checks, warning review, and
  `git diff --check` pass.
- `Toffoli.Audit.PaperCircleOperation.paperMul_exp_add_periods`, `contMDiff_paperMul`,
  `paperMul_not_associative`, `paperMul_no_left_identity`, `paperMul_no_right_identity`, and
  `paperMul_no_identity` machine-check the rejected source
  operation in a terminal audit leaf. Its focused build passed in 5.05 s and its axiom audit in
  4.56 s; the audit is not imported by either public facade.
- Corrections C-001, C-002, C-003, and the recursive-product choice C-023 are now backed by Lean
  declarations.  Arbitrary-coordinate atomic diffeomorphisms and the main extension fold remain
  explicitly assigned to Stage 8.
