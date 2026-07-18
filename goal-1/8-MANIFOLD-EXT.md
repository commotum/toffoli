# 8-MANIFOLD-EXT

Status: in progress.

## Current Facts

- `CircleExtension.CirclePower n` is a right-nested product of `n` analytic complex circles, with
  a singleton smooth zero-fold product.  `coord`, `embed`, and `circlePowerModel` fix its
  coordinate and manifold conventions.
- `CircleExtension.gateDiffeomorph m` is the corrected canonical-last smooth extension of
  `AndNand.thetaSucc m`; its Boolean interpolation theorem is already proved.
- `AtomicWord.decompose p` gives a chosen left-to-right word of literal Boolean cube-edge atoms
  for every `BoolPermN n` and `AtomicWord.eval_decompose` proves its semantics.
- `CirclePower` is not a Pi type.  Arbitrary target coordinates therefore require proved smooth
  coordinate projection/assembly or recursive product reindexing; no missing Pi-manifold instance
  may be assumed.
- Theorem 4.1 is existential in the connected manifold.  Exhibiting complex `Circle` suffices;
  connectedness alone is not being asserted to make every connected manifold universal.
- Theorem 5.3 needs more than Boolean interpolation: a smooth circuit restricted to fixed
  auxiliary circle points must preserve that whole smooth face and induce a diffeomorphism after
  deletion.  It must not be identified off the Boolean cube with the paper's ambiguous higher
  `Θ` formula.

## Updated Assumptions

- Build a direct smooth extension of each literal Boolean atom on `CirclePower n`.  For base
  pattern `b` and target `t`, multiply literal selector signals over every coordinate except `t`
  and update only `t` by inversion times the corresponding phase.
- Use recursive `ofFn` assembly and coordinatewise smoothness lemmas to make arbitrary-coordinate
  maps robust.  Keep coordinate infrastructure below atomic and decomposition leaves.
- Package each atomic map as a self-inverse `Diffeomorph`; compose the chosen atomic word in the
  same left-to-right convention as `AtomicWord.eval`.
- State a dedicated interpolation predicate linking a finite Boolean permutation to a smooth
  diffeomorphism; do not coerce or conflate the two types.
- The primary main theorem exhibits `M = Circle` and its recursive products.  Any generic
  atomic-extension interface is optional and must have hypotheses strong enough to construct the
  maps; bare connectedness is not enough by fiat.

## Big Picture Objective

Prove that every finite Boolean permutation has a diffeomorphic extension on the corresponding
product of the connected circle, including empty and low arities, and reconstruct the strongest
correct smooth three-bit qualified universality theorem justified by stable fixed auxiliary
faces.

## Detailed Implementation Plan

- Add a low-level recursive coordinate assembly equivalence for `CirclePower`; prove coordinate
  round trips, extensionality, smooth projections, and smooth assembly from finitely many smooth
  component functions.
- Define positive/negative literal signals and the all-other-coordinate activation product for an
  atomic edge; prove its Boolean value, smoothness, and invariance under the target update.
- Define the arbitrary-target atomic map; prove non-target/target coordinate laws, involution,
  smoothness, diffeomorphism packaging, and exact interpolation of `AtomicStep.perm`.
- Define left-to-right composition of smooth atomic diffeomorphisms and prove interpolation of an
  atomic word.  Keep the only `Perm.Decomposition` import in a final heavy `FromAtoms` leaf.
- Define the chosen extension of any `BoolPermN n`; prove the main interpolation theorem and an
  existential theorem explicitly exhibiting the connected circle model.  Handle `n=0`
  deliberately.
- Separately lift placed three-bit words to smooth diffeomorphisms and investigate a stable-face
  certificate strong enough to restrict and delete fixed auxiliary circle coordinates.  Prove a
  qualified Theorem 5.3 result if the compiler's compute/uncompute structure supplies that
  certificate; otherwise record the exact missing invariant rather than asserting off-cube
  equality.

## Build Structure

- `Smooth/CircleCoordinates`: low-level recursive tuple assembly and smooth coordinate lemmas.
- `Smooth/CircleAtomic`: literal selectors, arbitrary atomic map, diffeomorphism, interpolation.
- `Smooth/AtomicWord`: cheap serial smooth-word evaluator and induction theorem, without arbitrary
  permutation decomposition.
- `Smooth/Extension`: deliberately heavy terminal leaf importing `Perm.Decomposition` and
  producing the main theorem.
- Any smooth three-bit stable-face construction belongs in separate `Smooth/Synthesis/*` leaves so
  direct extension users do not import it.
- Diagnostics and axiom output stay in `Audit/*`; no internal leaf imports `Toffoli.Smooth` or the
  root umbrella.
- Focused builds will target each new leaf immediately.  Adjacent builds cover only its next
  consumer.  A milestone full smooth/public build is justified only after the main theorem is
  added to the public facade/root.

## No-Cheating Checks

- Do not define the smooth extension by finite-case interpolation on isolated Boolean points; it
  must be a globally smooth, proved bijective map.
- Do not use the finite permutation as the state or inverse of the smooth map.
- Do not assume a finite-Pi manifold instance, smooth arbitrary reindexing, or connected-manifold
  transitivity without a compiled theorem.
- Do not infer a diffeomorphism from smoothness alone; prove inverse laws and smooth inverse.
- Do not call an ambient smooth circuit's output projection a restriction/deletion unless the
  entire fixed smooth face is preserved and the induced map has a smooth inverse.
- Do not interpret the existence theorem as physical realizability.

## Boundary Checks

- At `n=0`, `CirclePower 0` and `BoolVec 0` are singleton; the extension must be identity without
  manufacturing a target coordinate.
- At `n=1`, an atomic gate has an empty activation product and extends NOT.
- Positive and negative literal selectors must agree with the exact `false→1`, `true→-1`
  convention.
- Atomic smooth composition order must match list-head-first `Equiv.trans` semantics.
- Non-target coordinate preservation is both a component-structure theorem and the key inverse
  invariant.
- The final theorem must say “there exists a connected manifold (the circle),” not “every
  connected manifold works.”

## Completion Requirements

- Coordinate assembly/projection and their smoothness lemmas compile for all arities.
- Every `AtomicStep (Fin n)` has a smooth self-inverse diffeomorphism with exact Boolean
  interpolation and component laws.
- Smooth atomic-word evaluation and arbitrary-permutation extension theorems compile in the
  documented composition order, including arity zero.
- The main theorem exposes a `Diffeomorph` on `CirclePower n`, the Boolean embedding, and the
  connected circle witness without conflating these objects.
- The strongest proved disposition of Theorem 5.3 and C-022 is recorded; any fixed-face/delete
  theorem names every constant and stability hypothesis.
- Focused/adjacent builds, boundary tests, import-direction scans, main-result axiom audit,
  milestone smooth build, and `git diff --check` pass.
- The paper map, correction log, dependencies, and public facade are updated.

## Stage Results

- Pending.
