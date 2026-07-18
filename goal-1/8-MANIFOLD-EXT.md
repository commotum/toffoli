# 8-MANIFOLD-EXT

Status: complete.

## Current Facts

- `CircleExtension.CirclePower n` is a right-nested product of `n` analytic complex circles with
  a singleton smooth zero-fold product.  `circlePowerModel`, `coord`, `assemble`, `coordEquiv`, and
  `embed` give a proved component API rather than assuming a finite-Pi manifold instance.
- `coord_assemble`, `assemble_coord`, `coord_ext`, `contMDiff_coord`, `contMDiff_assemble`, and
  `contMDiff_iff_coord` establish coordinate round trips, extensionality, smooth projections, and
  coordinatewise smooth assembly at every arity.
- `literalSignal` and `atomicActivation` form a direct finite product over all non-target
  coordinates.  `atomicMap` changes only its target, preserves its activation, is smooth and
  involutive, and is packaged as the self-inverse `atomicDiffeomorph`.
- `Interpolates F p` is the explicit relation between a finite `BoolPermN n` and a separate
  `Diffeomorph` of `CirclePower n`.  `atomicDiffeomorph_interpolates` and
  `evalAtomicWord_interpolates` prove this relation for an atom and a serial word without
  identifying the finite and smooth maps.
- `extension p` evaluates the chosen `AtomicWord.decompose p` in the same head-first serial order
  as the finite word.  `extension_interpolates`, `exists_extension`, and
  `connected_circle_witness` prove the arbitrary-permutation result using the connected complex
  circle; no theorem asserts that bare connectedness makes every connected manifold universal.
- Placed three-bit gates have their own smooth evaluator `evalThreeBitWord`.  The replacement,
  reindexing, avoidance, and `ChangesOnlyAt` theorems in `ThreeBitStability` prove component
  stability for arbitrary circle-valued inputs, not merely for embedded Boolean inputs.
- `insertUniversal` fixes two enable circles at `boolPoint true` and the work circles at
  `boolPoint false`; `projectUniversal` deletes them.  `PreservesUniversalAux` records global
  preservation of each named auxiliary coordinate and is strong enough to build the genuine
  restricted diffeomorphism `restrictUniversal`.
- The chosen ambient three-bit circuit globally preserves the entire auxiliary bank.
  `ambient_insert_eq_insert_restricted` therefore holds on the whole smooth face, while
  `restricted_interpolates` and `exists_qualified_smooth_realization` give the corrected qualified
  three-bit result with constants, restriction, and deletion explicit.

## Updated Assumptions

- The concrete witness for the paper's existential manifold is mathlib's analytic complex
  `Circle`, with Boolean points `false ↦ 1` and `true ↦ -1`.  The theorem does not quantify over
  every connected manifold and does not infer a generic atomic action from connectedness alone.
- The paper's nonassociative binary circle operation is not used to define arbitrary atomic
  controls.  A direct finite product of smooth literal signals supplies a representative-free,
  unambiguous extension with the required Boolean values.
- Direct arbitrary-permutation extension and three-bit synthesis are separate constructions.
  They agree with the same Boolean permutation on embedded points, but no off-cube equality
  between them or with an ambiguous higher-arity paper `Θ` is claimed.
- Smooth restriction/deletion requires a stable face in both directions.  Global auxiliary
  coordinate preservation supplies this evidence for the ambient circuit and its inverse; output
  projection alone would not suffice.
- The uniform three-bit compiler uses `auxCount n = 2 + (n - 3)`: two `true` enable constants and
  `n - 3` `false` work constants, all returned unchanged.  Thus it uses two auxiliaries for
  `n ≤ 3`, `n - 1` for `3 ≤ n`, and satisfies the paper's `2n - 3` bound only for `3 ≤ n`.
  Arity zero additionally has a separate no-auxiliary identity witness.
- Existence of these diffeomorphisms remains distinct from physical realizability; no gears,
  cams, energy model, or mechanism is part of the verified result.

## Big Picture Objective

Prove that every finite Boolean permutation has a diffeomorphic extension on the corresponding
product of the connected circle, including empty and low arities, and reconstruct the strongest
correct smooth three-bit qualified universality theorem justified by stable fixed auxiliary
faces.  Both goals are now met with the direct and qualified constructions kept distinct.

## Detailed Implementation Plan

- Build a recursive coordinate assembly equivalence for `CirclePower`, including round trips,
  extensionality, smooth projections, and coordinatewise smooth assembly.
- Define positive and negative literal signals and the all-other-coordinate activation product;
  prove its Boolean value, smoothness, and invariance under the target update.
- Define the arbitrary-target atomic map; prove its target and non-target coordinate laws,
  involution, smoothness, diffeomorphism packaging, and exact atomic interpolation.
- Compose smooth atoms in the verified left-to-right word convention, then isolate arbitrary
  permutation decomposition in the heavy `Smooth/Extension` terminal leaf.
- Lift placed three-bit instructions, reindexing, and compute/update/uncompute stability to circle
  products.  Flatten the verified discrete compiler without changing its semantics.
- Define the fixed universal smooth face, prove global auxiliary preservation, construct its
  induced data diffeomorphism, and state the qualified result with every constant, restriction,
  projection, and interpolation certificate visible.

## Build Structure

- `Smooth/CircleCoordinates` contains only the recursive coordinate equivalence and smooth
  projection/assembly API above `CircleModel`.
- `Smooth/CircleAtomic` contains literal selectors, arbitrary-target atomic maps,
  diffeomorphisms, component laws, and the `Interpolates` relation.
- `Smooth/AtomicWord` is the cheap serial evaluator and interpolation induction; it imports
  `Perm.AtomicWord` but not arbitrary-permutation decomposition.
- `Smooth/Extension` is the deliberately heavy direct terminal leaf.  It alone adds
  `Perm.Decomposition` to the direct path and exposes `extension`, `exists_extension`, and the
  connected-circle witness.
- `Smooth/ThreeBitCircuit`, `Smooth/ThreeBitStability`, `Smooth/UniversalLayout`, and
  `Smooth/UniversalFace` isolate placed-gate evaluation, component stability, flat index layout,
  and smooth-face restriction below the terminal synthesis proof.
- `Smooth/Synthesis/FlatCircuit` transports nested universal instructions to consecutive
  `Fin (n + auxCount n)` coordinates.  `Smooth/Synthesis/AtomicStability` proves the compiler's
  local stability without importing arbitrary permutation decomposition.
- `Smooth/Synthesis/Universality` is the separate heavy terminal leaf combining the finite
  arbitrary-permutation compiler with those stability results.
- The public `Toffoli.Smooth` facade imports exactly `Toffoli.Smooth.Extension` and
  `Toffoli.Smooth.Synthesis.Universality`.  The discrete root `Toffoli` does not import the smooth
  facade, so ordinary finite builds remain isolated from manifold dependencies.
- Boundary checks and `#print axioms` diagnostics live only in `Audit/*`; no implementation leaf
  imports an audit, the smooth facade, or the root umbrella.

## No-Cheating Checks

- The extension is a globally smooth composition of explicitly self-inverse smooth atomic maps;
  it is not finite-case interpolation on isolated Boolean points.
- The finite permutation is neither the state space nor the inverse of the smooth map; the two
  types are related only by `Interpolates`.
- No finite-Pi manifold instance, arbitrary smooth reindexing, or connected-manifold transitivity
  is assumed.  All needed coordinate assembly and reindexing maps have compiled proofs.
- Every claimed diffeomorphism carries proved forward and inverse smoothness and two-sided inverse
  laws; smoothness alone is never used as bijectivity.
- `restricted` is constructed only after proving global preservation of every fixed auxiliary
  coordinate for the ambient circuit and its inverse.  Projection is not passed off as deletion
  without that certificate.
- Neither the direct existence theorem nor qualified three-bit synthesis is interpreted as a
  mechanically or physically realizable device.

## Boundary Checks

- At `n = 0`, `extension_zero_eq_refl` and `refl_zero_interpolates` identify the direct extension
  with the identity of the singleton empty product.  The uniform three-bit word is empty,
  `ambient_zero_eq_refl` and `restricted_zero_eq_refl` hold, and
  `exists_zero_extension_noAux` supplies the sharper zero-auxiliary witness.
- At `n = 1`, the erased activation product is `1`, so the sole atomic coordinate is smoothly
  negated; `SmoothExtensionBoundary` checks both Boolean endpoints and the circle coordinate
  formula.
- `boolPoint false = 1` and `boolPoint true = -1`; `literalSignal_boolPoint` selects the requested
  value exactly.  The two enables are fixed at `true`, while every work coordinate is fixed at
  `false`.
- `evalAtomicWord` and `evalThreeBitWord` use head-first serial composition.  Their append laws and
  boundary examples pin the convention to the corresponding finite evaluators.
- `coord_atomicMap_of_ne`, `ThreeBitWordAvoids`, `ChangesOnlyAt`, and
  `PreservesUniversalAux` separately record non-target/data/auxiliary component behavior.
- `auxiliary_card_eq_two` covers `n ≤ 3`; `auxiliary_card_eq_sub_one` and
  `auxiliary_card_le_paper_bound` require `3 ≤ n`.  No negative or false low-arity reading of the
  paper's bound is exposed.
- `connected_circle_witness` says that the exhibited circle is connected and a manifold and that
  an extension exists on its product; it does not claim the result for every connected manifold.

## Completion Requirements

- [x] Coordinate assembly/projection and their smoothness lemmas compile for all arities.
- [x] Every `AtomicStep (Fin n)` has a smooth self-inverse diffeomorphism with exact Boolean
  interpolation and component laws.
- [x] Smooth atomic-word evaluation and arbitrary-permutation extension theorems compile in the
  documented composition order, including arity zero.
- [x] The main theorem exposes a `Diffeomorph` on `CirclePower n`, the Boolean embedding, and the
  connected circle witness without conflating these objects.
- [x] Theorem 5.3/C-022 is resolved by a stable whole-face theorem and a qualified
  restriction/deletion theorem naming all constants and certificates.
- [x] Focused terminal builds, boundary checks, import-direction scans, main-result axiom audits,
  the public smooth facade build, proof-hole scans, and `git diff --check` pass.
- [x] The Stage 8 result records the source correction, boundary behavior, dependency layering,
  public declarations, and remaining scope limitations for final integration.

## Stage Results

### Recursive coordinates and direct atomic extensions

- `assemble`, `coord_assemble`, `assemble_coord`, `coordEquiv`, and `coord_ext` give a total
  coordinate API for the recursive product.  `contMDiff_coord`, `contMDiff_assemble`, and
  `contMDiff_iff_coord` prove its smooth universal property without a finite-Pi manifold shortcut.
- `literalSignal_boolPoint` proves exact positive/negative Boolean selection.
  `atomicActivation_embed` identifies the product with the all-non-target-controls predicate, and
  `contMDiff_atomicActivation` proves its smoothness.
- `coord_atomicMap_target` and `coord_atomicMap_of_ne` expose component structure;
  `atomicActivation_atomicMap` is the inverse invariant.  `contMDiff_atomicMap` and
  `atomicMap_involutive` justify `atomicDiffeomorph`, while
  `atomicDiffeomorph_interpolates` proves exact agreement with `atomicEdge`.

### Direct arbitrary-permutation extension

- `evalAtomicWord`, `evalAtomicWord_append`, and `evalAtomicWord_interpolates` lift a finite atomic
  word in the verified head-first order.
- `extension p := evalAtomicWord (AtomicWord.decompose p)` is the chosen direct extension.
  `extension_interpolates` is the main pointwise theorem and `exists_extension` its existential
  form.
- `connected_circle_witness` explicitly packages connectedness and the manifold instance of the
  complex circle with the extension witness.  `extension_zero_eq_refl` and
  `refl_zero_interpolates` settle the empty product rather than manufacturing a target.

### Placed three-bit stability and smooth-face restriction

- `threeBitDiffeomorph` and `evalThreeBitWord` interpret placed copies of the corrected smooth
  three-bit gate; `evalThreeBitWord_interpolates` connects that evaluator to the discrete circuit.
- `replaceCoord`, `ThreeBitWordAvoids`, and `ChangesOnlyAt`, together with
  `evalThreeBitWord_replaceCoord`, `evalThreeBitWord_append_cons_reverse_changesOnlyAt`, and the
  reindexing theorems, establish off-cube component stability of the compiler gadgets.
- `universalIndexFinEquiv`, `flatDataIndex`, `flatEnableIndex`, `flatWorkIndex`, and
  `flatUniversalInput` prove the exact transport between nested discrete resources and consecutive
  circle coordinates.
- `insertUniversal`, `projectUniversal`, and `OnUniversalFace` define the smooth face.
  `projectUniversal_insertUniversal`, `insertUniversal_projectUniversal_iff`, and their smoothness
  theorems prove insertion/projection behavior.
- `PreservesUniversalAux`, its serial and inverse closure theorems, and `restrictUniversal`
  reconstruct a genuine face diffeomorphism.  This keeps restriction to fixed values distinct
  from deletion by projection.
- `multiControlWord_changesOnlyAt`, `positiveWord_changesOnlyAt`,
  `positiveWord_preservesUniversalAux`, `notMaskWord_preservesUniversalAux`, and
  `atomicWord_preservesUniversalAux` prove the compute/update/uncompute stability certificate
  before arbitrary decomposition is imported.

### Qualified three-bit smooth universality and C-022

- `nestedWord`, `flatWord`, and `ambient` expose the selected compiler word and its ambient smooth
  evaluation.  `compileAtomicWord_preservesUniversalAux` and
  `ambient_preservesUniversalAux` prove global preservation of all enables and work coordinates;
  `ambient_symm_preservesUniversalAux` supplies inverse-face stability.
- `restricted` is the induced data `Diffeomorph`.  `ambient_insert_eq_insert_restricted` proves
  exact equality on the entire inserted smooth face, and `restricted_interpolates` proves the
  requested Boolean semantics.
- `exists_restricted_extension_from_threeBit` exposes the placed three-bit word, ambient
  diffeomorphism, preservation certificate, restriction, and interpolation.
  `exists_qualified_smooth_realization` additionally exposes the induced data diffeomorphism and
  whole-face equation.
- C-022 is resolved as a source-proof reconstruction and specification correction.  The paper's
  one-line “parallel” proof is replaced by global auxiliary stability and certified face
  restriction.  The result deliberately does not identify `restricted p` with `extension p`, or
  with the paper's ambiguous higher `Θ`, away from embedded Boolean points.  It proves qualified
  universality with fixed constants and returned auxiliaries, not ancilla-free universality.
- `auxiliary_card`, `auxiliary_card_eq_two`, `auxiliary_card_eq_sub_one`, and
  `auxiliary_card_le_paper_bound` carry the verified discrete resource accounting into the smooth
  theorem.  `flatWord_zero_eq_nil`, `ambient_zero_eq_refl`, `restricted_zero_eq_refl`, and
  `exists_zero_extension_noAux` make the empty-data boundary explicit.

### Validation, audit, and compile-time isolation

- Focused `lake build Toffoli.Smooth.Synthesis.AtomicStability` passed through 2,557 jobs; its leaf
  compiled in 2.5 seconds.
- Focused `lake build Toffoli.Smooth.Synthesis.Universality` passed through 2,563 jobs; its terminal
  leaf compiled in 3.1 seconds.
- Public `lake build Toffoli.Smooth` passed through 2,570 jobs.  The facade leaf compiled in
  2.3 seconds and the recorded build took 4.0 seconds wall time.
- The combined direct/qualified boundary and axiom-audit milestone passed through 2,572 jobs with
  cached audit output replayed.  `SmoothExtensionBoundary` and `SmoothSynthesisBoundary` cover
  empty/low arities, word order, component stability, whole-face behavior, theorem signatures,
  and resource counts.
- `Audit/Axioms/SmoothExtension` and `Audit/Axioms/SmoothSynthesis` report only the standard
  mathlib/Lean axioms `propext`, `Classical.choice`, and `Quot.sound` for every audited main result;
  there are no project-specific axioms.
- Proof-hole scans over the smooth implementation and its audits find no `sorry`, `admit`,
  `axiom`, or `unsafe`.  The public facade has exactly its two intended terminal imports, the
  discrete root has no reverse smooth import, and whitespace/diff checks pass.
