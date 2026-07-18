# Goal 1 — Bicontinuous Extensions in Lean 4

Shorthand goal: `TOFFOLI-LIB`

Status: complete. Stages `1-SOURCE-AUDIT` through `9-INTEGRATE-AUDIT` are verified.

## Big-Picture Objective

Build a correct, reusable Lean 4 library that independently reconstructs and verifies the mathematical content of “Bicontinuous Extensions of Invertible Combinatorial Functions.” The verified core should cover finite Boolean permutations, generalized Toffoli gates, exact decomposition and universality results, parity obstructions, reusable restriction/extension operations, and smooth extensions to products of a connected manifold (including the paper's explicit circle construction where it is mathematically sound).

The paper is a source of claims and ideas, not a formal specification. Every theorem must be restated with precise hypotheses and checked independently. Claims that need correction, stronger assumptions, or a weaker conclusion must be documented and traced from the paper statement to the Lean declaration.

## Non-Negotiable Constraints and No-Cheating Rules

- Pin compatible Lean 4 and mathlib versions and keep the project build reproducible.
- Completed modules must contain no `sorry`, `admit`, `by_contra!` without a closed proof, or unexplained project-specific axioms.
- Do not fabricate a declaration, proof, citation, paper equation, or mathlib API.
- Prefer existing mathlib structures for finite equivalences, finite bit vectors, smooth manifolds, smooth maps, circles or quotient groups, and diffeomorphisms when they fit the exact need.
- Independently verify the paper's constructions, decomposition arguments, smooth extensions, universality claims, and obstruction theorems.
- Preserve explicit distinctions between:
  - a finite permutation and any smooth extension of it;
  - ordinary function/equivalence composition and one-to-one circuit composition;
  - fixing input coordinates, restricting a map, and deleting dummy output components;
  - existence of a diffeomorphic extension and physical realizability;
  - unrestricted universality and universality that uses ancillas, fixed constants, restrictions, or dummy-variable deletion.
- Keep gears, cams, energy, and other physical-language claims outside the verified core unless an explicit physical model is separately defined and justified.
- Cover arity zero and low-arity cases deliberately; never rely on an implicit nonempty finite type.
- State Boolean conventions and chosen embedded circle points explicitly.
- Do not accept a circle operation expressed on angle representatives until well-definedness modulo the period is proved.
- For every involutive smooth extension introduced, prove smoothness, the interpolation property,
  bijectivity, the inverse law, and preservation of the claimed component structure.
- For Gray-code decomposition, record the exact order and composition convention and test it in small dimensions.
- For parity and three-bit universality results, make all arity, ancilla, fixed-constant, restriction, and dummy-coordinate counts explicit.
- Keep a paper-to-Lean claim map, correction/unresolved-point log, dependency record, and axiom audit current as the formalization advances.
- Follow the incremental-build principles in repository-root `BUILD-PLAN.md`: narrow imports, low-dependency core definitions, heavy proof and audit leaves, thin public APIs, and the smallest build that covers each change.
- Avoid editing high-fanout modules for convenience. Avoid broad global simp lemmas, instances, notation, or umbrella imports unless the stage establishes a concrete need.
- Do not redefine success as a convenient subset of the paper. Unsupported or false claims may be corrected or decisively rejected, but the disposition and evidence must be recorded.

## Verified Project and Mathematical Facts

- The repository contains the paper as `toffoli-1981/toffoli-1981.md` and `toffoli-1981/toffoli-1981.pdf`, together with extracted figures. The Markdown identifies it as Tommaso Toffoli, *Mathematical Systems Theory* 14 (1981), 13–23.
- Repository-root `BUILD-PLAN.md` defines the mandatory incremental Lean build discipline for this goal.
- The repository also contains a minimal Python/uv shell (`pyproject.toml`, `uv.lock`, and `main.py`). The Lean project is isolated under `formal/`.
- `formal/lean-toolchain` pins Lean 4.32.0. `formal/lakefile.toml` pins mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`, and the generated manifest records that exact revision.
- The Stage 1 smoke leaf imports only `Mathlib.Logic.Equiv.Basic`; focused, root-target, and initial full builds pass.
- The PDF has 11 scan pages corresponding to printed pages 13–23. The principal formal claims are Definition 4.1, Lemmas 4.1–4.2, Theorem 4.1, and Theorems 5.1–5.3.
- `Toffoli.Audit.PaperCircleOperation` machine-checks that the binary circle operation in Lemma
  4.2 is invariant under independent `2πℤ` representative changes and smooth, but is not
  associative and has no left, right, or two-sided identity, contrary to the paper's “all ring
  axioms except distributivity” assertion. The verified smooth gate instead uses the direct finite
  control product.
- Printed page 21 contains two source errors in Theorem 5.2's proof: it cites Figure 4 rather than Figure 7 and writes the restriction face as `B³ × {0}` although the displayed five-wire construction fixes one wire and retains four, so it must be `B⁴ × {0}`.
- The finite core is implemented and verified. It uses generic indexed Boolean words and finite
  aliases, distinguishes coordinate wiring from gate conjugation, provides disjoint tensoring and
  resource-free one-to-one circuit syntax, and separates exact face restriction, singleton-factor
  deletion, and certificate-driven semantic dummy deletion.
- Generalized positive-control Toffoli gates are implemented as explicit involutive permutations.
  The paper family is `AndNand.thetaSucc n : BoolPermN (n + 1)` (parameter = control count), and
  reindexing/unused-coordinate placement agree definitionally at the specification level and by
  proved equality at the permutation level.
- Exact Gray decomposition is implemented. Atomic instructions are literal cube-edge swaps,
  endpoint transpositions use a checked recursive palindrome in documented left-to-right order,
  and `AtomicWord.exists_eval_eq` decomposes every finite Boolean permutation. Arbitrary edge
  patterns are related to the AND/NAND family by proved two-sided masked-NOT conjugation.
- The lower-arity obstruction is implemented with exact sign accounting. Proper identity
  extensions are even, bare coordinate wiring is even from three bits onward, and the complete
  paper generator subgroup is nonuniversal. The exceptional two-bit case is proved separately by
  a global-complement invariant; arities zero and one have explicit dispositions.
- Qualified three-bit universality is implemented.  Every `BoolPermN n` has a clean
  `OneToOneCircuit` over the sole canonical three-bit atom on
  `Fin n ⊕ (Fin 2 ⊕ Fin (n-3))`; the two enables are fixed `true`, work bits are fixed `false`,
  and the same word is returned.  Typed face restriction and certified dummy deletion recover the
  requested permutation.  The exact auxiliary count is two for `n ≤ 3` and `n-1` for `n ≥ 3`;
  the paper's `2n-3` bound is proved only for `n ≥ 3`, with a separate no-auxiliary arity-zero
  theorem and a structural one-auxiliary obstruction at two data bits.
- The smooth block is implemented.  Recursive products of complex `Circle` embed Boolean
  `false,true` as `1,-1`; the corrected direct selector product yields smooth self-inverse
  AND/NAND gates, and arbitrary literal cube edges have direct arbitrary-target smooth
  diffeomorphic extensions.  Composing `AtomicWord.decompose` gives
  `CircleExtension.extension` and `exists_extension` for every finite Boolean permutation,
  including the empty product; `connected_circle_witness` explicitly exhibits the connected
  component manifold required by Theorem 4.1.
- Theorem 5.3 is reconstructed with a stronger checked stability certificate.  The discrete
  three-bit compiler is flattened into recursive circle coordinates, and its compute/act/uncompute
  words globally preserve the two enable and all work coordinates for every circle-valued input.
  `CircleExtension.ThreeBitUniversal.restricted` is therefore a genuine diffeomorphism of the
  data product, `restricted_interpolates` extends the requested Boolean permutation, and
  `exists_qualified_smooth_realization` exposes the placed word, ambient diffeomorphism, fixed
  face, deletion/projection, auxiliary count, and interpolation.  No off-cube equality with the
  separately corrected higher-arity gate is asserted.

## Verified Representation and Scope Decisions

- Boolean words use `Fin n → Bool`, reversible functions use `Equiv.Perm`, and generic indexed
  variants support typed reindexing and product operations.
- Coordinate reindexing uses equivalences of index types; recursive circle products use the proved
  `coord`/`assemble` equivalence and smooth `reindexDiffeomorph`, not arithmetic casts or an
  assumed finite-Pi manifold instance.
- Generalized Toffoli gates carry explicit disjoint controls and target and are packaged as
  involutive permutations.  Literal atomic edges and the exact Gray palindrome provide the
  decomposition bridge.
- The lower-arity sign formula and every exceptional arity are proved; no parity assumption
  remains provisional.
- Three-bit Toffoli universality is represented by `CleanRealizes` over an explicit auxiliary
  index type, then related separately to exact face restriction and semantic dummy deletion.  The
  verified construction has count `2 + (n-3)` and returns all auxiliaries clean.
- The smooth implementation uses mathlib's complex unit `Circle`, its analytic manifold/Lie-group
  API, analytic `Circle.exp`, and the angle convention `0,π ↦ 1,-1`.
- Theorem 4.1 is existential in the connected manifold `M`; it does not claim extension over every connected manifold. Any generic-manifold strengthening must be stated separately and independently justified.
- The paper's `ℝ/(2πℤ)` is modeled by complex `Circle`; `signal_exp` relates the angular
  selector to `(1-cos x)/2`, while the implementation avoids a quotient-representative lift.
- Model one-to-one composition as a constrained circuit/wiring derivation whose evaluator uses ordinary equivalence composition, rather than inventing a second incompatible notion of semantic function composition.
- Keep canonical deletion of singleton product factors distinct from semantic deletion of Boolean outputs, which requires a constancy/dummy certificate.
- Smooth finite products use right-nested recursive binary products with a singleton Euclidean
  zero-fold product.  Arbitrary-coordinate assembly, projection, reindexing, atomic maps, and
  stable-face restriction are all proved for this representation.

## Implemented Formalization Direction and Results

The implementation follows three completed dependency blocks:

1. The finite block defines indexed Boolean words and permutations, typed component operations,
   generalized Toffoli gates, literal cube-edge swaps, and an exact Gray-path decomposition of
   every finite Boolean permutation.
2. The discrete consequence block proves the corrected lower-arity obstruction and qualified
   three-bit universality with explicit constants, clean auxiliaries, face restriction, dummy
   deletion, and exact resource counts.
3. The smooth block uses recursive products of complex `Circle`, replaces the paper's invalid
   iterated binary operation by a direct smooth control product, extends every atomic edge by a
   diffeomorphism, composes those extensions for arbitrary permutations, and reconstructs the
   qualified three-bit smooth theorem on a globally stable auxiliary face.

Finite and smooth extension objects remain separate and are related only by explicit
interpolation predicates. Physical realizability remains outside the verified core.

## Compile-Time and Module-Graph Strategy

`BUILD-PLAN.md` governs all Lean work. Each completed stage classified declarations by fanout and
recorded the smallest focused build targets before implementation. The resulting module layout is:

```text
Bool/{Defs,Finite,Reindex}
  → Component/{Tensor,Face,Restriction,Dummy,OneToOne}
  → Gate/{Toffoli,AndNand,Wiring,Atomic} + Cube/{Basic,Path}
  → Perm/{AtomicWord,Decomposition}
      ├→ Parity/{Lift,Wiring,Generated,Obstruction,Paper}
      └→ Circuit/{ThreeBit,ThreeBitLowering,ThreeBitTransport}
          + Synthesis/{Resources,FaceRealization,Not,MultiControl,Atomic,Universality,Obstruction}

Smooth/{CircleModel,CircleCoordinates,CircleGate,CircleAtomic,CircleReindex,
        AtomicWord,Extension}
  → Smooth/{UniversalLayout,UniversalFace,ThreeBitCircuit,ThreeBitStability}
  → Smooth/Synthesis/{FlatCircuit,AtomicStability,Universality}

Audit/{PaperCircleOperation,*Boundary,Axioms/*}
```

The implemented fanout boundaries are:

- finite combinatorics must not import manifold modules;
- cheap definitions and simp lemmas stay below heavy decomposition, parity, synthesis, and smooth proofs;
- diagnostic computations, counterexamples, and `#print axioms` probes stay under `Toffoli/Audit/` and are never imported by public modules;
- internal leaves import their exact dependencies, never a public facade or `Toffoli.lean`;
- public facades (`Toffoli.Bool`, `Toffoli.Gate`, `Toffoli.Decomposition`, `Toffoli.Parity`,
  `Toffoli.Synthesis`, and `Toffoli.Smooth`) are thin; the root `Toffoli` facade intentionally
  exports only the discrete library so ordinary users do not import manifold dependencies;
- `Perm.AtomicWord` exposes the cheap endpoint-word interface; `Perm.Decomposition` proves
  arbitrary-permutation decomposition, and terminal glue leaves combine it with the synthesis and
  smooth atomic-word engines;
- focused leaf builds and necessary adjacent-consumer builds are the default;
- a full project build is reserved for build-configuration, public/high-fanout API, global notation/instance/simp changes, explicit milestone verification, and final integration.

## Implemented Library and Theorem Inventory

The following are implemented declarations in the pinned project.

### Finite objects and component structure

- `BoolWord`, `BoolVec`, `BoolPerm`, and `BoolPermN` model indexed words and permutations;
  `BoolWord.reindex`, `BoolPerm.reindex`, and `BoolPerm.coordinatePerm` model coordinate changes.
- `BoolPerm.tensor` and `BoolPerm.extendRight` model disjoint extension, while
  `OneToOneCircuit` is separate typed syntax with evaluator `OneToOneCircuit.eval`.
- `Face`, `Face.Mem`, `restrictFaces`, and `restrictFace` encode fixed-coordinate faces and the
  closure evidence needed to restrict a permutation.
- `Component.fixRightEquiv` removes a singleton factor canonically; `RightDummy` and
  `RightDummy.deleteRight` require an explicit semantic constancy certificate before output
  deletion.

### Gate family and decomposition

- `ToffoliGate`, `ToffoliGate.run_involutive`, and `ToffoliGate.perm` give a target-bearing
  positive-control gate; `AndNand.thetaSucc` is the paper-indexed family.
- `atomicEdge` is the literal cube-edge transposition, and the masked-NOT normalization theorems
  identify every literal edge with a two-sided conjugate of the AND/NAND gate.
- `GrayReachable`, `IsEndpointWord`, and `IsEndpointWord.eval_eq_swap` implement connectivity and
  the checked Gray-path palindrome; `AtomicWord.exists_eval_eq` and
  `AtomicWord.eval_decompose` give the exact decomposition of every finite Boolean permutation.

### Parity and universality

- `sign_extendRight`, `sign_extendRight_of_nonempty`, and the placement lemmas prove exact sign
  accounting. `paperGenerated_le_evenSubgroup` handles ambient arity at least three;
  `paperGenerated_*` and the global-complement invariant settle arities zero, one, and two.
- `Synthesis.CleanRealizes`, `Synthesis.ThreeBitUniversal.circuit_cleanRealizes`,
  `Synthesis.ThreeBitUniversal.circuit_restrictFaces_eq`, and
  `Synthesis.ThreeBitUniversal.circuit_deleteRight_eq` state qualified universality with typed
  constants, returned auxiliaries, restriction, and deletion.
- `Synthesis.ThreeBitUniversal.circuit_aux_card*` proves the exact piecewise count and the
  corrected paper bound; `Synthesis.oneAux_not_faceRealizes_twoBitDoubleNot` records the
  two-data-bit one-auxiliary obstruction.

### Smooth extensions

- `CircleExtension.CirclePower`, `boolPoint`, `embed`, `signal`, and `controlProduct` implement the
  recursive circle model, Boolean embedding, and corrected direct selector.
- `gateDiffeomorph` extends `AndNand.thetaSucc`; `atomicDiffeomorph` extends every literal edge;
  `Interpolates` states the finite/smooth relationship and `reindexDiffeomorph` transports layouts.
- `CircleExtension.extension`, `extension_interpolates`, `exists_extension`, and
  `connected_circle_witness` prove the source-faithful existential circle theorem, including
  arity zero.
- `CircleExtension.ThreeBitUniversal.ambient_preservesUniversalAux`,
  `ambient_insert_eq_insert_restricted`, `restricted_interpolates`, and
  `exists_qualified_smooth_realization` prove the smooth qualified
  three-bit theorem on the whole stable auxiliary face.

### Audit declarations and generated reports

- This paper map and the correction log link each main claim to its verified theorem or explicit
  exclusion.
- `Toffoli.Audit.PaperCircleOperation` checks representative independence, smoothness,
  nonassociativity, and absence of an identity for the paper's rejected binary operation.
- `Toffoli.Audit.Axioms.*` runs `#print axioms` on representative exported theorems, and
  `Toffoli.Audit.*Boundary` checks empty/low-arity behavior and exact composition conventions.

## Verified Main-Theorem Dependency Graph

```text
`BoolWord` / `BoolPerm` + component APIs
        |
        +--> `ToffoliGate` + placement --> sign lemmas --> corrected parity obstruction
        |
        +--> cube paths --> `AtomicWord` --> `AtomicWord.exists_eval_eq`
                              |                         |
                              |                         +--> discrete three-bit compiler
                              |                                  |
                              |                                  +--> clean face universality
                              |
complex `Circle` --> coordinates + atomic diffeomorphisms
                              |
                              +--> atomic-word composition --> `exists_extension`
                              |
discrete compiler + smooth placed gates + global auxiliary stability
                              |
                              +--> stable-face restriction
                                       |
                                       +--> `exists_qualified_smooth_realization`
```

## Paper Map

The source is present under `toffoli-1981/`. Printed pages below were checked against the supplied
scan; each in-scope main claim has a Lean artifact or an explicit out-of-scope disposition.

| Paper location and claim | Lean artifact | Dependency | Disposition |
|---|---|---|---|
| Printed pp. 14–15, Goal 2.1: extend an invertible `Bⁿ → Bⁿ` over some connected `M` | `CircleExtension.Interpolates`, `exists_extension`, `connected_circle_witness` | smooth atomic gates, decomposition | Verified as an existential circle theorem; no physical interpretation or every-connected-manifold strengthening |
| Printed pp. 15–16, §§2–3: componentwise extension/restriction | `Face`, `restrictFaces`, `CircleExtension.insertUniversal`, `restrictUniversal` | indexed products, explicit Boolean embedding | Verified with typed faces; “componentwise” does not impose false coordinatewise independence |
| Printed p. 16, §3: one-to-one composition and reindexing | `OneToOneCircuit`, `ThreeBitCircuit.reindex`, smooth `reindexDiffeomorph` | finite equivalences | Verified separately from ordinary semantic composition |
| Printed p. 16, §3: deletion of singleton-valued dummy variables | `Component.fixRightEquiv`, `RightDummy.deleteRight`, `projectUniversal` under face stability | product decompositions | Verified in three deliberately distinct APIs |
| Printed p. 17, Definition 4.1, Eq. (4.1), Remark 4.1: `θ⁽ⁿ⁾` | `ToffoliGate`, `ToffoliGate.perm`, `AndNand.thetaSucc`, component and AND/NAND lemmas | finite controls/target | Verified for every positive order; no order-zero member; `n=1,2,3` conventions checked |
| Printed p. 17, Lemma 4.1: generation by `θ⁽ⁿ⁾` and `θ⁽¹⁾` | `atomicEdge`, `IsEndpointWord.eval_eq_swap`, `AtomicWord.exists_eval_eq`, masked-NOT conjugation theorems | cube adjacency, finite permutation induction | Verified with an explicit recursive palindrome and corrected two-sided conjugation |
| Printed p. 18, Lemma 4.2, Eq. (4.2): circle extension `Θ⁽ⁿ⁾` | `Audit.PaperCircleOperation.paperMul_exp_add_periods`, `paperMul_not_associative`, `paperMul_no_identity`; `CircleExtension.gateDiffeomorph`, `gate_interpolates_thetaSucc` | analytic `Circle`, recursive products, direct finite control product | Original binary operation checked and rejected as a ring operation; corrected gate verified for every positive order, including zero controls/NOT |
| Printed p. 18, Theorem 4.1: extension over an existential connected manifold | `extension_interpolates`, `exists_extension`, `connected_circle_witness` | atomic circle extensions, `AtomicWord.decompose` | Corrected construction verified without physical interpretation |
| Printed p. 20, Theorem 5.1: lower-order `θ` gates generate only even permutations | `sign_extendRight`, `paperGenerated_le_evenSubgroup`, low-arity theorems | sign, explicit proper placement, coordinate wiring | Corrected and verified: parity for `n≥3`; separate complement invariant at `n=2`; trivial `n=1`; false existential conclusion at `n=0` |
| Printed pp. 20–21, Theorem 5.2 and Fig. 7: `θ⁽³⁾` universality with restriction/deletion | `Synthesis.MultiControl.figureSeven_apply`, `Synthesis.ThreeBitUniversal.circuit_cleanRealizes`, `circuit_restrictFaces_eq`, `circuit_deleteRight_eq` | clean-ancilla recursion, atomic decomposition, dummy operations | Corrected and verified; exact count `2+(n-3)`, paper bound only for `n≥3` |
| Printed p. 21, Theorem 5.3: smooth analogue using `Θ⁽³⁾` | `CircleExtension.ThreeBitUniversal.ambient_preservesUniversalAux`, `restricted_interpolates`, `exists_qualified_smooth_realization` | placed circle gate, structural compiler stability, Theorem 5.2 | Reconstructed and verified with explicit constants, face restriction, deletion, and resource qualification; no off-cube higher-gate equality |
| Printed pp. 18–20 mechanisms and pp. 21–23 Appendix/energy interpretation | documentation-only boundary | an explicit physical model | Excluded from the verified core; no physical model is formalized |

## Correction and Resolution Log

Each entry records its source issue, mathematical risk, required evidence, and verified disposition.

| ID | Source issue | Mathematical risk | Verification criterion | Disposition |
|---|---|---|---|---|
| C-001 | Lemma 4.2 defines `x ∘ y = π(1-cos x)(1-cos y)/4` and claims all ring axioms except distributivity | The formula is periodic and hence well defined, but it is not associative and has no multiplicative identity; the iterated product is ambiguous | Check periodicity, smoothness, nonassociativity, and identity failure; formalize the required n-ary control directly as `π ∏ᵢ (1-cos xᵢ)/2` | Resolved and machine-checked: `PaperCircleOperation.paperMul_exp_add_periods` proves representative invariance, `contMDiff_paperMul` proves smoothness, `paperMul_not_associative` and `paperMul_no_*identity` reject the ring claim; the public construction uses direct `controlProduct` instead |
| C-002 | Does Eq. (4.2) define a smooth self-inverse map for every `n > 0`? | Smoothness alone is not a diffeomorphism | Two-sided inverse calculation, empty-product convention, and smoothness | Resolved for the corrected formula by `gate_involutive`, `contMDiff_gate`, `gate_bijective`, and `gateDiffeomorph`; zero controls use empty product `1` |
| C-003 | Lemma 4.2 embeds Boolean `0,1` as circle angles `0,π`; does Eq. (4.2) recover Eq. (4.1) under all conventions? | Convention mismatch can reverse gate semantics | Evaluated truth table and quotient-point distinctness | Resolved: `boolPoint` sends `false,true` to `1,-1`; `embed_injective` proves distinctness and `gate_interpolates_thetaSucc` proves the full truth table |
| C-004 | Theorem 4.1 is existential in `M`; should any reusable generic-manifold theorem be attempted? | Accidentally strengthening “there exists connected `M`” to “every connected `M`” | Keep existential circle theorem primary; require independent hypotheses/proof for any generic result | Resolved by scope: `connected_circle_witness` exhibits the connected complex circle and `exists_extension` proves the required product diffeomorphism; no every-connected-manifold theorem is claimed |
| C-005 | Lemma 4.1 sketches a Gray-path endpoint exchange but gives no exact transposition word or composition direction | Informal order can yield the wrong permutation | Algebraic proof and exhaustive low-arity check | Resolved: `IsEndpointWord` records the exact palindrome, `eval_eq_swap` proves it, and the two-bit direction audit covers every input |
| C-006 | Definition 4.1 assumes `n > 0`; what API and results should exist at arity `0`, and how do `n=1,2` special cases interact with later theorems? | Cardinality/parity formulas may have exceptions | Separate lemmas or uniform proof covering each | Resolved for the gate API: `thetaSucc n` has order `n+1`; no target-bearing gate exists on `Fin 0`; NOT/CNOT/three-bit cases are proved and audited. Later parity exceptions remain under C-020 |
| C-007 | Theorem 5.1 relies on `2^(n-i)` identical copies; what is the exact sign formula for extending an `i`-ary permutation to `n` bits? | Obstruction depends on the correct exponent | Derived sign formula and checked examples | Resolved: `sign_extendRight` proves exponent `card (BoolWord κ)`, rewritten as `2 ^ card κ`; nonempty `κ` gives sign one |
| C-008 | Theorem 5.1 concerns lower-order AND/NAND gates, not arbitrary lower-arity permutations; what is the strongest correct generalization? | The theorem may be overgeneralized | Formalize the exact statement first, then prove any generalization separately | Resolved in two layers: `ProperlyGenerated` proves the stronger placement-only arbitrary-local result; `paperGenerated` separately formalizes the exact AND/NAND-plus-wiring source generator set |
| C-009 | Theorem 5.2 claims at most `2n-3` constant-input deletions; what are their values, lifetimes, cleanliness, and corresponding outputs? | Resource-free universality may be falsely inferred | Explicit Fig. 7-based recursion and counted synthesis witness | Resolved: `UniversalAux n = Fin 2 ⊕ Fin(n-3)`, enables are always `true`, work bits always `false`, and `circuit_cleanRealizes` returns the same bank; exact size `2+(n-3)` |
| C-010 | Does restriction preserve bijectivity, or is a stable face hypothesis needed? | A restricted permutation need not map a face to itself | Precise closure/stability condition | Resolved: `FaceRealizes.maps_faces` proves exact source/target membership and supplies the evidence required by `restrictFaces`; clean universality preserves one named face |
| C-011 | When is output deletion legitimate? | Dropping a non-dummy component changes semantics | Dependence/identity proof for every deleted coordinate | Resolved: `RightDummy` is an explicit constancy certificate; `circuit_rightDummy` and `circuit_deleteRight_eq` certify all deleted outputs |
| C-012 | The paper calls a manifold diffeomorphism the appropriate generalization of a bicontinuous function; where are only continuity versus smoothness actually established? | Terminology can obscure a proof obligation | Audit each result and keep homeomorphism/diffeomorphism claims separate | Resolved: every smooth core extension is packaged as a mathlib `Diffeomorph` with separately proved smooth forward and inverse maps; no result is justified by continuity alone |
| C-013 | Are component-preservation claims literal or only up to coordinate reindexing? | Composition structure may be misstated | Typed statement and source diagram audit | Resolved: gate coordinate laws are literal in their chosen layout; `BoolWord.reindex`, `ThreeBitCircuit.reindex`, and `CircleExtension.reindexDiffeomorph` explicitly transport layouts, while circuit and semantic composition remain separate |
| C-014 | Are physical realizability claims mathematical consequences of the extension theorem? | Category error between existence and mechanism | Keep separate absent a formal physical model | Resolved as out of verified scope: no gears, cams, energy, reversibility-of-mechanism, or physical realizability declaration occurs in the Lean core |
| C-015 | Theorem 5.2's proof on printed p. 21 writes the restriction of `φ⁽⁵⁾` as `B³ × {0}` while fixing one of five wires and claiming the other four implement `θ⁽⁴⁾` | The displayed type has only four total coordinates and cannot be a face of the five-wire circuit with four retained data wires | Correct to `B⁴ × {0}` and verify the Fig. 7 circuit algebraically | Resolved: `figureSeven_word` and `figureSeven_apply` verify four retained data bits plus one zero work bit; the source face is `B⁴×{0}` |
| C-016 | Theorem 5.2's proof on printed p. 20 says “function `φ⁽⁵⁾` of Figure 4,” but the construction is Figure 7 | Incorrect cross-reference obscures the universality gadget | Cite and formalize Figure 7 | Resolved: `MultiControl.figureSeven_word` and `MultiControl.figureSeven_apply` formalize and audit Figure 7; Figure 4 is not used |
| C-017 | Theorem 5.2 claims at most `2n-3` constant inputs for every order `n` | The bound is negative for `n=1`; for `n=2`, one fixed wire cannot realize all two-bit permutations from three-bit Toffoli and wire permutations because the three-wire generators preserve Hamming-weight strata enough to obstruct, e.g., double NOT on the face | Prove the low-arity obstruction formally; state a corrected piecewise bound or require `3 ≤ n`; prove the remaining accounting | Resolved with scope: the construction uses two auxiliaries for `n≤3`, `n-1` for `n≥3`, and none at `n=0` via a separate theorem; `2n-3` is proved only for `n≥3`. `oneAux_not_faceRealizes_twoBitDoubleNot` covers the flattened placed-gate/wiring/serial closure |
| C-018 | At the start of Lemma 4.1's proof (printed p. 17), the PDF says “By definition, `θ⁽ⁿ⁾` is a permutation” where the argument requires the arbitrary given `f⁽ⁿ⁾` | The published text names the wrong function | Retain the Markdown transcription's justified correction to `f⁽ⁿ⁾` and document it | Resolved as a source typo: the formal permutation decomposition starts from arbitrary `p : BoolPermN n`, never from the gate family itself |
| C-019 | Literal set inclusion `M ⊇ B` and the word “componentwise” are underspecified for Lean | It can be misread as a subtype requirement or coordinatewise independence | Use an explicit injective Boolean embedding/two distinct points; define componentwise interpolation on product factors without imposing false dependency restrictions | Resolved: `boolPoint_injective`, `embed_injective`, and `Interpolates` use an explicit embedding; face/reindex APIs express product factors without imposing coordinatewise independence |
| C-020 | Theorem 5.1's proof says every allowed proper-arity operation is even, while §3 also calls coordinate reindexing one-to-one composition | A coordinate swap on `B²` is an odd vertex permutation; the parity proof as written therefore fails at ambient arity two if free reindexings are generators | Prove the parity theorem for `n ≥ 3` with free reindexing, or treat reindexing as placement/conjugation; settle `n=0,1,2` separately | Resolved: `sign_coordinatePerm_eq_one` covers `n≥3`; at `n=2` a global-complement centralizer excludes CNOT; `n=1` is trivial and at `n=0` the claimed existential obstruction is false |
| C-021 | Lemma 4.1 says NOTs are “applied” to selected controls to obtain all edge atoms | A zero-controlled edge requires NOT conjugation both before and after `θ⁽ⁿ⁾`, not a one-sided application | Formalize the explicit conjugation and verify the edge transposition | Resolved by `edgeNormalizer_permCongr_atomicEdge` and its converse: the same masked NOT occurs before and after |
| C-022 | Theorem 5.3 says only that its proof “parallels” Theorem 5.2 | Fixing a smooth `Θ³` control at `π` gives a valid extension but not necessarily the paper's exact lower-order `Θ` away from Boolean points; the nonassociative operation also makes higher `Θ` ambiguous | State interpolation/equivalence results, not literal off-cube equality unless separately proved; reconstruct the stable-face smooth circuit | Resolved by reconstruction: compute/act/uncompute replacement proves global auxiliary stability; `ambient_insert_eq_insert_restricted` holds on the entire smooth face and `restricted_interpolates` holds on Boolean points. No literal off-cube equality with the corrected direct higher gate is claimed |
| C-023 | The natural finite model uses `Fin n → Circle`, but pinned mathlib lacks a turnkey finite-Pi `IsManifold` and diffeomorphism constructor | Assuming an instance could stall the smooth layer or pull heavy infrastructure into the core | In an early Stage 7 leaf, compare recursively nested binary products with an isolated finite-Pi manifold bridge; prove equivalence to the chosen component indexing | Resolved: `CirclePower` is right-nested with a singleton zero-fold; `coordEquiv`, smooth assembly, `reindexDiffeomorph`, and flattened layout theorems supply the missing finite-coordinate API |

## Dependency and Environment Notes

### Versions and project setup

- `formal/lean-toolchain` pins `leanprover/lean4:v4.32.0`.
- `formal/lakefile.toml` pins mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`; `formal/lake-manifest.json` resolves the same commit.
- `formal/Toffoli/Smoke.lean` remains the Stage 1 diagnostic leaf. The thin root imports the
  completed discrete public facades; internal leaves import only exact dependencies and never the
  root or their own facade.
- `Toffoli.Audit.Axioms.Finite` reports only `propext`, `Classical.choice`, and `Quot.sound` for
  representative exported finite declarations and is not imported publicly.
- `formal/Toffoli/Gate/Toffoli.lean` has the narrow imports `Mathlib.Data.Finset.Basic` and
  `Toffoli.Bool.Defs`; paper-family and wiring dependencies are isolated in `Gate/AndNand` and
  `Gate/Wiring`. `Toffoli.Audit.Axioms.Gate` likewise reports only standard foundational axioms.
- Initial validation on 2026-07-17: after narrowing the smoke import, focused smoke output built in 2.02 s (309 jobs), the root output in 2.07 s (310 jobs), and a warm full build in 1.26 s (311 jobs). The first smoke attempt correctly failed on import ordering and was fixed before these successful results.
- Stage 3 gate promotion on 2026-07-17: the root output built in 1.3 s (771 jobs; 2.78 s command
  wall time), and the warm milestone full build passed in 1.51 s (772 jobs). Gate core remains a
  602-job leaf; paper-family/wiring and diagnostics remain outside its dependency path.
- Stage 4 decomposition promotion on 2026-07-17: cheap cube primitives were split into the
  314-job `Cube.Basic` leaf, while finite-group sign/induction stays exclusively in the 912-job
  `Perm.Decomposition` heavy leaf. The facade/root/audit build passed (943 jobs), the warm full
  build passed in 1.41 s (940 jobs), and the decomposition axiom audit contains only standard
  foundations.
- Stage 5 parity promotion on 2026-07-17: generic lift/serial leaves are separated from the
  first-two-coordinate wiring calculation and exact paper subgroup leaf. The public/root/audit
  build passed with 952 jobs; the warm full build passed in 1.38 s with 950 jobs. No sign or
  subgroup import flows into the finite, cube, gate, or decomposition cores.
- Stage 6 universality promotion on 2026-07-17: cheap face/resource/placed-gate infrastructure is
  separated from the prefix compiler and from the sole 931-job heavy leaf that imports arbitrary
  permutation decomposition.  The public synthesis facade built with 933 jobs; the
  facade/root/audit milestone passed with 964 jobs and the warm finite-block full build with 962
  jobs.  Representative main results use only `propext`, `Classical.choice`, and `Quot.sound`.
- Stage 7 circle promotion on 2026-07-17 exposes a thin `Toffoli.Smooth` facade without adding it
  to the root discrete umbrella. `CircleModel`/`CircleGate` built through 2531 jobs, the
  facade/boundary audit through 2533, and the axiom audit through 2532.  No smooth import flows
  back into the finite or synthesis graph.
- Stage 8 keeps coordinate assembly/reindexing, direct atomic diffeomorphisms, atomic-word
  composition, universal-face restriction, smooth placed-three-bit evaluation, compiler
  stability, and heavy arbitrary-decomposition glue in separate leaves.  `AtomicStability` built
  through 2557 jobs (2.5 s leaf), the terminal qualified theorem through 2563 (3.1 s leaf), and
  the public `Toffoli.Smooth` facade through 2570 (2.3 s leaf, 4.0 s wall).  Boundary and axiom
  diagnostics remain non-public; all direct and qualified smooth main results report only
  `propext`, `Classical.choice`, and `Quot.sound`.  The discrete root deliberately remains free of
  manifold imports.
- Stage 9 adds the rejected-operation check only as a terminal non-public audit leaf. Its focused
  build completed in 5.05 s and its axiom leaf in 4.56 s. The final warm setup/facade/boundary/
  axiom target set completed in 3.38 s; the default discrete target completed in 2.21 s.

### Mathlib reconnaissance disposition

- The finite implementation uses mathlib permutations, sign, finite-cardinality, product, and
  reindexing APIs listed below.
- No ready-made Gray-path decomposition matched the required exact word, so `Cube.Path` and
  `Perm.AtomicWord` supply the local reusable construction.
- The smooth implementation uses complex `Circle` and recursive binary products. It does not
  define an angular quotient lift. The non-public `PaperCircleOperation` audit instead proves
  invariance under independent `2πℤ` shifts after `Circle.exp`, so representative independence is
  checked without introducing the less robust quotient-manifold stack.

### Confirmed pinned mathlib surfaces

- `Mathlib.GroupTheory.Perm.Basic`: `Equiv.Perm`, swaps, and basic permutation operations.
- `Mathlib.GroupTheory.Perm.Sign`: `Equiv.Perm.sign`, `sign_swap`, conjugation invariance, product-congruence sign lemmas, and transposition factorization/induction.
- `Mathlib.Logic.Equiv.Basic` and `.Prod`: Pi reindexing plus dependent/product congruences.
- `Mathlib.Data.Fintype.Card` and `.BigOperators`: `Fintype.card_bool` and `Fintype.card_fun`.
- `Mathlib.InformationTheory.Hamming` was inspected, but the exact decomposition is implemented
  locally in `Toffoli.Cube.Path` and `Toffoli.Perm.AtomicWord`.
- `Mathlib.Analysis.Complex.Circle` and `Mathlib.Geometry.Manifold.Instances.Sphere`: complex unit `Circle`, analytic manifold/Lie-group instances, analytic `Circle.exp`, and the distinct Boolean points `1` and `Circle.exp π = -1`.
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle`: `AddCircle.homeomorphCircle'` relates `AddCircle (2 * π)` to complex `Circle` and sends quotient representatives to `Circle.exp`.
- `Mathlib.Geometry.Manifold.Diffeomorph`: the smooth diffeomorphism structure and product constructions.
- `AddCircle` has useful quotient topology, but the pinned generic quotient-manifold file explicitly leaves smoothness of quotient actions as a TODO; the complex `Circle` route is therefore preferred.

### Dependency policy

- Use only pinned project dependencies.
- Prefer mathlib results after confirming their exact statements in the pinned version.
- Keep the finite combinatorics layer independent of manifold imports where practical.
- Keep the generic extension interface separate from the concrete circle construction.
- Any classical-choice or quotient axioms inherited from Lean/mathlib must be visible in the final axiom audit; no unexplained local axioms are allowed.
- Treat `BUILD-PLAN.md` as the build policy for every Lean stage.
- Introduce declarations in the lowest suitable module and keep heavy proofs, exhaustive computations, counterexamples, and axiom probes in narrow leaves.
- Write the focused build and adjacent-consumer commands in the stage file before implementation.
- Build immediately after module skeleton or import changes; avoid umbrella imports and import churn.
- Run a full project build only for high-fanout/public API or configuration changes, global notation/instance/simp changes, explicit milestones, and final integration.
- Record focused build timings when a stage or tactic becomes noticeably slow; split or localize costly proofs before they enter a high-fanout dependency path.

## Success Metrics and Final Verification Requirements

The original objective is complete only when all applicable conditions below hold:

- The pinned project builds from a clean checkout using documented commands.
- The finite Boolean permutation API handles empty and low arities and exposes tested reindexing, one-to-one composition, restriction, dummy extension, and deletion notions.
- Generalized Toffoli gates are defined as permutations and their involution and component semantics are proved.
- The exact Gray-code/atomic-flip decomposition of every Boolean permutation is proved.
- The parity obstruction is proved with its exact scope and boundary cases.
- Three-bit Toffoli universality is proved with explicit, verified resource accounting and is not presented as stronger ancilla-free universality.
- The explicit circle construction is either formalized with well-definedness, smoothness, inverse, and interpolation proofs or replaced by a documented equivalent construction after the original is decisively corrected/rejected.
- The main smooth extension theorem is proved with all necessary manifold hypotheses stated.
- Physical claims remain outside the verified mathematical core unless separately modeled.
- The paper map links each main paper claim to a Lean declaration, correction, counterexample, or explicitly unresolved item.
- Completed modules contain no `sorry` and no unexplained project-specific axioms.
- Focused module and adjacent-consumer checks pass throughout development; milestone and final clean full builds, whitespace checks, and the main-theorem axiom audit pass.
- Documentation records conventions, representation choices, changes from the paper, unresolved points, and limitations.

## Stages

### 1-SOURCE-AUDIT

Status: complete.

#### Big Picture Objective

Establish a source-grounded, reproducible formalization baseline before mathematical implementation.

#### Detailed Implementation Plan

- Verify the supplied Markdown transcription against `toffoli-1981/toffoli-1981.pdf`; inventory sections, definitions, propositions, theorem statements, equations, and diagrams relevant to scope.
- Complete the preliminary paper map with PDF page coordinates and normalized mathematical statements.
- Separate claims into discrete combinatorics, smooth topology/geometry, and informal physical assertions.
- Inspect candidate Lean/mathlib versions and relevant APIs.
- Select and pin compatible Lean/mathlib versions; initialize the minimal Lake project and a namespaced smoke import.
- Adapt the low-fanout module graph to the APIs actually available; record focused build targets
  and avoid importing a broad mathlib umbrella where narrow imports suffice.
- Record source ambiguity and suspected missing assumptions in the correction log without prematurely resolving them.

#### Completion Requirements

- A source-location-complete map exists for every in-scope main claim.
- The paper version and bibliographic identity are recorded.
- Lean and mathlib are pinned, and a clean minimal build succeeds with the exact command logged.
- Initial API reconnaissance is based on declarations available in the pinned version.
- The smoke module has narrow imports, its focused build is recorded, and the initial dependency graph has no avoidable high-fanout umbrella module.
- No substantive theorem is represented as verified yet.

### 2-FINITE-CORE

Status: complete.

#### Big Picture Objective

Define the finite Boolean objects and reusable component operations with precise typing and boundary behavior.

#### Detailed Implementation Plan

- Compare `Fin n → Bool`, `Vector Bool n`, and any suitable mathlib bit-vector type against reindexing and cardinality needs; document the chosen representation.
- Define or alias Boolean permutations using finite equivalences.
- Implement coordinate reindexing and prove identity/composition laws.
- Formalize ordinary equivalence composition and a distinct one-to-one circuit/wiring derivation with an evaluator into ordinary composition.
- Define fixed-coordinate faces, restriction, identity/dummy extension, and component dependence.
- Keep canonical deletion of singleton factors after restriction separate from semantic deletion of Boolean outputs carrying a constancy/dummy certificate.
- State and prove all arity-zero and low-arity behavior rather than relying on nonemptiness.
- Keep `Bool/Core` and cheap component definitions below the heavier restriction/deletion proof leaf; do not import manifold or synthesis modules.

#### Completion Requirements

- All finite-core modules build without `sorry` or local axioms.
- The distinction between each composition/restriction/deletion operation is reflected in types and documentation.
- Empty and low-arity examples or lemmas pass.
- Focused leaf builds and necessary adjacent finite-core consumer builds pass; run a broader build only if a public/high-fanout surface changed.
- Exported core declarations have acceptable axiom audits, and the stage records the module/fanout decision and build timings if material.

### 3-TOFFOLI

Status: complete.

#### Big Picture Objective

Formalize generalized Toffoli/AND/NAND permutations and their component semantics.

#### Detailed Implementation Plan

- Choose a controls/target representation that makes distinctness explicit.
- Define the target-bit update and package it as an equivalence.
- Prove involutivity, truth-table behavior, support, and compatibility with coordinate reindexing.
- Relate special cases to NOT, controlled-NOT, and three-bit Toffoli under explicit Boolean conventions.
- Define extension by unused coordinates and prove its interaction with gate arity.
- Keep gate definitions and cheap involution laws in a narrow module; isolate any expensive support or synthesis-facing proofs in leaves.

#### Completion Requirements

- Every gate constructor produces a proved permutation, including deliberately specified degenerate/low-arity cases.
- AND/NAND naming and Boolean conventions are documented and checked by lemmas.
- Reindexing and dummy-extension laws build without `sorry`.
- Focused gate-leaf and adjacent-consumer builds plus axiom checks pass; a full build is required only if the public API or a high-fanout dependency changed.

### 4-GRAY-DECOMP

Status: complete.

#### Big Picture Objective

Prove an exact decomposition of arbitrary Boolean permutations into atomic bit-flip/edge permutations.

#### Detailed Implementation Plan

- Define cube adjacency and atomic edge transpositions.
- Construct Gray-code paths with endpoints, adjacency, and no-duplication properties needed by the proof.
- Derive a transposition of arbitrary vertices as an explicitly ordered word in edge transpositions.
- Combine this with a proved finite-permutation transposition decomposition.
- State the final decomposition in a reusable algebraic form and prove component/gate interpretations.
- Exhaustively evaluate small arities to catch direction, endpoint, and duplication mistakes.
- Keep executable exhaustive checks in `Perm/Audit`, which no runtime or public core module imports; keep the heavy decomposition theorem out of `Bool/Core` and `Gate/Basic`.

#### Completion Requirements

- The exact word evaluates to the intended permutation under the documented composition convention.
- Every Boolean permutation has a proved finite atomic decomposition.
- Arity `0`, `1`, and `2` are explicitly covered.
- Small exhaustive checks and focused builds for Gray/decomposition leaves and their necessary consumers pass, together with whitespace/diff checks and axiom audit.
- Run a milestone full build because this decomposition is a major dependency boundary; record its result and any expensive modules.

### 5-PARITY

Status: complete.

#### Big Picture Objective

Derive and formalize the precise parity obstruction to generation by lower-arity gates.

#### Detailed Implementation Plan

- Reconcile mathlib's permutation sign/parity API with Boolean-word equivalences.
- Prove the sign formula for extending a gate across unused Boolean coordinates.
- Determine when repeated copies force the extended permutation to be even.
- Formalize the generated-subgroup argument and exhibit an odd target permutation outside it.
- State all arity assumptions and exceptions; compare the result line-by-line with the paper.
- Keep sign infrastructure separate from the obstruction proof so discrete users do not import the generated-subgroup argument unnecessarily.

#### Completion Requirements

- The extension sign formula is proved, not inferred from examples.
- The obstruction theorem names the exact allowed lower-arity generators and ambient arity.
- Every small-arity exception is settled.
- Computed audit examples agree with the theorem; focused parity/obstruction and necessary consumer builds plus axiom audit pass.

### 6-UNIVERSALITY

Status: complete.

#### Big Picture Objective

Prove the exact qualified universality of the three-bit Toffoli gate and account for every auxiliary resource.

#### Detailed Implementation Plan

- Define a synthesis/closure relation that separately records gate composition, reindexing, fixed input constants, restrictions, ancilla coordinates, and justified dummy deletion.
- Reconstruct the paper's simulations and validate their truth tables.
- Use the discrete decomposition theorem to reduce arbitrary permutations to the simulated atoms.
- Track clean versus dirty ancillas, returned constants, retained garbage, and deleted dummy outputs.
- Prove the strongest justified theorem and state explicit non-claims about unrestricted or ancilla-free universality.
- Keep the closure/resource vocabulary below the heavy three-bit synthesis theorem, and keep truth-table/exhaustive diagnostics out of the public API path.

#### Completion Requirements

- The universality statement cannot hide constants or deletion in an untyped phrase such as “restriction.”
- A checked construction gives an explicit resource count or a proved bound.
- Deleted outputs satisfy the formal dummy criterion.
- The result is compared with the exact paper claim and any correction is logged.
- Focused closure/synthesis and adjacent-consumer builds plus the main-theorem axiom audit pass.
- Run a milestone full build at the end of the finite/discrete block and record costly dependency paths.

### 7-CIRCLE-EXT

Status: complete.

#### Big Picture Objective

Validate and formalize the explicit circle-valued smooth extension, or replace it with a documented equivalent construction if necessary.

#### Detailed Implementation Plan

- Transcribe the paper's formula and Boolean embedding exactly, with source locations.
- Test representative invariance before committing to a quotient-based definition.
- Compare available mathlib circle/Lie-group models and select the most robust one.
- Define the smooth control function/operation and prove interpolation at embedded Boolean points.
- Construct the generalized gate map on a product of circles.
- Prove smoothness, involution, two-sided inverse, diffeomorphism packaging, and component preservation.
- If the formula fails, record a proof/counterexample and formalize the closest correct theorem without disguising the change.
- Keep the circle model/embedding below smooth gate proofs; isolate experimental formula probes and counterexamples in `Smooth/Audit`.

#### Completion Requirements

- Every quotient lift has a proved well-definedness obligation.
- The Boolean truth table, smoothness, inverse, and self-inverse claims are formal theorems.
- Empty and low-dimensional products are addressed.
- The relation between the chosen circle model and the paper's circle is documented.
- Focused circle/basic, gate, and necessary adjacent-consumer builds plus axiom audit pass; no finite module is rebuilt through a reverse smooth import.

### 8-MANIFOLD-EXT

Status: complete.

#### Big Picture Objective

Determine and prove the strongest correct extension theorem for products of a connected manifold.

#### Detailed Implementation Plan

- Normalize the paper's claimed manifold hypotheses and identify the structure actually used by its construction.
- Determine whether connectedness alone suffices; seek a proof, a counterexample, or necessary strengthened assumptions.
- Define a generic atomic-extension interface separated from the concrete circle implementation.
- Compose atomic diffeomorphisms according to the verified decomposition theorem.
- Prove finite interpolation, inverse/diffeomorphism properties, and compatibility with component reindexing.
- Keep topological/homeomorphic and smooth/diffeomorphic theorems separate.
- Place the heavy main extension proof in a leaf over the generic interface and concrete atomic construction; do not move it into a shared smooth core.

#### Completion Requirements

- The main theorem's hypotheses exactly support every construction step.
- Any correction to “connected manifold” is proved or supported by a decisive counterexample and recorded.
- Finite permutation and smooth extension remain distinct types linked by an interpolation predicate.
- Existence is not described as physical realizability.
- Focused extension and adjacent public-consumer builds plus the main-result axiom audit pass.
- Run a milestone full build for the completed smooth block and record any compile-time hotspots.

### 9-INTEGRATE-AUDIT

Status: complete.

#### Big Picture Objective

Turn the proved modules into a coherent reusable library and close the paper/correction/axiom audit.

#### Detailed Implementation Plan

- Stabilize namespaces, theorem names, imports, and public module boundaries.
- Add user-facing examples and documentation without duplicating core proofs.
- Complete the paper-to-Lean map with verified, corrected, disproved, out-of-scope, or unresolved status for every claim.
- Complete the correction log with evidence and explain all material deviations.
- Run repository-wide searches for placeholders and project-specific axioms.
- Run the full clean build, focused examples, whitespace/diff checks, and `#print axioms` audit of public main results.
- Record reproducibility commands and known limitations.
- Review the import graph and high-fanout modules against `BUILD-PLAN.md`; remove accidental umbrella imports, public diagnostics, and broad global automation.

#### Completion Requirements

- The project builds from a clean environment using pinned versions and documented commands.
- Repository-wide searches find no `sorry`, `admit`, untracked proof placeholders, or unexplained axioms in completed modules.
- Each scoped paper claim has a documented disposition and declaration link where applicable.
- Main theorem axiom output is recorded and explained.
- The final module graph keeps heavy proofs/audits out of low-level dependency paths, and focused build commands for common edit surfaces are documented.
- Documentation preserves all conceptual distinctions and accurately states resource assumptions and limitations.
- The original objective, rather than merely the easiest subset, is demonstrably achieved or any genuinely unresolved claim remains explicit next work rather than being marked complete.

#### Stage Results

- A clean explicit build of both facades and all then-existing boundary/axiom leaves passed 2607
  jobs in 1099.53 s wall time with 3009048 KiB maximum RSS. This cold cost includes rebuilding
  pinned mathlib and is deliberately milestone-only.
- The final warm target set, including `Toffoli.Smoke`, both facades, every boundary audit, the new
  paper-operation audit, and every axiom audit, passed in 3.38 s; plain `lake build` passed in
  2.21 s.
- The final graph contains 71 Lean modules and 138 internal imports, with no cycles, reverse
  smooth imports, implementation-to-umbrella imports, public audit imports, or unreachable
  implementation leaves.
- Lean-source scans find no `sorry`, `admit`, project `axiom`, `unsafe`, `partial`, `opaque`, or
  `extern` declaration. All representative axiom output is confined to `propext`,
  `Classical.choice`, and `Quot.sound`.
- The paper map and all C-001–C-023 corrections have final dispositions. Physical mechanisms
  remain explicitly outside the verified core. Repository whitespace/diff checks pass.
