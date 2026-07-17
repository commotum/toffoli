# Goal 1 — Bicontinuous Extensions in Lean 4

Shorthand goal: `TOFFOLI-LIB`

Status: Stage `2-FINITE-CORE` complete; Stage `3-TOFFOLI` in progress.

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
- For every proposed involutive smooth extension, prove smoothness, the interpolation property, bijectivity, the inverse law, and preservation of the claimed component structure.
- For Gray-code decomposition, record the exact order and composition convention and test it in small dimensions.
- For parity and three-bit universality results, make all arity, ancilla, fixed-constant, restriction, and dummy-coordinate counts explicit.
- Keep a paper-to-Lean claim map, correction/unresolved-point log, dependency record, and axiom audit current as the formalization advances.
- Follow the incremental-build principles in repository-root `BUILD-PLAN.md`: narrow imports, low-dependency core definitions, heavy proof and audit leaves, thin public APIs, and the smallest build that covers each change.
- Avoid editing high-fanout modules for convenience. Avoid broad global simp lemmas, instances, notation, or umbrella imports unless the stage establishes a concrete need.
- Do not redefine success as a convenient subset of the paper. Unsupported or false claims may be corrected or decisively rejected, but the disposition and evidence must be recorded.

## Current Facts

- The repository contains the paper as `toffoli-1981/toffoli-1981.md` and `toffoli-1981/toffoli-1981.pdf`, together with extracted figures. The Markdown identifies it as Tommaso Toffoli, *Mathematical Systems Theory* 14 (1981), 13–23.
- Repository-root `BUILD-PLAN.md` defines the mandatory incremental Lean build discipline for this goal.
- The repository also contains a minimal Python/uv shell (`pyproject.toml`, `uv.lock`, and `main.py`). The Lean project is isolated under `formal/`.
- `formal/lean-toolchain` pins Lean 4.32.0. `formal/lakefile.toml` pins mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`, and the generated manifest records that exact revision.
- The Stage 1 smoke leaf imports only `Mathlib.Logic.Equiv.Basic`; focused, root-target, and initial full builds pass.
- No existing `goal-*` folder was present before this scaffold, so this goal is `goal-1`.
- The PDF has 11 scan pages corresponding to printed pages 13–23. The principal formal claims are Definition 4.1, Lemmas 4.1–4.2, Theorem 4.1, and Theorems 5.1–5.3.
- Source audit has confirmed that the binary circle operation in Lemma 4.2 is well defined but is not associative and has no multiplicative identity, contrary to the paper's “all ring axioms except distributivity” assertion. The required smooth gate can instead use the direct finite control product.
- Printed page 21 contains two source errors in Theorem 5.2's proof: it cites Figure 4 rather than Figure 7 and writes the restriction face as `B³ × {0}` although the displayed five-wire construction fixes one wire and retains four, so it must be `B⁴ × {0}`.
- The finite core is implemented and verified. It uses generic indexed Boolean words and finite
  aliases, distinguishes coordinate wiring from gate conjugation, provides disjoint tensoring and
  resource-free one-to-one circuit syntax, and separates exact face restriction, singleton-factor
  deletion, and certificate-driven semantic dummy deletion.

## Current Assumptions to Validate

- A Boolean word of arity `n` can likely use `Fin n → Bool` (or an equivalent mathlib finite-vector representation), with reversible Boolean functions represented by `Equiv.Perm (Fin n → Bool)`.
- Coordinate subsets and reindexings may be most reusable as equivalences between finite index types rather than arithmetic casts between naturals.
- Generalized Toffoli/AND/NAND gates should be modeled as explicit involutive permutations with a target coordinate and a finite set or predicate of control coordinates; degenerate target/control overlaps must be ruled out or assigned precise semantics.
- Atomic bit-flip permutations and transpositions can likely bridge Gray-code paths to general finite-permutation generation.
- The lower-arity obstruction is expected to use sign/parity after extending a gate by unused coordinates; the exact exponent and all small-arity exceptions must be derived.
- Three-bit Toffoli universality requires a precise closure operation involving componentwise restriction and deletion of dummy coordinates. Theorem 5.2 claims at most `2n - 3` constant-input deletions for an order-`n` target when composition precedes deletion; that construction and count are not yet verified.
- Use mathlib's complex unit `Circle` if Stage 7 validation succeeds. In the pinned version it is an analytic one-manifold and Lie group (`Mathlib.Geometry.Manifold.Instances.Sphere`), and `Circle.exp` is analytic. Angles `0,π` correspond to `1,-1`.
- Theorem 4.1 is existential in the connected manifold `M`; it does not claim extension over every connected manifold. Any generic-manifold strengthening must be stated separately and independently justified.
- The paper explicitly uses the circle `ℝ/(2πℤ)`, embeds Boolean `0,1` as angles `0,π`, and calls the desired map a diffeomorphism. These conventions still need a precise Lean model and proof.
- Model one-to-one composition as a constrained circuit/wiring derivation whose evaluator uses ordinary equivalence composition, rather than inventing a second incompatible notion of semantic function composition.
- Keep canonical deletion of singleton product factors distinct from semantic deletion of Boolean outputs, which requires a constancy/dummy certificate.
- The smooth product representation is not settled: binary product manifolds are supported directly, but the pinned source does not expose a turnkey finite-Pi manifold/diffeomorphism API. Stage 7 must choose recursive products or prove an isolated finite-Pi bridge.

## Tentative Formalization Direction

Proceed in three dependency blocks:

1. Finite core: finite Boolean words and permutations, component reindexing, restriction/extension operations, generalized Toffoli gates, atomic flips, and exact Gray-code decomposition.
2. Discrete consequences: lower-arity parity obstruction and three-bit Toffoli universality with resource accounting for constants, ancillas, restrictions, and dummy deletion.
3. Smooth layer: validate the explicit circle formula, choose a robust circle model, construct smooth involutions/diffeomorphisms, then prove the main extension theorem without conflating it with physical realization.

This ordering is provisional. Source audit or mathlib constraints may require a different representation or theorem factorization.

## Compile-Time and Module-Graph Strategy

`BUILD-PLAN.md` governs all stages that add Lean code. Before each stage, the stage file must classify each proposed declaration as low-level data/API, proof-side, diagnostic/audit, fallback, or temporary scaffolding and name the smallest build targets that cover it.

The tentative namespace/module layout is deliberately layered. Heavy universal-decomposition proofs are separated from the cheap atomic-word interface so synthesis and smooth engines do not rebuild when Gray-code proofs change:

```text
Toffoli/
  Bool/Defs.lean
  Bool/Reindex.lean
  Component/{Reindex,OneToOne,Face,Restriction,Dummy}.lean
  Gate/{Toffoli,Wiring,Atomic}.lean
  Cube/{Adjacency,Path}.lean
  Perm/{AtomicWord,Transposition,Decomposition}.lean
  Parity/{Lift,Toffoli,Obstruction}.lean
  Synthesis/{Resources,Semantics,Gadgets,FromAtoms,ThreeBit}.lean
  Smooth/Extension/{Defs,Compose,FromAtoms}.lean
  Smooth/Circle/{Model,Control,Toffoli,Atoms,Extension}.lean
  Smooth/Synthesis/{Lift,ThreeBit}.lean
  Audit/*.lean
```

This is a planning aid, not permission to create all modules preemptively. A stage should prefer one narrow leaf until real import or fanout pressure justifies splitting it. In particular:

- finite combinatorics must not import manifold modules;
- cheap definitions and simp lemmas stay below heavy decomposition, parity, synthesis, and smooth proofs;
- diagnostic computations, counterexamples, and `#print axioms` probes stay under `Toffoli/Audit/` and are never imported by public modules;
- internal leaves import their exact dependencies, never a public facade or `Toffoli.lean`;
- final public facades (`Toffoli.Bool`, `Toffoli.Gate`, `Toffoli.Decomposition`, `Toffoli.Parity`, `Toffoli.Synthesis`, and `Toffoli.Smooth`) remain thin; `Toffoli.lean` is an optional umbrella only;
- `Perm.AtomicWord` exposes the cheap decomposition witness/interface; `Perm.Decomposition` proves universality, and only tiny final glue leaves combine it with synthesis or smooth “from atoms” engines;
- focused leaf builds and necessary adjacent-consumer builds are the default;
- a full project build is reserved for build-configuration, public/high-fanout API, global notation/instance/simp changes, explicit milestone verification, and final integration.

## Proposed Library and Theorem Outline

Names below are design targets, not existing declarations. Final names should follow mathlib conventions and may change after API reconnaissance.

### Finite objects and component structure

- `BoolWord (ι)` or direct use of `ι → Bool`.
- `BoolPerm ι := Equiv.Perm (ι → Bool)`.
- coordinate reindexing equivalences induced by `ι ≃ κ`.
- ordinary equivalence composition and a separately typed one-to-one circuit/wiring derivation, with an evaluator into ordinary composition.
- component support/dependence predicates.
- fixing selected input coordinates.
- restriction to a face of a Boolean cube, including a closure condition ensuring the result is a permutation when required.
- extension by identity/dummy coordinates.
- canonical deletion of singleton factors after face restriction.
- semantic deletion of Boolean outputs, only with an explicit constancy/dummy certificate; this is distinct from singleton-factor deletion.

### Gate family and decomposition

- generalized Toffoli gate with controls and one target.
- proofs that the gate is an involution and therefore a permutation.
- identification of AND/NAND component conventions.
- atomic flip at a selected vertex and coordinate, stated as an edge transposition of the Boolean cube.
- Gray-code path construction between two Boolean words.
- decomposition of an arbitrary transposition using adjacent edge transpositions.
- decomposition of an arbitrary Boolean permutation into atomic flips, with the exact multiplication/composition order specified.

### Parity and universality

- parity/sign of a permutation extended by dummy variables.
- parity of a gate acting on fewer than all coordinates.
- lower-arity non-generation theorem with every exceptional arity handled.
- simulations of NOT and controlled-NOT from three-bit Toffoli using constants where justified.
- synthesis of generalized Toffoli or atomic flips from three-bit Toffoli with explicitly counted ancillas/constants.
- universality theorem stated via a closure relation that records fixed constants, component restriction, and deletion of dummy variables.
- a separate negative or qualified statement preventing that theorem from being read as unrestricted ancilla-free universality.

### Smooth extensions

- an explicit Boolean embedding into the selected circle model.
- a predicate saying a diffeomorphism extends a finite Boolean permutation on the embedded Boolean cube.
- a documented correction replacing the paper's nonassociative binary circle multiplication by the direct finite smooth control product.
- a smooth component gate extending the generalized Toffoli gate.
- smoothness and involutive inverse proof, packaged as a diffeomorphism.
- compatibility with reindexing and one-to-one component composition.
- construction extending an arbitrary Boolean permutation by composing atomic smooth extensions.
- the source-faithful existential circle theorem; any generic connected-manifold criterion is optional and separately hypothesized.

### Audit declarations and generated reports

- a paper-claim table linking each main claim to definitions/theorems and verification status.
- an axiom audit for exported main theorems using `#print axioms` or a maintained equivalent.
- executable small-arity examples where useful, without treating them as substitutes for proofs.

## Tentative Main-Theorem Dependency Graph

```text
finite indices + Boolean words
        |
        +--> component reindexing / one-to-one circuit semantics
        |
        +--> generalized Toffoli involutions
        |            |
        |            +--> lifted-gate sign --> lower-arity obstruction
        |
        +--> cube adjacency + Gray paths --> atomic-word interface
                         |                         |
                         |                         +--> synthesis from atoms
                         |                         +--> smooth extension from atoms
                         |
                         +--> heavy universal decomposition
                                      |
                                      +--> tiny discrete universality glue theorem
                                      +--> tiny smooth extension glue theorem

restriction + constants + dummy extension/deletion
        |
        +--> exact three-bit Toffoli simulations
                         |
                         +--> qualified three-bit universality

analytic complex Circle + Boolean embedding
        |
        +--> well-defined smooth atomic gate diffeomorphism
                         |
                         +--> compatibility with finite atomic flips
                                      |
                                      +--> main diffeomorphic extension theorem
```

## Paper Map

The source is present under `toffoli-1981/`. Printed pages below were checked against the supplied scan; declaration-level Lean links will be added as implementation proceeds.

| Paper location and claim | Proposed Lean artifact | Dependency | Planned disposition |
|---|---|---|---|
| Printed pp. 14–15, Goal 2.1: extend an invertible `Bⁿ → Bⁿ` over some connected `M` | extension predicate and existential theorem | smooth atomic gates, decomposition | Formalize the mathematical existence statement only |
| Printed pp. 15–16, §§2–3: componentwise extension/restriction | typed productwise restriction and extension notions | indexed products, explicit Boolean embedding | “Componentwise” preserves separate factors; it does not mean output `i` depends only on input `i` |
| Printed p. 16, §3: one-to-one composition and reindexing | typed circuit/wiring derivation and evaluation laws | finite equivalences | Keep distinct from ordinary semantic composition |
| Printed p. 16, §3: deletion of singleton-valued dummy variables | singleton deletion plus separate semantic dummy-output API | product decompositions | Do not conflate the two operations |
| Printed p. 17, Definition 4.1, Eq. (4.1), Remark 4.1: `θ⁽ⁿ⁾` | involutive generalized Toffoli equivalence | controls/target representation | Cover `n > 0` and decide an arity-zero API separately |
| Printed p. 17, Lemma 4.1: generation by `θ⁽ⁿ⁾` and `θ⁽¹⁾` | atomic flip and arbitrary-permutation decomposition | cube adjacency, Gray paths | Reconstruct the omitted exact word |
| Printed p. 18, Lemma 4.2, Eq. (4.2): circle extension `Θ⁽ⁿ⁾` | smooth involutive diffeomorphism | analytic `Circle`, finite control product | Correct the nonassociative binary-operation presentation |
| Printed p. 18, Theorem 4.1: extension over an existential connected manifold | main finite-to-smooth extension theorem | Lemmas 4.1–4.2 | Formalize without physical interpretation |
| Printed p. 20, Theorem 5.1: lower-order `θ` gates generate only even permutations | parity non-generation theorem | sign and dummy-coordinate lift | Re-derive, including boundary cases |
| Printed pp. 20–21, Theorem 5.2 and Fig. 7: `θ⁽³⁾` universality with restriction/deletion | resource-indexed closure theorem | clean-ancilla recursion, dummy operations | Correct source typos and verify the `2n - 3` bound |
| Printed p. 21, Theorem 5.3: smooth analogue using `Θ⁽³⁾` | qualified smooth synthesis theorem | circle gate, Theorem 5.2 | Reconstruct the one-line “parallels” proof |
| Printed pp. 18–20 mechanisms and pp. 21–23 Appendix/energy interpretation | documentation-only boundary | explicit physical model, if ever added | Exclude from verified core by default |

## Initial Correction and Unresolved-Point Log

This is an audit queue, not a finding that the paper is wrong. Every entry must later acquire a source location, evidence, and final disposition.

| ID | Issue to investigate | Risk | Required evidence before closure | Status |
|---|---|---|---|---|
| C-001 | Lemma 4.2 defines `x ∘ y = π(1-cos x)(1-cos y)/4` and claims all ring axioms except distributivity | The formula is periodic and hence well defined, but it is not associative and has no multiplicative identity; the iterated product is ambiguous | Formalize the required n-ary control directly as `π ∏ᵢ (1-cos xᵢ)/2`; document the counterexample `(π/2 ∘ π/2) ∘ π ≠ π/2 ∘ (π/2 ∘ π)` | Confirmed material correction; Lean work pending |
| C-002 | Does Eq. (4.2) define a smooth self-inverse map for every `n > 0`? | Smoothness alone is not a diffeomorphism | Two-sided inverse calculation, empty-product convention, and smoothness | Open |
| C-003 | Lemma 4.2 embeds Boolean `0,1` as circle angles `0,π`; does Eq. (4.2) recover Eq. (4.1) under all conventions? | Convention mismatch can reverse gate semantics | Evaluated truth table and quotient-point distinctness | Open |
| C-004 | Theorem 4.1 is existential in `M`; should any reusable generic-manifold theorem be attempted? | Accidentally strengthening “there exists connected `M`” to “every connected `M`” | Keep existential circle theorem primary; require independent hypotheses/proof for any generic result | Open |
| C-005 | Lemma 4.1 sketches a Gray-path endpoint exchange but gives no exact transposition word or composition direction | Informal order can yield the wrong permutation | Algebraic proof and exhaustive low-arity check | Open |
| C-006 | Definition 4.1 assumes `n > 0`; what API and results should exist at arity `0`, and how do `n=1,2` special cases interact with later theorems? | Cardinality/parity formulas may have exceptions | Separate lemmas or uniform proof covering each | Open |
| C-007 | Theorem 5.1 relies on `2^(n-i)` identical copies; what is the exact sign formula for extending an `i`-ary permutation to `n` bits? | Obstruction depends on the correct exponent | Derived sign formula and checked examples | Open |
| C-008 | Theorem 5.1 concerns lower-order AND/NAND gates, not arbitrary lower-arity permutations; what is the strongest correct generalization? | The theorem may be overgeneralized | Formalize the exact statement first, then prove any generalization separately | Open |
| C-009 | Theorem 5.2 claims at most `2n-3` constant-input deletions; what are their values, lifetimes, cleanliness, and corresponding outputs? | Resource-free universality may be falsely inferred | Explicit Fig. 7-based recursion and counted synthesis witness | Open |
| C-010 | Does restriction preserve bijectivity, or is a stable face hypothesis needed? | A restricted permutation need not map a face to itself | Precise closure/stability condition | Open |
| C-011 | When is output deletion legitimate? | Dropping a non-dummy component changes semantics | Dependence/identity proof for every deleted coordinate | Open |
| C-012 | The paper calls a manifold diffeomorphism the appropriate generalization of a bicontinuous function; where are only continuity versus smoothness actually established? | Terminology can obscure a proof obligation | Audit each result and keep homeomorphism/diffeomorphism claims separate | Open |
| C-013 | Are component-preservation claims literal or only up to coordinate reindexing? | Composition structure may be misstated | Typed statement and source diagram audit | Open |
| C-014 | Are physical realizability claims mathematical consequences of the extension theorem? | Category error between existence and mechanism | Keep separate absent a formal physical model | Open |
| C-015 | Theorem 5.2's proof on printed p. 21 writes the restriction of `φ⁽⁵⁾` as `B³ × {0}` while fixing one of five wires and claiming the other four implement `θ⁽⁴⁾` | The displayed type has only four total coordinates and cannot be a face of the five-wire circuit with four retained data wires | Correct to `B⁴ × {0}` and verify the Fig. 7 circuit algebraically | Confirmed source typo; Lean work pending |
| C-016 | Theorem 5.2's proof on printed p. 20 says “function `φ⁽⁵⁾` of Figure 4,” but the construction is Figure 7 | Incorrect cross-reference obscures the universality gadget | Cite and formalize Figure 7 | Confirmed source typo; documentation pending |
| C-017 | Theorem 5.2 claims at most `2n-3` constant inputs for every order `n` | The bound is negative for `n=1`; for `n=2`, one fixed wire cannot realize all two-bit permutations from three-bit Toffoli and wire permutations because the three-wire generators preserve Hamming-weight strata enough to obstruct, e.g., double NOT on the face | Prove the low-arity obstruction formally; state a corrected piecewise bound or require `3 ≤ n`; prove the remaining accounting | Confirmed material correction; exact replacement pending |
| C-018 | At the start of Lemma 4.1's proof (printed p. 17), the PDF says “By definition, `θ⁽ⁿ⁾` is a permutation” where the argument requires the arbitrary given `f⁽ⁿ⁾` | The published text names the wrong function | Retain the Markdown transcription's justified correction to `f⁽ⁿ⁾` and document it | Confirmed source typo |
| C-019 | Literal set inclusion `M ⊇ B` and the word “componentwise” are underspecified for Lean | It can be misread as a subtype requirement or coordinatewise independence | Use an explicit injective Boolean embedding/two distinct points; define componentwise interpolation on product factors without imposing false dependency restrictions | Confirmed specification correction |
| C-020 | Theorem 5.1's proof says every allowed proper-arity operation is even, while §3 also calls coordinate reindexing one-to-one composition | A coordinate swap on `B²` is an odd vertex permutation; the parity proof as written therefore fails at ambient arity two if free reindexings are generators | Prove the parity theorem for `n ≥ 3` with free reindexing, or treat reindexing as placement/conjugation; settle `n=0,1,2` separately | Confirmed proof gap; theorem disposition pending |
| C-021 | Lemma 4.1 says NOTs are “applied” to selected controls to obtain all edge atoms | A zero-controlled edge requires NOT conjugation both before and after `θ⁽ⁿ⁾`, not a one-sided application | Formalize the explicit conjugation and verify the edge transposition | Open proof obligation |
| C-022 | Theorem 5.3 says only that its proof “parallels” Theorem 5.2 | Fixing a smooth `Θ³` control at `π` gives a valid extension but not necessarily the paper's exact lower-order `Θ` away from Boolean points; the nonassociative operation also makes higher `Θ` ambiguous | State interpolation/equivalence results, not literal off-cube equality unless separately proved; reconstruct the stable-face smooth circuit | Confirmed proof gap; Lean work pending |
| C-023 | The natural finite model uses `Fin n → Circle`, but pinned mathlib lacks a turnkey finite-Pi `IsManifold` and diffeomorphism constructor | Assuming an instance could stall the smooth layer or pull heavy infrastructure into the core | In an early Stage 7 leaf, compare recursively nested binary products with an isolated finite-Pi manifold bridge; prove equivalence to the chosen component indexing | Open design obligation |

## Dependency and Environment Notes

### Versions and project setup

- `formal/lean-toolchain` pins `leanprover/lean4:v4.32.0`.
- `formal/lakefile.toml` pins mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`; `formal/lake-manifest.json` resolves the same commit.
- `formal/Toffoli/Smoke.lean` remains the Stage 1 diagnostic leaf. The thin root now imports the
  verified `Toffoli.Bool` facade; finite internal leaves import only exact dependencies.
- `Toffoli.Audit.Axioms.Finite` reports only `propext`, `Classical.choice`, and `Quot.sound` for
  representative exported finite declarations and is not imported publicly.
- Initial validation on 2026-07-17: after narrowing the smoke import, focused smoke output built in 2.02 s (309 jobs), the root output in 2.07 s (310 jobs), and a warm full build in 1.26 s (311 jobs). The first smoke attempt correctly failed on import ordering and was fixed before these successful results.

### Expected mathlib areas to investigate

- `Equiv.Perm`, finite permutations, transpositions, sign/parity, and generation.
- `Fin`, `Fintype`, `Finite`, finite function types, `Bool`, vectors, and cardinality lemmas.
- finite sets and coordinate-support APIs.
- Gray codes or hypercube paths, if present; otherwise a local reusable construction.
- products, Pi types, and reindexing equivalences.
- smooth manifolds, `ContMDiff`, smooth maps, Lie groups, circles/real modulo subgroups, and diffeomorphisms.
- quotient-lift APIs if the paper's angular formula is retained.

### Confirmed pinned mathlib surfaces

- `Mathlib.GroupTheory.Perm.Basic`: `Equiv.Perm`, swaps, and basic permutation operations.
- `Mathlib.GroupTheory.Perm.Sign`: `Equiv.Perm.sign`, `sign_swap`, conjugation invariance, product-congruence sign lemmas, and transposition factorization/induction.
- `Mathlib.Logic.Equiv.Basic` and `.Prod`: Pi reindexing plus dependent/product congruences.
- `Mathlib.Data.Fintype.Card` and `.BigOperators`: `Fintype.card_bool` and `Fintype.card_fun`.
- `Mathlib.InformationTheory.Hamming`: Hamming distance exists, but no ready-made Gray-path decomposition was found; a narrow local cube-path construction is still expected.
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
- Adapt the tentative low-fanout module graph to the APIs actually available; record focused build targets and avoid importing a broad mathlib umbrella where narrow imports suffice.
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
