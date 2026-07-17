# 1-SOURCE-AUDIT

Status: complete.

## Current Facts

- The source is available as `toffoli-1981/toffoli-1981.pdf` and a Markdown transcription at `toffoli-1981/toffoli-1981.md`, with seven extracted figures.
- The transcription identifies Tommaso Toffoli, “Bicontinuous Extensions of Invertible Combinatorial Functions,” *Mathematical Systems Theory* 14 (1981), 13–23.
- Its principal formal claims are Definition 4.1, Lemmas 4.1–4.2, Theorem 4.1, and Theorems 5.1–5.3. Section 3 supplies nonstandard componentwise restriction, one-to-one composition, reindexing, and dummy-variable terminology.
- The Lean project now lives under `formal/` and is intentionally separate from the source paper and Python shell.
- Lean 4.31.0 and 4.32.0 toolchains are installed. This project now pins Lean 4.32.0 (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`) with mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Direct `lean --version` and `lake --version` work. `elan show` aborts in the managed sandbox because its Rust timeout handler cannot write a file descriptor; this does not yet demonstrate a Lean/Lake build failure.
- Repository-root `BUILD-PLAN.md` requires narrow imports, low-dependency definition modules, heavy proof/audit leaves, thin public APIs, and focused builds by default.

## Updated Assumptions

- Use a `formal/` Lake project so Lean artifacts remain separate from the paper and the repository's small Python shell.
- Pin `leanprover/lean4:v4.32.0` and mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`; both have now passed this project's setup/build checks.
- Begin with a single narrow smoke leaf rather than pre-creating the entire planned module tree.
- Treat the Markdown as a navigable transcription, but use the PDF as the publication authority where the transcription, equations, or figures matter. The main statements and source corrections have now been checked directly.
- Theorem 4.1 is existential in a connected manifold `M`; it is not a theorem about every connected manifold.
- Theorem 5.2's `2n - 3` constant-input/deletion bound and Lemma 4.1's exact Gray-path permutation word require reconstruction rather than acceptance of the sketches.
- Prefer mathlib's analytic complex unit `Circle` to `AddCircle` for the smooth layer: the pinned library already supplies the manifold, Lie-group, and analytic exponential structures needed by the construction.
- Replace the paper's nonassociative binary circle multiplication with a documented direct finite control product; preserve Boolean interpolation, not unsupported off-cube equality.

## Big Picture Objective

Establish a source-grounded and reproducible baseline: an exact paper claim inventory, a correction/audit queue, a pinned minimal Lean/mathlib project, confirmed narrow imports, and a low-fanout module plan. Do not begin any substantive theorem implementation in this stage.

## Detailed Implementation Plan

- Compare the Markdown metadata, section structure, definitions, equations, and theorem statements against the supplied PDF.
- Normalize the main paper claims and record their exact locations, hypotheses, conventions, dependencies, proof gaps, and physical-language boundary.
- Update `goal-1/0-plan.md` with source-audit findings and corrected assumptions.
- Create `formal/lean-toolchain`, `formal/lakefile.toml`, a minimal namespace smoke leaf, and only the root import surface necessary to validate project wiring.
- Resolve and commit a Lake manifest with the exact mathlib revision.
- Inspect the pinned mathlib source for narrow modules covering finite permutations, sign/parity, finite function types, smooth manifolds, quotient circles, and diffeomorphisms; record findings without implementing project definitions.
- Run the minimal focused build, proof-hole/axiom scans, and whitespace/diff checks.

## Build Structure

- New setup files: `formal/lean-toolchain`, `formal/lakefile.toml`, and the generated `formal/lake-manifest.json`.
- New Lean leaf: `formal/Toffoli/Smoke.lean`, importing only `Mathlib.Logic.Equiv.Basic` and containing harmless compile-time examples.
- Root surface: `formal/Toffoli.lean`, importing only the smoke leaf for Stage 1 project validation. It must remain thin.
- No finite core, gate, decomposition, parity, synthesis, or smooth implementation module is created in this stage.
- Focused target: `cd formal && lake build Toffoli.Smoke`.
- Adjacent public target: `cd formal && lake build Toffoli`.
- A full build is justified once in this stage because build configuration and the root public target are new.

## No-Cheating Checks

- The smoke leaf must not contain any project theorem masquerading as a verified paper result.
- No `sorry`, `admit`, `axiom`, or unexplained local assumption may appear in Lean source.
- A successful dependency fetch alone is not a build result; Lean must compile both the leaf and root target.
- A compiled import is only evidence that the API exists, not that any mathematical paper claim is proved.

## Boundary Checks

- Keep paper-source notes in planning/documentation, not in runtime definitions.
- Keep physical mechanism and energy claims classified as out of the verified mathematical core.
- Do not create umbrella imports from internal leaves.
- Do not introduce global simp attributes, instances, or notation in the smoke module.
- Do not edit neighboring projects or reuse their generated build outputs as proof that this project builds.

## Completion Requirements

- The paper version and exact source artifacts are recorded, and the Markdown's main statements are checked against the PDF.
- Every in-scope main claim has a source location and a normalized audit disposition in `0-plan.md`.
- Open ambiguity/correction items include concrete evidence obligations rather than vague concerns.
- Lean and mathlib are pinned to compatible exact versions, and `lake-manifest.json` records the resolved mathlib commit.
- `lake build Toffoli.Smoke`, `lake build Toffoli`, and the one-time initial full `lake build` all succeed with commands and outcomes recorded.
- Initial API reconnaissance names declarations/modules actually present in the pinned dependency.
- Proof-hole/axiom scans and `git diff --check` pass, with documentation-only guardrail hits classified.
- No substantive definition or proof from a later stage is implemented.

## Stage Results

### Source audit

- Checked the 11-page supplied scan (printed pp. 13–23) against the Markdown transcription for all in-scope definitions and theorem statements.
- Completed the paper map in `0-plan.md` with printed-page locations and normalized dispositions.
- Confirmed and logged the following material source issues:
  - Lemma 4.2's binary circle multiplication is representative-independent and smooth but neither associative nor unital. For example, `(π ∘ π/2) ∘ π/2 = π/4`, while `π ∘ (π/2 ∘ π/2) = π(2-√2)/4`.
  - Theorem 5.2 cites Figure 4 instead of Figure 7 and gives the dimensionally impossible face `B³ × {0}` instead of `B⁴ × {0}`.
  - The `2n-3` constant bound fails as written at `n=1,2`; its exact corrected range/bound remains a Stage 6 proof obligation.
  - Theorem 5.1's parity proof needs special treatment at ambient arity two if free coordinate reindexing is included as an allowed operation.
  - Lemma 4.1 omits the exact palindromic edge-transposition word and the required two-sided NOT conjugations.
  - Theorem 5.3's one-line “parallel” proof establishes valid interpolation only after its smooth stable-face construction is reconstructed; it cannot silently assert equality of ambiguous off-cube `Θ⁽ⁿ⁾` formulas.
- Recorded that literal `M ⊇ B` becomes an explicit two-point embedding and that “componentwise” preserves product factors rather than imposing coordinatewise independence.
- Classified the gear/cam/no-dead-point, work/heat, dissipation, and physical-realizability language outside the verified core.

### Lean and dependency setup

- Created `formal/lean-toolchain` with Lean 4.32.0.
- Created `formal/lakefile.toml` with exact mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997` and generated a manifest resolving the same revision.
- Created the narrow leaf `formal/Toffoli/Smoke.lean` (only `Mathlib.Logic.Equiv.Basic`) and thin root `formal/Toffoli.lean`; no later-stage mathematical definition was added.
- Updated `.gitignore` for Lake output and documented project status/build commands in `README.md`.

### Pinned API reconnaissance

- Finite layer: `Equiv.Perm`/swaps in `Mathlib.GroupTheory.Perm.Basic`; sign, swap factorization, conjugation invariance, and product sign lemmas in `Mathlib.GroupTheory.Perm.Sign`; Pi/product reindexing in `Mathlib.Logic.Equiv.Basic` and `.Prod`; Boolean/function cardinalities in `Mathlib.Data.Fintype.Card` and `.BigOperators`.
- Gray layer: mathlib has Hamming distance but no source-ready Gray-path endpoint-transposition theorem was found, so the project will own a narrow simple-path construction.
- Smooth layer: `Circle` is an analytic one-manifold and Lie group in `Mathlib.Geometry.Manifold.Instances.Sphere`; `Circle.exp` is analytic; `Diffeomorph` and product operations are in `Mathlib.Geometry.Manifold.Diffeomorph`.
- `AddCircle` is not the preferred smooth representation because the pinned generic quotient-manifold source explicitly leaves smoothness of quotient actions as a TODO.
- The pinned source provides `AddCircle.homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle` and identifies quotient representatives with `Circle.exp`, allowing the complex-circle formalization to be related precisely to the paper.
- General finite Pi charted-space ingredients exist, but no turnkey finite-Pi `IsManifold`/diffeomorphism stack was found. Stage 7 must isolate the choice between recursively nested binary products and a proved finite-Pi manifold API.

### Commands and results

- `cd formal && lake update`: succeeded after explicit network approval; dependency cache decompression completed successfully.
- Initial `lake build Toffoli.Smoke`: failed because imports followed the module documentation under Lean 4.32.0. Imports were moved first; no theorem code was affected.
- `lake build +Toffoli.Smoke:olean`: succeeded after narrowing the import (309 jobs, 2.02 s, maximum RSS 1,113,980 KiB).
- `lake build +Toffoli:olean`: succeeded (310 jobs, 2.07 s, maximum RSS 1,105,628 KiB).
- Warm `lake build`: succeeded (311 jobs, 1.26 s, maximum RSS 865,340 KiB).
- Project Lean scan for `sorry`, `admit`, and declared `axiom`: no hits.
- Trailing-whitespace scan and `git diff --check`: passed.
- No `#print axioms` result is required yet because Stage 1 exports no mathematical theorem.

### Fold-back

- Updated `0-plan.md` with the pinned environment, source corrections, exact page map, preferred complex-circle model, and a lower-fanout dependency graph.
- Stage 2 should freeze the Boolean word/permutation representation and distinguish circuit wiring, stable-face restriction, singleton deletion, and semantic dummy-output deletion before downstream gate or synthesis work.
