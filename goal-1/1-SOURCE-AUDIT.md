# 1-SOURCE-AUDIT

Status: in progress.

## Current Facts

- The source is available as `toffoli-1981/toffoli-1981.pdf` and a Markdown transcription at `toffoli-1981/toffoli-1981.md`, with seven extracted figures.
- The transcription identifies Tommaso Toffoli, “Bicontinuous Extensions of Invertible Combinatorial Functions,” *Mathematical Systems Theory* 14 (1981), 13–23.
- Its principal formal claims are Definition 4.1, Lemmas 4.1–4.2, Theorem 4.1, and Theorems 5.1–5.3. Section 3 supplies nonstandard componentwise restriction, one-to-one composition, reindexing, and dummy-variable terminology.
- There is no Lean project in this repository yet.
- Lean 4.31.0 and 4.32.0 toolchains are installed. Neighboring formalization projects successfully pin Lean 4.32.0 with mathlib tag `v4.32.0`, resolved to commit `81a5d257c8e410db227a6665ed08f64fea08e997` in their current manifests.
- Direct `lean --version` and `lake --version` work. `elan show` aborts in the managed sandbox because its Rust timeout handler cannot write a file descriptor; this does not yet demonstrate a Lean/Lake build failure.
- Repository-root `BUILD-PLAN.md` requires narrow imports, low-dependency definition modules, heavy proof/audit leaves, thin public APIs, and focused builds by default.

## Updated Assumptions

- Use a `formal/` Lake project so Lean artifacts remain separate from the paper and the repository's small Python shell.
- Tentatively pin `leanprover/lean4:v4.32.0` and the exact mathlib commit already resolved by a neighboring project, subject to an actual clean setup/build check here.
- Begin with a single narrow smoke leaf rather than pre-creating the entire planned module tree.
- Treat the Markdown as a navigable transcription, but use the PDF as the publication authority where the transcription, equations, or figures matter.
- Theorem 4.1 is existential in a connected manifold `M`; it is not a theorem about every connected manifold.
- Theorem 5.2's `2n - 3` constant-input/deletion bound and Lemma 4.1's exact Gray-path permutation word require reconstruction rather than acceptance of the sketches.

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
- New Lean leaf: `formal/Toffoli/Smoke.lean`, containing imports and harmless compile-time examples only.
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

- Pending.
