# 9-INTEGRATE-AUDIT

Status: in progress.

## Current Facts

- Stages 1–8 have focused builds, boundary checks, and representative axiom audits.
- The finite/discrete public facades remain under `Toffoli.lean`; the smooth public facade is
  `Toffoli.Smooth`.  Keeping the latter separate prevents ordinary discrete imports from pulling
  in the roughly 2500-job manifold dependency graph.
- `Toffoli.Smooth` imports only the direct arbitrary-permutation extension leaf and the terminal
  qualified three-bit synthesis leaf.  Audit modules are not publicly imported.
- The direct main extension and qualified smooth synthesis results use only `propext`,
  `Classical.choice`, and `Quot.sound` in their recorded axiom output.
- Repository-wide final scans, a clean milestone build, public examples, final paper-map review,
  and reproducibility documentation still need one integrated pass before completion.

## Updated Assumptions

- The discrete and smooth facades should remain separate public entry points; making the root
  umbrella import manifolds would violate the explicit compile-time objective without adding a
  theorem.
- A final full-library build must cover unimported diagnostic leaves as well as both public
  facades.  If the default Lake target does not do so, the verification command will name the
  facades and all axiom/boundary audit targets explicitly.
- Documentation guardrail occurrences of words such as `axiom`, `sorry`, or `unsafe` are not proof
  holes; Lean-source declarations and placeholders are forbidden.

## Big Picture Objective

Stabilize the proved modules as a coherent reusable library, close every paper/correction/axiom
audit item, and record a reproducible final build without sacrificing the incremental dependency
boundaries required by `BUILD-PLAN.md`.

## Detailed Implementation Plan

- Review namespaces, declarations, facade imports, and module comments for stale or duplicate APIs.
- Complete the paper map and correction log with declaration-level dispositions.
- Add or refresh user-facing examples only where they exercise a public distinction not already
  covered by the non-public boundary modules.
- Run repository-wide proof-hole, project-axiom, unsafe, reverse-import, umbrella-import, warning,
  and whitespace scans.
- Build the discrete facade, smooth facade, every boundary audit, and every axiom audit; then run
  the justified final `lake build` milestone and record timings/fanout.
- Verify the pinned toolchain, mathlib revision, manifest, and documented setup commands.
- Review the final diff and repository status, then mark this stage and the overall goal complete
  only if every in-scope paper claim has a verified, corrected, rejected, or explicitly
  out-of-scope disposition.

## Build Structure

- No new mathematical core module is planned.
- Public changes are limited to thin facade/documentation surfaces if the audit finds a concrete
  omission.
- Diagnostic additions remain under `Toffoli/Audit`; they are never imported by a public facade.
- Focused verification targets are `Toffoli`, `Toffoli.Smooth`, each `Toffoli.Audit.*Boundary`, and
  each `Toffoli.Audit.Axioms.*` leaf.
- A full project build is required because this is the final integration milestone.

## No-Cheating Checks

- Do not hide an unresolved paper claim by deleting it from the map.
- Do not treat a successful discrete root build as coverage of the isolated smooth graph.
- Do not weaken theorem statements during cleanup or replace certified restriction/deletion with
  an unproved projection.
- Do not add the smooth facade to the discrete root merely to force build coverage.

## Boundary Checks

- Empty and low arities remain represented in every relevant public result.
- Finite permutations and diffeomorphisms remain linked by `Interpolates`, never coerced into one
  another.
- Theorem 5.3 remains explicitly qualified by constants, returned auxiliaries, smooth-face
  restriction, and deletion; no ancilla-free or off-cube higher-gate equality is introduced.
- Physical mechanisms remain documentation-only and outside the verified core.

## Completion Requirements

- Public facades and all boundary/axiom audits build from the pinned environment.
- The final full project build passes and its scope is recorded.
- Repository-wide Lean scans find no `sorry`, `admit`, unexplained project `axiom`, or `unsafe`
  declaration in completed modules.
- No discrete/core module imports `Toffoli.Smooth` or a smooth implementation leaf.
- Every correction-log entry has a final disposition, and every in-scope main paper claim maps to
  a declaration or documented correction/rejection.
- Main theorem axiom output is recorded and contains no project-specific axiom.
- `git diff --check`, warning review, and final status/diff review pass.

## Stage Results

- Pending final integration verification.
