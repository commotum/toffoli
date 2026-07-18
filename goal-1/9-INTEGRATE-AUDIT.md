# 9-INTEGRATE-AUDIT

Status: complete.

## Current Facts

- Stages 1–8 have focused builds, boundary checks, and representative axiom audits.
- The finite/discrete public facades remain under `Toffoli.lean`; the smooth public facade is
  `Toffoli.Smooth`.  Keeping the latter separate prevents ordinary discrete imports from pulling
  in the roughly 2500-job manifold dependency graph.
- `Toffoli.Smooth` imports only the direct arbitrary-permutation extension leaf and the terminal
  qualified three-bit synthesis leaf.  Audit modules are not publicly imported.
- The direct main extension and qualified smooth synthesis results use only `propext`,
  `Classical.choice`, and `Quot.sound` in their recorded axiom output.
- The explicit clean all-surfaces milestone passed: 2607 jobs, 1099.53 s wall, 16568.58 s user,
  1714.06 s system, and 3009048 KiB maximum RSS.
- The final import graph has 71 modules and 138 internal edges, with no cycle, reverse smooth
  dependency, umbrella import in an implementation leaf, audit import leak, or unreachable
  implementation module.
- Repository-wide Lean scans find no proof holes, project axioms, or `unsafe` declarations.
- `Toffoli.Audit.PaperCircleOperation` now machine-checks the original binary circle operation's
  representative invariance, smoothness, nonassociativity, and absence of either one-sided
  identity; its axiom audit is standard-only.
- The final warm setup/facade/boundary/axiom set passed in 3.38 s, and plain `lake build` passed in
  2.21 s.

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

### BUILD-PLAN workflow

Routine development uses a warm leaf-first feedback loop.  Representative low- or terminal-leaf
targets are:

```text
cd formal
lake build Toffoli.Bool.Finite
lake build Toffoli.Gate.Toffoli
lake build Toffoli.Perm.Decomposition
lake build Toffoli.Synthesis.Universality
lake build Toffoli.Smooth.Extension
lake build Toffoli.Smooth.Synthesis.Universality
```

After a public-surface change, build only the adjacent facade (`Toffoli` or `Toffoli.Smooth`).
Audit leaves stay outside those facades.  `lake clean` is not part of the routine loop because it
rebuilds mathlib; it is reserved for the following final all-surfaces milestone:

```text
cd formal
lake clean
lake build \
  Toffoli \
  Toffoli.Smooth \
  Toffoli.Audit.FiniteBoundary \
  Toffoli.Audit.GateBoundary \
  Toffoli.Audit.GrayBoundary \
  Toffoli.Audit.ParityBoundary \
  Toffoli.Audit.UniversalityBoundary \
  Toffoli.Audit.CircleBoundary \
  Toffoli.Audit.PaperCircleOperation \
  Toffoli.Audit.SmoothExtensionBoundary \
  Toffoli.Audit.SmoothSynthesisBoundary \
  Toffoli.Audit.Axioms.Finite \
  Toffoli.Audit.Axioms.Gate \
  Toffoli.Audit.Axioms.Decomposition \
  Toffoli.Audit.Axioms.Parity \
  Toffoli.Audit.Axioms.Universality \
  Toffoli.Audit.Axioms.Circle \
  Toffoli.Audit.Axioms.PaperCircleOperation \
  Toffoli.Audit.Axioms.SmoothExtension \
  Toffoli.Audit.Axioms.SmoothSynthesis
```

This explicit list is necessary because the default Lake target is only the discrete `Toffoli`
facade.  Setup-only validation remains available separately as `lake build Toffoli.Smoke`.

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

- The clean all-surfaces build passed all 2607 jobs.  `/usr/bin/time` recorded 1099.53 s wall,
  16568.58 s user, 1714.06 s system, and 3009048 KiB maximum RSS.  The high cold-build cost is why
  routine work follows the focused targets above.
- All main-result `#print axioms` output is confined to `propext`, `Classical.choice`, and
  `Quot.sound`; there is no project-specific axiom.
- The 71-module, 138-edge internal import graph is acyclic.  It has no discrete-to-smooth reverse
  edge, no implementation leaf importing an umbrella, no public module importing an audit, and no
  unreachable implementation module.
- Lean-source scans found no `sorry`, `admit`, project `axiom`, or `unsafe` declaration.
- `Toffoli.Audit.PaperCircleOperation` proves independent-period invariance of the paper's angular
  formula, its smoothness and commutativity, its nonassociativity, and the absence of left, right,
  or two-sided identities. Its focused build passed in 5.05 s and its axiom leaf in 4.56 s.
- The final warm target set—including setup smoke, both facades, every boundary leaf, the
  paper-operation correction, and every axiom leaf—passed in 3.38 s with 1115716 KiB maximum RSS.
  Plain default `lake build` passed 962 jobs in 2.21 s.
- The source PDF has a non-executable mode and tracked macOS metadata has been removed. Final
  warning, whitespace, and diff checks pass.
