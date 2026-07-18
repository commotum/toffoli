# Goal 1 Execution Loop

Use this protocol for future maintenance or an explicitly added implementation stage. Stages 1–9
in `goal-1/0-plan.md` are complete; do not reopen them or infer new scope without a concrete
requirement.

## Repeatable Loop

1. Sync current state with actual files and tests.
2. Update `0-plan.md` with current facts before starting the next stage.
3. Select the first incomplete stage.
4. Create or refresh `goal-1/[INDEX]-[SHORTHAND].md` from the stage template.
5. Implement only that stage.
6. Add verification and no-cheating checks.
7. Run the smallest focused builds and adjacent-consumer checks that cover the stage, plus milestone/full verification only when required by `BUILD-PLAN.md`, and run whitespace/diff checks.
8. Record results in the stage file.
9. Fold results back into `0-plan.md`.
10. Continue toward the original objective. If stopping for the session, leave the goal in a resumable state with current evidence, next experiments, unblock actions, and assumptions to challenge.

## Invariants

- Do not narrow the user's objective without saying so.
- Do not mark a stage complete without evidence.
- Do not use tests or green checks as evidence unless they cover the requirement.
- Prefer small, low-complexity stages that narrow uncertainty.
- Convert blockers into work items: decompose them, route around them, or turn them into proof and verification tasks.
- Preserve the distinction between implementation, verifier, diagnostic, and fallback paths.
- Treat the paper as a mathematical source, not a formal specification.
- Do not begin a proof from a paraphrase when the precise paper statement or construction has not been source-audited.
- Never use `sorry`, fabricated mathlib declarations, or unexplained project-specific axioms to cross a proof gap.
- Keep finite permutations separate from smooth extensions, ordinary composition separate from one-to-one composition, restrictions separate from dummy deletion, and existence separate from physical realization.
- Make empty/low arities, Boolean/circle conventions, quotient well-definedness, and auxiliary-resource counts explicit.
- Update the paper map, correction log, dependency notes, and axiom audit whenever a stage changes the evidence.
- A stage file records what was actually verified; it must not present intended work as completed work.
- Read and follow repository-root `BUILD-PLAN.md` for every stage that changes Lean code.
- Optimize the module graph before proof work: cheap definitions low, heavy proofs and diagnostics in leaves, and the public API thin.
- Prefer a new narrow leaf to an edit in a high-fanout module; never import the umbrella API from internal implementation modules.
- Avoid broad global simp rules, instances, notation, or automation changes unless a recorded requirement justifies their rebuild cost.

## Current-State and Verification Checklist

At the start of each loop:

- Inspect the worktree and do not overwrite unrelated user changes.
- Read the current plan, prior stage results, source map, and open correction items.
- Inspect the actual pinned toolchain and available mathlib declarations before naming APIs in implementation.
- Re-run or reproduce the last relevant focused check if the current state may have drifted.
- Identify the lowest owner module, high-fanout files to avoid, focused build target, and adjacent consumers before changing Lean code.

At the end of each loop, choose checks proportional to the stage and record exact commands and outcomes:

- focused Lean build or test for every changed module;
- adjacent-consumer builds that exercise any changed public surface;
- full `lake build` only for configuration, public/high-fanout API, global notation/instance/simp changes, explicit milestones, or final integration;
- small exhaustive/evaluation checks where they validate conventions but do not replace proofs;
- repository-wide placeholder and axiom searches;
- `#print axioms` or equivalent audit for newly exported main results;
- `git diff --check` and an intentional diff review;
- source-map and correction-log updates.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New tests or commands required.

## Build Structure

- New or touched Lean modules and why each owns its declarations.
- High-fanout modules intentionally avoided.
- Classification of declarations as low-level API, proof-side, diagnostic/audit, fallback, or temporary scaffolding.
- Focused build command and required adjacent-consumer builds.
- Whether a full build trigger applies under `BUILD-PLAN.md`.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden fallback paths.

## Boundary Checks

- Runtime/public API/proof-side/diagnostic boundaries relevant to this stage.
- Import-direction, global-automation, and forbidden-shortcut checks.

## Completion Requirements

- Requirement-by-requirement checks.
- Required test commands.
- Documentation updates required.

## Stage Results

- Fill in at the end of the stage.
- Include tests run and outcomes.
- Include what was learned.
- Include focused/adjacent/full builds actually run and any material timing or fanout finding.
- Include what should change in `0-plan.md` before the next stage.
```

## Stop/Resume Handoff

When stopping before the full goal is complete, leave the active stage file and `0-plan.md` aligned. Record:

- the last verified commit/worktree state;
- exact commands last run and their results;
- current mathematical facts versus conjectures;
- open source ambiguities and correction-log identifiers;
- the smallest next proof, experiment, or API investigation;
- any blocker, the attempted routes, and concrete unblock actions;
- assumptions the next session should challenge first.

Do not call the goal complete while an in-scope claim is silently omitted. Carry open issues forward as explicit staged work.
