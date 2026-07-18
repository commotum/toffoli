import Toffoli.Perm.AtomicWord
import Toffoli.Smooth.CircleAtomic

/-!
# Smooth evaluation of atomic Boolean words

This file is the cheap composition layer between the literal atomic circle extension and the
heavy finite-permutation decomposition theorem.  Atomic diffeomorphisms act from left to right,
matching the convention of `Toffoli.AtomicWord.eval` exactly.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- Step-level wrapper around the lower analytic edge theorem. -/
theorem atomicStepDiffeomorph_interpolates {n : ℕ} (step : AtomicStep (Fin n)) :
    Interpolates (atomicDiffeomorph step.base step.target) step.perm := by
  rw [AtomicStep.perm]
  exact atomicDiffeomorph_interpolates step.base step.target

/-- Evaluate a word of atomic Boolean edges as smooth circle diffeomorphisms.  The list head acts
first. -/
def evalAtomicWord {n : ℕ} : List (AtomicStep (Fin n)) →
    Diffeomorph (circlePowerModel n) (circlePowerModel n)
      (CirclePower n) (CirclePower n) ∞
  | [] => Diffeomorph.refl (circlePowerModel n) (CirclePower n) ∞
  | step :: steps =>
      (atomicDiffeomorph step.base step.target).trans (evalAtomicWord steps)

@[simp]
theorem evalAtomicWord_nil {n : ℕ} :
    evalAtomicWord ([] : List (AtomicStep (Fin n))) =
      Diffeomorph.refl (circlePowerModel n) (CirclePower n) ∞ :=
  rfl

@[simp]
theorem evalAtomicWord_cons {n : ℕ} (step : AtomicStep (Fin n))
    (steps : List (AtomicStep (Fin n))) :
    evalAtomicWord (step :: steps) =
      (atomicDiffeomorph step.base step.target).trans (evalAtomicWord steps) :=
  rfl

theorem evalAtomicWord_append {n : ℕ} (first second : List (AtomicStep (Fin n))) :
    evalAtomicWord (first ++ second) =
      (evalAtomicWord first).trans (evalAtomicWord second) := by
  induction first with
  | nil => simp
  | cons step steps ih =>
      simp only [List.cons_append, evalAtomicWord_cons, ih]
      apply Diffeomorph.ext
      intro p
      rfl

/-- Smooth word evaluation agrees with finite atomic-word evaluation on every embedded Boolean
point. -/
theorem evalAtomicWord_interpolates {n : ℕ} (steps : List (AtomicStep (Fin n))) :
    Interpolates (evalAtomicWord steps) (AtomicWord.eval steps) := by
  induction steps with
  | nil =>
      intro x
      rfl
  | cons step steps ih =>
      intro x
      change
        evalAtomicWord steps
            (atomicDiffeomorph step.base step.target (embed n x)) =
          embed n (AtomicWord.eval steps (step.perm x))
      rw [atomicStepDiffeomorph_interpolates step x]
      exact ih (step.perm x)

end CircleExtension
end Toffoli
