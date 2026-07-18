import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Toffoli.Perm.Decomposition
import Toffoli.Smooth.AtomicWord

/-!
# Diffeomorphic circle extensions of finite Boolean permutations

This is the deliberately heavy terminal leaf of the direct smooth-extension construction.  It
combines the finite atomic decomposition theorem with the cheap smooth atomic-word evaluator.
The component manifold exhibited here is the connected complex unit circle; no claim is made
that connectedness alone supplies such extensions on every connected manifold.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- The chosen smooth extension of a finite Boolean permutation, obtained by evaluating its
chosen atomic decomposition in the same left-to-right order. -/
noncomputable def extension {n : ℕ} (p : BoolPermN n) :
    Diffeomorph (circlePowerModel n) (circlePowerModel n)
      (CirclePower n) (CirclePower n) ∞ :=
  evalAtomicWord (AtomicWord.decompose p)

/-- The chosen smooth extension agrees with the original permutation on every embedded Boolean
point. -/
theorem extension_interpolates {n : ℕ} (p : BoolPermN n) :
    Interpolates (extension p) p := by
  simpa only [extension, AtomicWord.eval_decompose] using
    evalAtomicWord_interpolates (AtomicWord.decompose p)

/-- Every finite Boolean permutation therefore has a diffeomorphic extension on the corresponding
finite product of circles. -/
theorem exists_extension {n : ℕ} (p : BoolPermN n) :
    ∃ F : Diffeomorph (circlePowerModel n) (circlePowerModel n)
        (CirclePower n) (CirclePower n) ∞,
      Interpolates F p :=
  ⟨extension p, extension_interpolates p⟩

private theorem atomicWord_fin_zero_eq_nil (steps : List (AtomicStep (Fin 0))) : steps = [] := by
  cases steps with
  | nil => rfl
  | cons step _ => exact Fin.elim0 step.target

/-- At arity zero the chosen extension is the identity diffeomorphism of the singleton empty
product; no target coordinate or atomic gate is manufactured. -/
theorem extension_zero_eq_refl (p : BoolPermN 0) :
    extension p =
      Diffeomorph.refl (circlePowerModel 0) (CirclePower 0) ∞ := by
  rw [extension, atomicWord_fin_zero_eq_nil (AtomicWord.decompose p)]
  rfl

/-- Explicit empty-arity interpolation by the identity on the empty circle product. -/
theorem refl_zero_interpolates (p : BoolPermN 0) :
    Interpolates
      (Diffeomorph.refl (circlePowerModel 0) (CirclePower 0) ∞) p := by
  simpa only [extension_zero_eq_refl] using extension_interpolates p

/-- Source-faithful connected-manifold witness: the single component space is the connected
complex unit circle, and the extension acts on its recursively modeled `n`-fold product.  This
statement deliberately does not assert that every connected manifold admits the construction. -/
theorem connected_circle_witness {n : ℕ} (p : BoolPermN n) :
    IsConnected (Set.univ : Set ManifoldSpace.circle.Carrier) ∧
      IsManifold ManifoldSpace.circle.modelWithCorners ω ManifoldSpace.circle.Carrier ∧
        ∃ F : Diffeomorph (circlePowerModel n) (circlePowerModel n)
            (CirclePower n) (CirclePower n) ∞,
          Interpolates F p :=
  ⟨isConnected_univ, inferInstance, exists_extension p⟩

end CircleExtension
end Toffoli
