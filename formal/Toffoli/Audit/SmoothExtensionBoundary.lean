import Mathlib.Data.Fin.VecNotation
import Toffoli.Smooth.Extension

/-!
# Direct smooth-extension boundary checks

These non-public checks pin down empty arity, the one-circle atomic NOT, smooth word composition
order, and the exact signatures of the main direct circle-extension results.  They do not test or
import the separate qualified smooth-synthesis path.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli.Audit

open Toffoli CircleExtension

/-! ## Empty arity is the identity on the singleton empty product -/

example (p : BoolPermN 0) :
    extension p = Diffeomorph.refl (circlePowerModel 0) (CirclePower 0) ∞ :=
  extension_zero_eq_refl p

example (p : BoolPermN 0) (x : CirclePower 0) : extension p x = x := by
  rw [extension_zero_eq_refl]
  rfl

example (p : BoolPermN 0) :
    Interpolates (Diffeomorph.refl (circlePowerModel 0) (CirclePower 0) ∞) p :=
  refl_zero_interpolates p

/-! ## The sole one-bit component is smoothly negated -/

def oneBitStep : AtomicStep (Fin 1) :=
  ⟨![false], 0⟩

example :
    atomicDiffeomorph oneBitStep.base oneBitStep.target (embed 1 ![false]) =
      embed 1 ![true] := by
  rw [atomicStepDiffeomorph_interpolates]
  congr 1

example :
    atomicDiffeomorph oneBitStep.base oneBitStep.target (embed 1 ![true]) =
      embed 1 ![false] := by
  rw [atomicStepDiffeomorph_interpolates]
  congr 1
  decide

example (p : CirclePower 1) : atomicActivation oneBitStep.base oneBitStep.target p = 1 := by
  simp [atomicActivation, oneBitStep]

example (p : CirclePower 1) :
    coord 1 (atomicDiffeomorph oneBitStep.base oneBitStep.target p) oneBitStep.target =
      (coord 1 p oneBitStep.target)⁻¹ * Circle.exp Real.pi := by
  rw [atomicDiffeomorph_apply, coord_atomicMap_target]
  simp [atomicActivation, oneBitStep]

/-! ## Smooth words use the same head-first serial order as finite words -/

def firstTwoBitStep : AtomicStep (Fin 2) :=
  ⟨![false, false], 0⟩

def secondTwoBitStep : AtomicStep (Fin 2) :=
  ⟨![true, false], 1⟩

example (p : CirclePower 2) :
    evalAtomicWord [firstTwoBitStep, secondTwoBitStep] p =
      atomicDiffeomorph secondTwoBitStep.base secondTwoBitStep.target
        (atomicDiffeomorph firstTwoBitStep.base firstTwoBitStep.target p) :=
  rfl

example :
    evalAtomicWord [firstTwoBitStep, secondTwoBitStep] (embed 2 ![false, false]) =
      embed 2 ![true, true] := by
  rw [evalAtomicWord_interpolates]
  congr 1
  decide

example :
    evalAtomicWord ([firstTwoBitStep] ++ [secondTwoBitStep]) =
      (evalAtomicWord [firstTwoBitStep]).trans (evalAtomicWord [secondTwoBitStep]) :=
  evalAtomicWord_append _ _

/-! ## Main extension and concrete connected-circle witness signatures -/

example {n : ℕ} (p : BoolPermN n) : Interpolates (extension p) p :=
  extension_interpolates p

example {n : ℕ} (p : BoolPermN n) :
    ∃ F : Diffeomorph (circlePowerModel n) (circlePowerModel n)
        (CirclePower n) (CirclePower n) ∞,
      Interpolates F p :=
  exists_extension p

example {n : ℕ} (p : BoolPermN n) :
    IsConnected (Set.univ : Set ManifoldSpace.circle.Carrier) ∧
      IsManifold ManifoldSpace.circle.modelWithCorners ω ManifoldSpace.circle.Carrier ∧
        ∃ F : Diffeomorph (circlePowerModel n) (circlePowerModel n)
            (CirclePower n) (CirclePower n) ∞,
          Interpolates F p :=
  connected_circle_witness p

end Toffoli.Audit
