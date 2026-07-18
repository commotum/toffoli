import Mathlib.Geometry.Manifold.Diffeomorph
import Toffoli.Gate.AndNand
import Toffoli.Smooth.CircleModel

/-!
# A smooth circle extension of the AND/NAND gate

For `n` controls and target `z`, the target component is

`z⁻¹ * exp (π * controlProduct controls)`.

This is the complex-unit-circle form of the paper's angular formula
`-x_target + π ∏ᵢ (1 - cos xᵢ) / 2`.  The direct `n`-ary product removes the paper's
nonassociative binary-operation ambiguity.  The map is visibly self-inverse because its controls
are fixed.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- The corrected smooth gate with `n` controls and the last circle as target. -/
def gate (n : ℕ) (p : CirclePower (n + 1)) : CirclePower (n + 1) :=
  (p.1, p.2⁻¹ * Circle.exp (Real.pi * controlProduct n p.1))

@[simp]
theorem gate_controls (n : ℕ) (p : CirclePower (n + 1)) : (gate n p).1 = p.1 :=
  rfl

@[simp]
theorem gate_target (n : ℕ) (p : CirclePower (n + 1)) :
    (gate n p).2 = p.2⁻¹ * Circle.exp (Real.pi * controlProduct n p.1) :=
  rfl

theorem gate_involutive (n : ℕ) : Function.Involutive (gate n) := by
  rintro ⟨controls, target⟩
  simp [gate, mul_inv_rev, mul_assoc]

theorem contMDiff_gate (n : ℕ) :
    ContMDiff (circlePowerModel (n + 1)) (circlePowerModel (n + 1)) ∞ (gate n) := by
  apply ContMDiff.prodMk contMDiff_fst
  apply contMDiff_snd.inv.mul
  apply contMDiff_circleExp.comp
  exact contMDiff_const.mul (contMDiff_controlProduct n |>.comp contMDiff_fst)

/-- The smooth gate packaged as a self-inverse diffeomorphism. -/
def gateDiffeomorph (n : ℕ) :
    Diffeomorph (circlePowerModel (n + 1)) (circlePowerModel (n + 1))
      (CirclePower (n + 1)) (CirclePower (n + 1)) ∞ where
  toEquiv :=
    { toFun := gate n
      invFun := gate n
      left_inv := gate_involutive n
      right_inv := gate_involutive n }
  contMDiff_toFun := contMDiff_gate n
  contMDiff_invFun := contMDiff_gate n

@[simp]
theorem gateDiffeomorph_apply (n : ℕ) (p : CirclePower (n + 1)) :
    gateDiffeomorph n p = gate n p :=
  rfl

@[simp]
theorem gateDiffeomorph_symm_apply (n : ℕ) (p : CirclePower (n + 1)) :
    (gateDiffeomorph n).symm p = gate n p :=
  rfl

theorem coord_gate_control (n : ℕ) (p : CirclePower (n + 1)) (i : Fin n) :
    coord (n + 1) (gate n p) i.castSucc = coord (n + 1) p i.castSucc := by
  simp [coord, gate]

@[simp]
theorem coord_gate_target (n : ℕ) (p : CirclePower (n + 1)) :
    coord (n + 1) (gate n p) (Fin.last n) =
      (coord (n + 1) p (Fin.last n))⁻¹ *
        Circle.exp (Real.pi * controlProduct n p.1) := by
  simp [coord, gate]

end CircleExtension
end Toffoli
