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

@[simp]
theorem boolPoint_inv (b : Bool) : (boolPoint b)⁻¹ = boolPoint b := by
  cases b <;> simp [boolPoint]

@[simp]
theorem boolPoint_not (b : Bool) :
    (boolPoint b)⁻¹ * Circle.exp Real.pi = boolPoint (!b) := by
  cases b <;> simp [boolPoint]

/-- On the embedded Boolean cube, the smooth gate is exactly the AND/NAND permutation. -/
theorem gate_interpolates_thetaSucc (n : ℕ) (x : Fin (n + 1) → Bool) :
    gate n (embed (n + 1) x) = embed (n + 1) (AndNand.thetaSucc n x) := by
  apply Prod.ext
  · change embed n (Fin.init x) = embed n (Fin.init (AndNand.thetaSucc n x))
    congr 1
    funext i
    exact (AndNand.thetaSucc_apply_control n x i).symm
  · change
      (boolPoint (x (Fin.last n)))⁻¹ *
          Circle.exp (Real.pi * controlProduct n (embed n (Fin.init x))) =
        boolPoint (AndNand.thetaSucc n x (Fin.last n))
    rw [controlProduct_embed]
    by_cases h : ∀ i : Fin n, x i.castSucc = true
    · have hinit : ∀ i : Fin n, Fin.init x i = true := h
      rw [if_pos hinit]
      rw [AndNand.thetaSucc_apply_target, if_pos h]
      simpa using boolPoint_not (x (Fin.last n))
    · have hinit : ¬∀ i : Fin n, Fin.init x i = true := h
      rw [if_neg hinit]
      rw [AndNand.thetaSucc_apply_target, if_neg h]
      simp

/-- Diffeomorphism-level form of `gate_interpolates_thetaSucc`. -/
theorem gateDiffeomorph_interpolates_thetaSucc (n : ℕ) (x : Fin (n + 1) → Bool) :
    gateDiffeomorph n (embed (n + 1) x) = embed (n + 1) (AndNand.thetaSucc n x) :=
  gate_interpolates_thetaSucc n x

theorem gate_bijective (n : ℕ) : Function.Bijective (gate n) :=
  (gateDiffeomorph n).toEquiv.bijective

end CircleExtension
end Toffoli
