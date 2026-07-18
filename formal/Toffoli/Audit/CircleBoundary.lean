import Mathlib.Data.Fin.VecNotation
import Toffoli.Smooth.CircleGate

/-!
# Circle-extension boundary checks

These non-public checks pin down the empty-control case, the Boolean angle convention, recursive
component order, and the generic interpolation theorem.  The reusable proofs remain in the public
circle leaves.
-/

namespace Toffoli.Audit

open Toffoli CircleExtension

/-! ## Empty product and Boolean angle convention -/

example (p : CirclePower 0) : p = 0 :=
  Subsingleton.elim _ _

example (p : CirclePower 0) : controlProduct 0 p = 1 :=
  controlProduct_zero p

example : boolPoint false = Circle.exp 0 :=
  boolPoint_false_eq_exp_zero

example : boolPoint true = Circle.exp Real.pi :=
  boolPoint_true_eq_exp_pi

example : signal (Circle.exp 0) = 0 := by
  rw [← boolPoint_false_eq_exp_zero]
  norm_num [signal, boolPoint]

example : signal (Circle.exp Real.pi) = 1 := by
  rw [← boolPoint_true_eq_exp_pi]
  norm_num [signal, boolPoint]

/-! ## Zero-control gate is Boolean NOT at both embedded values -/

example :
    gate 0 (embed 1 ![false]) = embed 1 ![true] := by
  rw [gate_interpolates_thetaSucc]
  congr 1
  decide

example :
    gate 0 (embed 1 ![true]) = embed 1 ![false] := by
  rw [gate_interpolates_thetaSucc]
  congr 1
  decide

/-! ## Controls precede the final target -/

example (n : ℕ) (p : CirclePower (n + 1)) (i : Fin n) :
    coord (n + 1) (gate n p) i.castSucc = coord (n + 1) p i.castSucc :=
  coord_gate_control n p i

example (n : ℕ) (p : CirclePower (n + 1)) :
    coord (n + 1) (gate n p) (Fin.last n) =
      (coord (n + 1) p (Fin.last n))⁻¹ *
        Circle.exp (Real.pi * controlProduct n p.1) :=
  coord_gate_target n p

/-! ## Generic interpolation signature -/

example (n : ℕ) (x : Fin (n + 1) → Bool) :
    gateDiffeomorph n (embed (n + 1) x) =
      embed (n + 1) (AndNand.thetaSucc n x) :=
  gateDiffeomorph_interpolates_thetaSucc n x

end Toffoli.Audit
