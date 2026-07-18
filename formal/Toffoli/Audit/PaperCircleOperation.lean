import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Toffoli.Smooth.CircleModel

/-!
# Audit of the paper's rejected binary circle operation

This non-public leaf checks the operation asserted in Lemma 4.2 of the paper.  On angular
representatives it is

`x ∘ y = π ((1 - cos x) / 2) ((1 - cos y) / 2)`.

Defining it on the complex unit circle makes representative independence explicit.  The operation
is smooth, but it is not associative and admits neither a left nor a right identity.  Consequently
it cannot carry the claimed (non-distributive) ring structure and is not used by the public smooth
extension.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli.Audit.PaperCircleOperation

open CircleExtension

/-- The binary operation from Lemma 4.2, defined directly on circle points. -/
def paperMul (z w : Circle) : Circle :=
  Circle.exp (Real.pi * signal z * signal w)

/-- Pulling `paperMul` back along the angular map gives exactly the paper's formula. -/
theorem paperMul_exp (x y : ℝ) :
    paperMul (Circle.exp x) (Circle.exp y) =
      Circle.exp
        (Real.pi * ((1 - Real.cos x) / 2) * ((1 - Real.cos y) / 2)) := by
  simp [paperMul, signal_exp]

/-- The angular formula is invariant under independent changes of representative by `2πℤ`. -/
theorem paperMul_exp_add_periods (x y : ℝ) (m n : ℤ) :
    paperMul
        (Circle.exp (x + m * (2 * Real.pi)))
        (Circle.exp (y + n * (2 * Real.pi))) =
      paperMul (Circle.exp x) (Circle.exp y) := by
  have hx : Circle.exp (x + m * (2 * Real.pi)) = Circle.exp x :=
    Circle.exp_eq_exp.mpr ⟨m, rfl⟩
  have hy : Circle.exp (y + n * (2 * Real.pi)) = Circle.exp y :=
    Circle.exp_eq_exp.mpr ⟨n, rfl⟩
  rw [hx, hy]

/-- The rejected operation is nevertheless a smooth map of two circle inputs. -/
theorem contMDiff_paperMul :
    ContMDiff
      (ManifoldSpace.circle.modelWithCorners.prod ManifoldSpace.circle.modelWithCorners)
      ManifoldSpace.circle.modelWithCorners ∞
      (fun p : Circle × Circle => paperMul p.1 p.2) := by
  apply contMDiff_circleExp.comp
  exact
    (contMDiff_const.mul (contMDiff_signal.comp contMDiff_fst)).mul
      (contMDiff_signal.comp contMDiff_snd)

theorem paperMul_comm (z w : Circle) : paperMul z w = paperMul w z := by
  apply congrArg Circle.exp
  ring

private theorem paperMul_right_pi (z : Circle) :
    paperMul z (Circle.exp Real.pi) = Circle.exp (Real.pi * signal z) := by
  unfold paperMul
  rw [signal_exp, Real.cos_pi]
  norm_num

private theorem exp_pi_div_four_ne_exp_pi_div_three :
    Circle.exp (Real.pi / 4) ≠ Circle.exp (Real.pi / 3) := by
  intro h
  have heq : Real.pi / 4 = Real.pi / 3 :=
    Circle.exp_injOn_Icc (a := 0) (b := Real.pi) (by nlinarith [Real.pi_pos])
      (by constructor <;> nlinarith [Real.pi_pos])
      (by constructor <;> nlinarith [Real.pi_pos]) h
  nlinarith [Real.pi_pos]

/-- A circle point whose selector signal is exactly `1/3`. -/
private def thirdSignalPoint : Circle :=
  Circle.exp (Real.arccos (1 / 3))

@[simp]
private theorem signal_thirdSignalPoint : signal thirdSignalPoint = 1 / 3 := by
  rw [thirdSignalPoint, signal_exp, Real.cos_arccos]
  · norm_num
  · norm_num
  · norm_num

private theorem paperMul_assoc_left_value :
    paperMul (paperMul thirdSignalPoint (Circle.exp Real.pi)) (Circle.exp Real.pi) =
      Circle.exp (Real.pi / 4) := by
  have hinner : paperMul thirdSignalPoint (Circle.exp Real.pi) =
      Circle.exp (Real.pi / 3) := by
    rw [paperMul_right_pi, signal_thirdSignalPoint]
    apply congrArg Circle.exp
    ring
  rw [hinner]
  rw [paperMul_right_pi, signal_exp, Real.cos_pi_div_three]
  apply congrArg Circle.exp
  ring

private theorem paperMul_assoc_right_value :
    paperMul thirdSignalPoint
        (paperMul (Circle.exp Real.pi) (Circle.exp Real.pi)) =
      Circle.exp (Real.pi / 3) := by
  have hinner : paperMul (Circle.exp Real.pi) (Circle.exp Real.pi) =
      Circle.exp Real.pi := by
    rw [paperMul_right_pi, signal_exp, Real.cos_pi]
    norm_num
  rw [hinner]
  rw [paperMul_right_pi, signal_thirdSignalPoint]
  apply congrArg Circle.exp
  ring

/-- The operation in Lemma 4.2 is not associative. -/
theorem paperMul_not_associative :
    ¬∀ x y z : Circle, paperMul (paperMul x y) z = paperMul x (paperMul y z) := by
  intro h
  have hassoc := h thirdSignalPoint (Circle.exp Real.pi) (Circle.exp Real.pi)
  rw [paperMul_assoc_left_value, paperMul_assoc_right_value] at hassoc
  exact exp_pi_div_four_ne_exp_pi_div_three hassoc

private theorem signal_quarter_turns :
    signal (Circle.exp (Real.pi / 2)) = signal (Circle.exp (-Real.pi / 2)) := by
  rw [signal_exp, signal_exp, show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.cos_neg]

private theorem paperMul_quarter_turns_eq (e : Circle) :
    paperMul (Circle.exp (Real.pi / 2)) e =
      paperMul (Circle.exp (-Real.pi / 2)) e := by
  simp only [paperMul, signal_quarter_turns]

private theorem exp_quarter_turns_ne :
    Circle.exp (Real.pi / 2) ≠ Circle.exp (-Real.pi / 2) := by
  intro h
  have heq : Real.pi / 2 = -Real.pi / 2 :=
    Circle.exp_injOn_Icc (a := -Real.pi / 2) (b := Real.pi / 2)
      (by nlinarith [Real.pi_pos])
      (by constructor <;> nlinarith [Real.pi_pos])
      (by constructor <;> nlinarith [Real.pi_pos]) h
  nlinarith [Real.pi_pos]

/-- There is no right identity for the paper's operation. -/
theorem paperMul_no_right_identity :
    ¬∃ e : Circle, ∀ z : Circle, paperMul z e = z := by
  rintro ⟨e, he⟩
  apply exp_quarter_turns_ne
  exact (he (Circle.exp (Real.pi / 2))).symm.trans
    ((paperMul_quarter_turns_eq e).trans (he (Circle.exp (-Real.pi / 2))))

/-- There is no left identity for the paper's operation. -/
theorem paperMul_no_left_identity :
    ¬∃ e : Circle, ∀ z : Circle, paperMul e z = z := by
  rintro ⟨e, he⟩
  apply paperMul_no_right_identity
  exact ⟨e, fun z => (paperMul_comm z e).trans (he z)⟩

/-- In particular, the operation admits no two-sided multiplicative identity. -/
theorem paperMul_no_identity :
    ¬∃ e : Circle,
      (∀ z : Circle, paperMul e z = z) ∧ (∀ z : Circle, paperMul z e = z) := by
  rintro ⟨e, -, he⟩
  exact paperMul_no_right_identity ⟨e, he⟩

end Toffoli.Audit.PaperCircleOperation
