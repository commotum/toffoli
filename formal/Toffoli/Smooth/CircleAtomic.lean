import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Diffeomorph
import Toffoli.Perm.AtomicWord
import Toffoli.Smooth.CircleCoordinates

/-!
# Smooth extensions of literal Boolean cube edges

For a Boolean base word and target coordinate, every non-target coordinate supplies a positive or
negative smooth selector according to the base pattern.  Their direct finite product is one
exactly on the matching Boolean control pattern and zero on every other Boolean pattern.  The
target is updated by inversion followed by the selected phase, while all other coordinates are
unchanged.

This gives a globally smooth self-inverse map.  The finite atomic permutation and its smooth
extension remain separate objects, related by the explicit `Interpolates` predicate.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- Select the embedded Boolean point requested by `expected`. -/
def literalSignal (expected : Bool) (z : Circle) : ℝ :=
  if expected then signal z else 1 - signal z

@[simp]
theorem literalSignal_boolPoint (expected actual : Bool) :
    literalSignal expected (boolPoint actual) = if actual = expected then 1 else 0 := by
  rw [literalSignal, signal_boolPoint]
  cases expected <;> cases actual <;> norm_num

theorem contMDiff_literalSignal (expected : Bool) :
    ContMDiff ManifoldSpace.circle.modelWithCorners (modelWithCornersSelf ℝ ℝ) ∞
      (literalSignal expected) := by
  cases expected
  · exact contMDiff_const.sub contMDiff_signal
  · exact contMDiff_signal

/-- The direct product of the literals on every coordinate except the target. -/
def atomicActivation {n : ℕ} (base : BoolVec n) (target : Fin n) (p : CirclePower n) : ℝ :=
  ∏ i ∈ Finset.univ.erase target, literalSignal (base i) (coord n p i)

theorem contMDiff_atomicActivation {n : ℕ} (base : BoolVec n) (target : Fin n) :
    ContMDiff (circlePowerModel n) (modelWithCornersSelf ℝ ℝ) ∞
      (atomicActivation base target) := by
  apply ContMDiff.prod
  intro i _hi
  exact (contMDiff_literalSignal (base i)).comp (contMDiff_coord n i)

@[simp]
theorem atomicActivation_embed {n : ℕ} (base x : BoolVec n) (target : Fin n) :
    atomicActivation base target (embed n x) =
      if ∀ i, i ≠ target → x i = base i then 1 else 0 := by
  rw [atomicActivation]
  simp only [coord_embed, literalSignal_boolPoint]
  by_cases h : ∀ i, i ≠ target → x i = base i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    rw [if_pos]
    exact h i (Finset.ne_of_mem_erase hi)
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hit, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hit, Finset.mem_univ i⟩) (by simp [hi])

/-- Smooth extension of the literal cube edge named by `base` and `target`. -/
def atomicMap {n : ℕ} (base : BoolVec n) (target : Fin n) (p : CirclePower n) :
    CirclePower n :=
  assemble n fun i =>
    if i = target then
      (coord n p i)⁻¹ * Circle.exp (Real.pi * atomicActivation base target p)
    else coord n p i

@[simp]
theorem coord_atomicMap_target {n : ℕ} (base : BoolVec n) (target : Fin n)
    (p : CirclePower n) :
    coord n (atomicMap base target p) target =
      (coord n p target)⁻¹ * Circle.exp (Real.pi * atomicActivation base target p) := by
  simp [atomicMap]

@[simp]
theorem coord_atomicMap_of_ne {n : ℕ} (base : BoolVec n) (target : Fin n)
    (p : CirclePower n) {i : Fin n} (hi : i ≠ target) :
    coord n (atomicMap base target p) i = coord n p i := by
  simp [atomicMap, hi]

@[simp]
theorem atomicActivation_atomicMap {n : ℕ} (base : BoolVec n) (target : Fin n)
    (p : CirclePower n) :
    atomicActivation base target (atomicMap base target p) =
      atomicActivation base target p := by
  unfold atomicActivation
  apply Finset.prod_congr rfl
  intro i hi
  rw [coord_atomicMap_of_ne]
  exact Finset.ne_of_mem_erase hi

theorem contMDiff_atomicMap {n : ℕ} (base : BoolVec n) (target : Fin n) :
    ContMDiff (circlePowerModel n) (circlePowerModel n) ∞ (atomicMap base target) := by
  unfold atomicMap
  apply contMDiff_assemble
  intro i
  by_cases hi : i = target
  · subst i
    simp only [if_pos]
    apply (contMDiff_coord n target).inv.mul
    apply contMDiff_circleExp.comp
    exact contMDiff_const.mul (contMDiff_atomicActivation base target)
  · simp only [if_neg hi]
    exact contMDiff_coord n i

theorem atomicMap_involutive {n : ℕ} (base : BoolVec n) (target : Fin n) :
    Function.Involutive (atomicMap base target) := by
  intro p
  apply coord_ext
  intro i
  by_cases hi : i = target
  · subst i
    rw [coord_atomicMap_target, coord_atomicMap_target, atomicActivation_atomicMap]
    simp [mul_inv_rev, mul_assoc]
  · rw [coord_atomicMap_of_ne _ _ _ hi, coord_atomicMap_of_ne _ _ _ hi]

/-- The atomic smooth map packaged as a self-inverse diffeomorphism. -/
def atomicDiffeomorph {n : ℕ} (base : BoolVec n) (target : Fin n) :
    Diffeomorph (circlePowerModel n) (circlePowerModel n) (CirclePower n) (CirclePower n) ∞ where
  toEquiv :=
    { toFun := atomicMap base target
      invFun := atomicMap base target
      left_inv := atomicMap_involutive base target
      right_inv := atomicMap_involutive base target }
  contMDiff_toFun := contMDiff_atomicMap base target
  contMDiff_invFun := contMDiff_atomicMap base target

@[simp]
theorem atomicDiffeomorph_apply {n : ℕ} (base : BoolVec n) (target : Fin n)
    (p : CirclePower n) :
    atomicDiffeomorph base target p = atomicMap base target p :=
  rfl

/-- A smooth diffeomorphism interpolates a finite Boolean permutation through the fixed
embedding. -/
def Interpolates {n : ℕ}
    (F : Diffeomorph (circlePowerModel n) (circlePowerModel n)
      (CirclePower n) (CirclePower n) ∞)
    (p : BoolPermN n) : Prop :=
  ∀ x, F (embed n x) = embed n (p x)

private theorem atomic_boolPoint_inv (b : Bool) : (boolPoint b)⁻¹ = boolPoint b := by
  cases b <;> simp [boolPoint]

private theorem atomic_boolPoint_not (b : Bool) :
    (boolPoint b)⁻¹ * Circle.exp Real.pi = boolPoint (!b) := by
  cases b <;> simp [boolPoint]

private theorem atomicEdge_eq_if_controls {n : ℕ} (base x : BoolVec n) (target : Fin n) :
    atomicEdge base target x =
      if ∀ i, i ≠ target → x i = base i then x.flipAt target else x := by
  by_cases h : ∀ i, i ≠ target → x i = base i
  · rw [if_pos h]
    by_cases ht : x target = base target
    · have hx : x = base := by
        funext i
        by_cases hi : i = target
        · subst i
          exact ht
        · exact h i hi
      subst x
      exact atomicEdge_apply_base base target
    · have ht' : x target = !(base target) := by
        cases hx : x target <;> cases hb : base target <;> simp_all
      have hx : x = base.flipAt target := by
        funext i
        by_cases hi : i = target
        · subst i
          simpa using ht'
        · rw [BoolWord.flipAt_apply_of_ne _ hi]
          exact h i hi
      subst x
      rw [atomicEdge_apply_flipAt, BoolWord.flipAt_involutive]
  · rw [if_neg h]
    apply atomicEdge_apply_of_ne
    · intro hx
      apply h
      intro i _hi
      simp [hx]
    · intro hx
      apply h
      intro i hi
      rw [hx, BoolWord.flipAt_apply_of_ne _ hi]

private theorem atomicMap_embed_eq_if_controls {n : ℕ} (base x : BoolVec n)
    (target : Fin n) :
    atomicMap base target (embed n x) =
      embed n (if ∀ i, i ≠ target → x i = base i then x.flipAt target else x) := by
  apply coord_ext
  intro i
  by_cases h : ∀ j, j ≠ target → x j = base j
  · rw [if_pos h]
    by_cases hi : i = target
    · subst i
      rw [coord_atomicMap_target, atomicActivation_embed, if_pos h]
      simpa [BoolWord.flipAt_apply_self] using atomic_boolPoint_not (x target)
    · rw [coord_atomicMap_of_ne _ _ _ hi]
      simp [BoolWord.flipAt_apply_of_ne, hi]
  · rw [if_neg h]
    by_cases hi : i = target
    · subst i
      rw [coord_atomicMap_target, atomicActivation_embed, if_neg h]
      simpa using atomic_boolPoint_inv (x target)
    · rw [coord_atomicMap_of_ne _ _ _ hi]

/-- The atomic diffeomorphism agrees exactly with its Boolean edge transposition on the embedded
cube. -/
theorem atomicDiffeomorph_interpolates {n : ℕ} (step : AtomicStep (Fin n)) :
    Interpolates (atomicDiffeomorph step.base step.target) step.perm := by
  intro x
  rw [atomicDiffeomorph_apply, atomicMap_embed_eq_if_controls,
    AtomicStep.perm, atomicEdge_eq_if_controls]

end CircleExtension
end Toffoli
