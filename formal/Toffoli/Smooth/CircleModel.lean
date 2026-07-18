import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Recursive products of the complex unit circle

This file fixes the smooth model used for the paper's circle construction.  Boolean `false` and
`true` are embedded as `1` and `-1`, corresponding to the angles `0` and `π`.  Products are nested
on the right:

`CirclePower (n + 1) = CirclePower n × Circle`.

The zero-fold product is the zero-dimensional Euclidean space, which is a singleton.  This avoids
assuming a finite-Pi manifold instance that is not available in the pinned mathlib version.

The control signal is `(1 - re z) / 2`.  `controlProduct` is a direct finite product of these
signals; it deliberately does not iterate the nonassociative binary operation asserted in the
paper.  No angle representative is chosen: the signal is defined on the complex unit-circle point
itself, so invariance modulo `2π` is built into the definition.  `signal_exp` proves that pulling
the definition back along the angular map gives the paper's cosine formula.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- The type-and-instance data needed to form recursive products of smooth spaces. -/
structure ManifoldSpace where
  Tangent : Type
  Model : Type
  Carrier : Type
  [normedAddCommGroup : NormedAddCommGroup Tangent]
  [normedSpace : NormedSpace ℝ Tangent]
  [modelTopology : TopologicalSpace Model]
  modelWithCorners : ModelWithCorners ℝ Tangent Model
  [carrierTopology : TopologicalSpace Carrier]
  [chartedSpace : ChartedSpace Model Carrier]
  isManifold : IsManifold modelWithCorners ω Carrier

namespace ManifoldSpace

theorem finrank_real_complex_fact : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
  Complex.finrank_real_complex_fact

attribute [local instance] finrank_real_complex_fact

instance (X : ManifoldSpace) : NormedAddCommGroup X.Tangent := X.normedAddCommGroup
instance (X : ManifoldSpace) : NormedSpace ℝ X.Tangent := X.normedSpace
instance (X : ManifoldSpace) : TopologicalSpace X.Model := X.modelTopology
instance (X : ManifoldSpace) : TopologicalSpace X.Carrier := X.carrierTopology
instance (X : ManifoldSpace) : ChartedSpace X.Model X.Carrier := X.chartedSpace
instance (X : ManifoldSpace) : IsManifold X.modelWithCorners ω X.Carrier := X.isManifold

/-- The complex unit circle with its pinned analytic one-manifold structure. -/
@[reducible]
def circle : ManifoldSpace where
  Tangent := EuclideanSpace ℝ (Fin 1)
  Model := EuclideanSpace ℝ (Fin 1)
  Carrier := Circle
  modelWithCorners := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))
  isManifold := inferInstance

/-- A singleton smooth space, used as the empty product. -/
@[reducible]
def point : ManifoldSpace where
  Tangent := EuclideanSpace ℝ (Fin 0)
  Model := EuclideanSpace ℝ (Fin 0)
  Carrier := EuclideanSpace ℝ (Fin 0)
  modelWithCorners := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 0))
  isManifold := inferInstance

/-- Binary products of packaged smooth spaces. -/
@[reducible]
def prod (X Y : ManifoldSpace) : ManifoldSpace where
  Tangent := X.Tangent × Y.Tangent
  Model := ModelProd X.Model Y.Model
  Carrier := X.Carrier × Y.Carrier
  modelWithCorners := X.modelWithCorners.prod Y.modelWithCorners
  isManifold := IsManifold.prod X.Carrier Y.Carrier

/-- The recursively nested product of `n` circles. -/
@[reducible]
def circlePower : ℕ → ManifoldSpace
  | 0 => point
  | n + 1 => prod (circlePower n) circle

end ManifoldSpace

attribute [local instance] ManifoldSpace.finrank_real_complex_fact

/-- The carrier of the recursively nested product of `n` circles. -/
abbrev CirclePower (n : ℕ) := (ManifoldSpace.circlePower n).Carrier

/-- The smooth model with corners for `CirclePower n`. -/
abbrev circlePowerModel (n : ℕ) := (ManifoldSpace.circlePower n).modelWithCorners

/-- The paper's Boolean embedding: `false` is angle `0`, and `true` is angle `π`. -/
def boolPoint : Bool → Circle
  | false => 1
  | true => -1

@[simp]
theorem circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Subtype.ext
  exact Complex.exp_pi_mul_I

@[simp]
theorem boolPoint_false_eq_exp_zero : boolPoint false = Circle.exp 0 := by
  simp [boolPoint]

@[simp]
theorem boolPoint_true_eq_exp_pi : boolPoint true = Circle.exp Real.pi := by
  simp [boolPoint]

/-- Componentwise embedding of a Boolean vector into a recursive circle product. -/
def embed : (n : ℕ) → (Fin n → Bool) → CirclePower n
  | 0, _ => 0
  | n + 1, x => (embed n (Fin.init x), boolPoint (x (Fin.last n)))

/-- Read coordinate `i` from the recursive product. -/
def coord : (n : ℕ) → CirclePower n → Fin n → Circle
  | 0, _, i => Fin.elim0 i
  | n + 1, p, i => Fin.lastCases p.2 (fun j => coord n p.1 j) i

@[simp]
theorem coord_embed (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    coord n (embed n x) i = boolPoint (x i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [coord, embed]
      · simpa only [coord, embed, Fin.lastCases_castSucc, Fin.init] using
          ih (Fin.init x) j

theorem boolPoint_injective : Function.Injective boolPoint := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact (Circle.neg_ne_self 1 h.symm).elim
  · exact (Circle.neg_ne_self 1 h).elim
  · rfl

theorem embed_injective (n : ℕ) : Function.Injective (embed n) := by
  intro x y h
  funext i
  apply boolPoint_injective
  rw [← coord_embed n x i, ← coord_embed n y i, h]

/-- The real selector signal: it is `0` at angle `0` and `1` at angle `π`. -/
def signal (z : Circle) : ℝ := (1 - (z : ℂ).re) / 2

@[simp]
theorem signal_exp (x : ℝ) : signal (Circle.exp x) = (1 - Real.cos x) / 2 := by
  rw [signal, Circle.coe_exp, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re]

@[simp]
theorem signal_boolPoint (b : Bool) : signal (boolPoint b) = if b then 1 else 0 := by
  cases b <;> norm_num [signal, boolPoint]

theorem contMDiff_signal :
    ContMDiff ManifoldSpace.circle.modelWithCorners (modelWithCornersSelf ℝ ℝ) ∞ signal := by
  have hre :
      ContMDiff ManifoldSpace.circle.modelWithCorners (modelWithCornersSelf ℝ ℝ) ∞
        fun z : Circle => (z : ℂ).re :=
    Complex.reCLM.contDiff.contMDiff.comp contMDiff_coe_sphere
  exact (contMDiff_const.sub hre).div_const 2

/-- The corrected direct `n`-ary control product.  The empty product is `1`. -/
def controlProduct : (n : ℕ) → CirclePower n → ℝ
  | 0, _ => 1
  | n + 1, p => controlProduct n p.1 * signal p.2

@[simp]
theorem controlProduct_zero (p : CirclePower 0) : controlProduct 0 p = 1 :=
  rfl

theorem contMDiff_controlProduct (n : ℕ) :
    ContMDiff (circlePowerModel n) (modelWithCornersSelf ℝ ℝ) ∞ (controlProduct n) := by
  induction n with
  | zero => exact contMDiff_const
  | succ n ih =>
      exact (ih.comp contMDiff_fst).mul (contMDiff_signal.comp contMDiff_snd)

theorem controlProduct_eq_prod_signal (n : ℕ) (p : CirclePower n) :
    controlProduct n p = ∏ i : Fin n, signal (coord n p i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [controlProduct, Fin.prod_univ_castSucc]
      simp only [coord, Fin.lastCases_castSucc, Fin.lastCases_last]
      rw [ih]

@[simp]
theorem controlProduct_embed (n : ℕ) (x : Fin n → Bool) :
    controlProduct n (embed n x) = if ∀ i, x i = true then 1 else 0 := by
  rw [controlProduct_eq_prod_signal]
  simp only [coord_embed, signal_boolPoint]
  by_cases h : ∀ i, x i = true
  · simp [h]
  · have hex : ∃ i, x i ≠ true := by simpa only [not_forall] using h
    obtain ⟨i, hi⟩ := hex
    have hfalse : x i = false := Bool.eq_false_of_not_eq_true hi
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hfalse])

end CircleExtension
end Toffoli
