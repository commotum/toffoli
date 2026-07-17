import Mathlib.Logic.Equiv.Set
import Toffoli.Component.Face

/-!
# Restricting equivalences to specified source and target sets

The paper correctly observes that restricting an invertible map requires both an intended source
and an intended target. The exact membership equivalence below is the evidence that the ambient
equivalence maps one set onto the other.
-/

namespace Toffoli

universe u v

namespace Component

variable {α : Type u} {β : Type v}

/-- Restrict an equivalence to source and target sets that it maps exactly onto one another. -/
def restrictEquiv (e : α ≃ β) (source : Set α) (target : Set β)
    (maps : ∀ x, e x ∈ target ↔ x ∈ source) : source ≃ target where
  toFun x := ⟨e x, (maps x).2 x.property⟩
  invFun y :=
    ⟨e.symm y, (maps (e.symm y)).1 (by
      rw [e.apply_symm_apply]
      exact y.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y

@[simp]
theorem restrictEquiv_apply (e : α ≃ β) (source : Set α) (target : Set β)
    (maps : ∀ x, e x ∈ target ↔ x ∈ source) (x : source) :
    restrictEquiv e source target maps x = ⟨e x, (maps x).2 x.property⟩ :=
  rfl

@[simp]
theorem restrictEquiv_symm_apply_val (e : α ≃ β) (source : Set α) (target : Set β)
    (maps : ∀ x, e x ∈ target ↔ x ∈ source) (y : target) :
    ↑((restrictEquiv e source target maps).symm y) = e.symm y :=
  rfl

/-- Restrict a Boolean permutation to a face that it preserves exactly. -/
def restrictFaces {ι : Type u} (p : BoolPerm ι) (source target : Face ι)
    (maps : ∀ x, p x ∈ target.carrier ↔ x ∈ source.carrier) : source.Points ≃ target.Points :=
  restrictEquiv p source.carrier target.carrier maps

@[simp]
theorem restrictFaces_apply_val {ι : Type u} (p : BoolPerm ι) (source target : Face ι)
    (maps : ∀ x, p x ∈ target.carrier ↔ x ∈ source.carrier) (x : source.Points) :
    ↑(restrictFaces p source target maps x) = p x :=
  rfl

/-- Restrict a Boolean permutation to a face that it preserves exactly. -/
def restrictFace {ι : Type u} (p : BoolPerm ι) (face : Face ι)
    (stable : ∀ x, p x ∈ face.carrier ↔ x ∈ face.carrier) : Equiv.Perm face.Points :=
  restrictFaces p face face stable

@[simp]
theorem restrictFace_apply_val {ι : Type u} (p : BoolPerm ι) (face : Face ι)
    (stable : ∀ x, p x ∈ face.carrier ↔ x ∈ face.carrier) (x : face.Points) :
    ↑(restrictFace p face stable x) = p x :=
  rfl

end Component

end Toffoli
