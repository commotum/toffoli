import Toffoli.Component.Restriction
import Toffoli.Component.Tensor

/-!
# Fixed faces and dummy component deletion

This file separates two notions:

* `fixRightEquiv` canonically inserts or removes coordinates whose type has become singleton-valued
  after restricting to a fixed face;
* `RightDummy` certifies that Boolean output coordinates are semantically constant before a
  projection is described as dummy deletion.
-/

namespace Toffoli

universe u v w

namespace Component

variable {ι : Type u} {κ : Type v} {α : Type w}

/-- Insert fixed right coordinates, equivalently delete their singleton factors from the face. -/
def fixRightEquiv (c : BoolWord κ) : BoolWord ι ≃ (Face.right (ι := ι) c).Points where
  toFun x :=
    ⟨BoolWord.sumEquiv.symm (x, c),
      (Face.mem_right_iff (ι := ι) c _).2 fun _ => rfl⟩
  invFun x := (BoolWord.sumEquiv x.val).1
  left_inv x := by
    funext i
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr k => exact ((Face.mem_right_iff (ι := ι) c x.val).1 x.property k).symm

@[simp]
theorem fixRightEquiv_apply_inl (c : BoolWord κ) (x : BoolWord ι) (i : ι) :
    (fixRightEquiv c x).val (Sum.inl i) = x i :=
  rfl

@[simp]
theorem fixRightEquiv_apply_inr (c : BoolWord κ) (x : BoolWord ι) (k : κ) :
    (fixRightEquiv c x).val (Sum.inr k) = c k :=
  rfl

@[simp]
theorem fixRightEquiv_symm_apply (c : BoolWord κ)
    (x : (Face.right (ι := ι) c).Points) (i : ι) :
    (fixRightEquiv c).symm x i = x.val (Sum.inl i) :=
  rfl

/-- Extending by identity preserves every face that fixes only the new right coordinates. -/
theorem extendRight_stable (p : BoolPerm ι) (c : BoolWord κ) (x : BoolWord (ι ⊕ κ)) :
    BoolPerm.extendRight p κ x ∈ (Face.right (ι := ι) c).carrier ↔
      x ∈ (Face.right (ι := ι) c).carrier := by
  simp only [Face.mem_right_iff, BoolPerm.extendRight_apply_inr]

/-- The identity extension, restricted to a fixed right face. -/
def extendRightOnFace (p : BoolPerm ι) (c : BoolWord κ) :
    Equiv.Perm (Face.right (ι := ι) c).Points :=
  restrictFace (BoolPerm.extendRight p κ) (Face.right (ι := ι) c) (extendRight_stable p c)

/-- Inserting fixed coordinates conjugates `p` to its identity extension restricted to the face. -/
theorem permCongr_fixRightEquiv (p : BoolPerm ι) (c : BoolWord κ) :
    (fixRightEquiv (ι := ι) c).permCongr p = extendRightOnFace p c := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  funext i
  cases i with
  | inl i => rfl
  | inr k => exact ((Face.mem_right_iff (ι := ι) c x.val).1 x.property k).symm

/-- The retained left part of an output word. This is mere projection until accompanied by a
`RightDummy` certificate. -/
def keepLeft (f : α → BoolWord (ι ⊕ κ)) : α → BoolWord ι :=
  fun x i => f x (Sum.inl i)

/-- Assemble retained left outputs with fixed right outputs. -/
def assembleRight (f : α → BoolWord ι) (c : BoolWord κ) : α → BoolWord (ι ⊕ κ) :=
  fun x => BoolWord.sumEquiv.symm (f x, c)

/-- Evidence that the right output components of `f` are the fixed word `c`. -/
structure RightDummy (f : α → BoolWord (ι ⊕ κ)) (c : BoolWord κ) : Prop where
  eq_const : ∀ x k, f x (Sum.inr k) = c k

namespace RightDummy

variable {f : α → BoolWord (ι ⊕ κ)} {c : BoolWord κ}

/-- A certified dummy output lies in the corresponding fixed right face. -/
theorem mem_face (h : RightDummy f c) (x : α) : f x ∈ (Face.right c).carrier :=
  (Face.mem_right_iff (ι := ι) c (f x)).2 (h.eq_const x)

/-- A map with certified right dummy outputs is reconstructed from its retained outputs and the
fixed word. -/
theorem reconstruct (h : RightDummy f c) : assembleRight (keepLeft f) c = f := by
  funext x i
  cases i with
  | inl i => rfl
  | inr k => exact (h.eq_const x k).symm

/-- Delete certified right dummy outputs. The proof argument prevents an arbitrary projection from
being presented as dummy deletion. -/
def deleteRight (_h : RightDummy f c) : α → BoolWord ι :=
  keepLeft f

@[simp]
theorem deleteRight_apply (h : RightDummy f c) (x : α) (i : ι) :
    h.deleteRight x i = f x (Sum.inl i) :=
  rfl

end RightDummy

end Component

end Toffoli
