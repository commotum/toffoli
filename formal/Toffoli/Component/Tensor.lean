import Mathlib.Logic.Equiv.Prod
import Toffoli.Bool.Defs

/-!
# Disjoint component products

Parallel composition acts on disjoint coordinate summands. It is the semantic operation behind
no-fan-out tensoring and identity extension.
-/

namespace Toffoli

universe u v

namespace BoolWord

variable {ι : Type u} {κ : Type v}

/-- Split a word on a disjoint sum of coordinates into its two component words. -/
def sumEquiv : BoolWord (ι ⊕ κ) ≃ BoolWord ι × BoolWord κ where
  toFun x := (fun i => x (Sum.inl i), fun k => x (Sum.inr k))
  invFun x := Sum.elim x.1 x.2
  left_inv x := by
    funext i
    cases i <;> rfl
  right_inv x := rfl

@[simp]
theorem sumEquiv_apply_fst (x : BoolWord (ι ⊕ κ)) : (sumEquiv x).1 = fun i => x (Sum.inl i) :=
  rfl

@[simp]
theorem sumEquiv_apply_snd (x : BoolWord (ι ⊕ κ)) : (sumEquiv x).2 = fun k => x (Sum.inr k) :=
  rfl

@[simp]
theorem sumEquiv_symm_apply_inl (x : BoolWord ι × BoolWord κ) (i : ι) :
    sumEquiv.symm x (Sum.inl i) = x.1 i :=
  rfl

@[simp]
theorem sumEquiv_symm_apply_inr (x : BoolWord ι × BoolWord κ) (k : κ) :
    sumEquiv.symm x (Sum.inr k) = x.2 k :=
  rfl

end BoolWord

namespace BoolPerm

variable {ι : Type u} {κ : Type v}

/-- Run two Boolean permutations in parallel on disjoint coordinate summands. -/
def tensor (p : BoolPerm ι) (q : BoolPerm κ) : BoolPerm (ι ⊕ κ) :=
  BoolWord.sumEquiv.symm.permCongr (Equiv.prodCongr p q)

@[simp]
theorem tensor_apply_inl (p : BoolPerm ι) (q : BoolPerm κ) (x : BoolWord (ι ⊕ κ)) (i : ι) :
    tensor p q x (Sum.inl i) = p (fun j => x (Sum.inl j)) i := by
  rfl

@[simp]
theorem tensor_apply_inr (p : BoolPerm ι) (q : BoolPerm κ) (x : BoolWord (ι ⊕ κ)) (k : κ) :
    tensor p q x (Sum.inr k) = q (fun l => x (Sum.inr l)) k := by
  rfl

@[simp]
theorem tensor_refl :
    tensor (Equiv.refl (BoolWord ι)) (Equiv.refl (BoolWord κ)) =
      Equiv.refl (BoolWord (ι ⊕ κ)) := by
  apply Equiv.ext
  intro x
  funext i
  cases i <;> rfl

theorem tensor_serial (p p' : BoolPerm ι) (q q' : BoolPerm κ) :
    tensor (p.trans p') (q.trans q') = (tensor p q).trans (tensor p' q') := by
  apply Equiv.ext
  intro x
  funext i
  cases i <;> rfl

/-- Extend a Boolean permutation by identity on a disjoint right coordinate summand. -/
def extendRight (p : BoolPerm ι) (κ : Type v) : BoolPerm (ι ⊕ κ) :=
  tensor p (Equiv.refl (BoolWord κ))

@[simp]
theorem extendRight_apply_inl (p : BoolPerm ι) (x : BoolWord (ι ⊕ κ)) (i : ι) :
    extendRight p κ x (Sum.inl i) = p (fun j => x (Sum.inl j)) i :=
  rfl

@[simp]
theorem extendRight_apply_inr (p : BoolPerm ι) (x : BoolWord (ι ⊕ κ)) (k : κ) :
    extendRight p κ x (Sum.inr k) = x (Sum.inr k) :=
  rfl

end BoolPerm

end Toffoli
