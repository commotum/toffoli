import Toffoli.Bool.Defs

/-!
# Reindexing Boolean components

A coordinate equivalence induces an equivalence of Boolean word spaces. Reindexing a Boolean
permutation is conjugation by that word equivalence.
-/

namespace Toffoli

universe u v w

namespace BoolWord

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- Reindex a Boolean word along an equivalence of coordinate types. -/
def reindex (e : ι ≃ κ) : BoolWord ι ≃ BoolWord κ where
  toFun x k := x (e.symm k)
  invFun y i := y (e i)
  left_inv x := by
    funext i
    simp
  right_inv y := by
    funext k
    simp

@[simp]
theorem reindex_apply (e : ι ≃ κ) (x : BoolWord ι) (k : κ) : reindex e x k = x (e.symm k) :=
  by simp [reindex]

@[simp]
theorem reindex_symm_apply (e : ι ≃ κ) (x : BoolWord κ) (i : ι) :
    (reindex e).symm x i = x (e i) :=
  by simp [reindex]

@[simp]
theorem reindex_refl : reindex (Equiv.refl ι) = Equiv.refl (BoolWord ι) := by
  apply Equiv.ext
  intro x
  rfl

theorem reindex_trans (e : ι ≃ κ) (f : κ ≃ μ) :
    reindex (e.trans f) = (reindex e).trans (reindex f) := by
  apply Equiv.ext
  intro x
  rfl

end BoolWord

namespace BoolPerm

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- Conjugate a Boolean permutation by a coordinate reindexing. -/
def reindex (e : ι ≃ κ) : BoolPerm ι ≃ BoolPerm κ :=
  (BoolWord.reindex e).permCongr

@[simp]
theorem reindex_apply (e : ι ≃ κ) (p : BoolPerm ι) (x : BoolWord κ) (k : κ) :
    reindex e p x k = p (fun i => x (e i)) (e.symm k) :=
  by simp [reindex, BoolWord.reindex]

@[simp]
theorem reindex_refl (p : BoolPerm ι) : reindex (Equiv.refl ι) p = p := by
  apply Equiv.ext
  intro x
  rfl

theorem reindex_trans (e : ι ≃ κ) (f : κ ≃ μ) (p : BoolPerm ι) :
    reindex (e.trans f) p = reindex f (reindex e p) := by
  apply Equiv.ext
  intro x
  rfl

theorem reindex_serial (e : ι ≃ κ) (p q : BoolPerm ι) :
    reindex e (p.trans q) = (reindex e p).trans (reindex e q) := by
  exact (Equiv.permCongr_trans (BoolWord.reindex e) p q).symm

/-- A bare coordinate permutation, viewed as a permutation of Boolean words. This is wiring, not
conjugation of another gate. -/
def coordinatePerm (e : Equiv.Perm ι) : BoolPerm ι :=
  BoolWord.reindex e

@[simp]
theorem coordinatePerm_apply (e : Equiv.Perm ι) (x : BoolWord ι) (i : ι) :
    coordinatePerm e x i = x (e.symm i) :=
  rfl

end BoolPerm

end Toffoli
