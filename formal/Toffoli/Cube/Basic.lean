import Mathlib.Data.Bool.Basic
import Toffoli.Bool.Defs

/-!
# Boolean-cube edges

This module contains only the cheap combinatorial primitives shared by Gray paths and atomic
gates.  In particular, it does not import the generalized Toffoli family.
-/

namespace Toffoli

universe u

namespace BoolWord

variable {ι : Type u} [DecidableEq ι]

/-- Complement one selected component of a Boolean word. -/
def flipAt (x : BoolWord ι) (target : ι) : BoolWord ι :=
  Function.update x target (!(x target))

@[simp]
theorem flipAt_apply_self (x : BoolWord ι) (target : ι) :
    x.flipAt target target = !(x target) := by
  simp [flipAt]

theorem flipAt_apply_of_ne (x : BoolWord ι) {target i : ι} (hi : i ≠ target) :
    x.flipAt target i = x i := by
  simp [flipAt, hi]

@[simp]
theorem flipAt_involutive (x : BoolWord ι) (target : ι) :
    (x.flipAt target).flipAt target = x := by
  funext i
  by_cases hi : i = target
  · subst i
    simp
  · rw [flipAt_apply_of_ne _ hi, flipAt_apply_of_ne _ hi]

theorem flipAt_ne (x : BoolWord ι) (target : ι) : x.flipAt target ≠ x := by
  intro h
  have htarget := congrFun h target
  rw [flipAt_apply_self] at htarget
  exact Bool.not_ne_self _ htarget

end BoolWord

namespace BoolWord

variable {ι : Type u}

/-- Complement exactly the components selected by a Boolean mask. -/
def flipMask (mask x : BoolWord ι) : BoolWord ι :=
  fun i => if mask i then !(x i) else x i

@[simp]
theorem flipMask_apply (mask x : BoolWord ι) (i : ι) :
    flipMask mask x i = if mask i then !(x i) else x i :=
  rfl

@[simp]
theorem flipMask_involutive (mask : BoolWord ι) : Function.Involutive (flipMask mask) := by
  intro x
  funext i
  cases hmask : mask i <;> simp [flipMask, hmask]

/-- Componentwise masked NOT, as a self-inverse permutation of Boolean words. -/
def flipMaskEquiv (mask : BoolWord ι) : BoolWord ι ≃ BoolWord ι where
  toFun := flipMask mask
  invFun := flipMask mask
  left_inv := flipMask_involutive mask
  right_inv := flipMask_involutive mask

@[simp]
theorem flipMaskEquiv_apply (mask x : BoolWord ι) :
    flipMaskEquiv mask x = flipMask mask x :=
  rfl

@[simp]
theorem flipMaskEquiv_symm (mask : BoolWord ι) : (flipMaskEquiv mask).symm = flipMaskEquiv mask :=
  rfl

/-- A componentwise NOT mask sending `base` to the all-`true` word. -/
def edgeNormalizer (base : BoolWord ι) : BoolWord ι ≃ BoolWord ι :=
  flipMaskEquiv fun i => !(base i)

@[simp]
theorem edgeNormalizer_symm (base : BoolWord ι) :
    (edgeNormalizer base).symm = edgeNormalizer base :=
  rfl

@[simp]
theorem edgeNormalizer_apply_base (base : BoolWord ι) :
    edgeNormalizer base base = (fun _ => true) := by
  funext i
  cases hi : base i <;> simp [edgeNormalizer, flipMaskEquiv, flipMask, hi]

@[simp]
theorem edgeNormalizer_apply_allTrue (base : BoolWord ι) :
    edgeNormalizer base (fun _ => true) = base := by
  simpa using (edgeNormalizer base).symm_apply_apply base

@[simp]
theorem edgeNormalizer_apply_flipAt [DecidableEq ι] (base : BoolWord ι) (target : ι) :
    edgeNormalizer base (base.flipAt target) =
      BoolWord.flipAt (fun _ : ι => true) target := by
  funext i
  by_cases hi : i = target
  · subst i
    cases hbase : base target <;>
      simp [edgeNormalizer, flipMaskEquiv, flipMask, flipAt, hbase]
  · cases hbase : base i <;>
      simp [edgeNormalizer, flipMaskEquiv, flipMask, flipAt, hi, hbase]

@[simp]
theorem edgeNormalizer_apply_allTrue_flipAt [DecidableEq ι]
    (base : BoolWord ι) (target : ι) :
    edgeNormalizer base (BoolWord.flipAt (fun _ : ι => true) target) =
      base.flipAt target := by
  simpa using (edgeNormalizer base).symm_apply_apply (base.flipAt target)

end BoolWord

/-- Two Boolean words are cube-adjacent when one is obtained from the other by flipping one
component. -/
def CubeAdjacent {ι : Type u} [DecidableEq ι] (x y : BoolWord ι) : Prop :=
  ∃ target, y = x.flipAt target

namespace CubeAdjacent

variable {ι : Type u} [DecidableEq ι] {x y : BoolWord ι}

theorem flipAt (x : BoolWord ι) (target : ι) : CubeAdjacent x (x.flipAt target) :=
  ⟨target, rfl⟩

theorem symm (h : CubeAdjacent x y) : CubeAdjacent y x := by
  obtain ⟨target, rfl⟩ := h
  exact ⟨target, (BoolWord.flipAt_involutive x target).symm⟩

theorem ne (h : CubeAdjacent x y) : x ≠ y := by
  obtain ⟨target, rfl⟩ := h
  exact (BoolWord.flipAt_ne x target).symm

end CubeAdjacent

end Toffoli
