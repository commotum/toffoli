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
