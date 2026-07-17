import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Toffoli.Gate.Atomic

/-!
# Boolean-cube paths

The finite difference set measures Hamming distance without importing the heavier information-
theory API. Flipping a differing coordinate erases exactly that coordinate from the difference
set. Strong induction therefore gives a precise Gray-path connectivity theorem, including equal
and empty-index boundary cases.
-/

namespace Toffoli

universe u

namespace BoolWord

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Coordinates on which two Boolean words differ. -/
def diff (x y : BoolWord ι) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ y i

@[simp]
theorem mem_diff (x y : BoolWord ι) (i : ι) : i ∈ x.diff y ↔ x i ≠ y i := by
  simp [diff]

@[simp]
theorem diff_self (x : BoolWord ι) : x.diff x = ∅ := by
  ext i
  simp

theorem diff_comm (x y : BoolWord ι) : x.diff y = y.diff x := by
  ext i
  simp [ne_comm]

@[simp]
theorem diff_eq_empty_iff (x y : BoolWord ι) : x.diff y = ∅ ↔ x = y := by
  constructor
  · intro h
    funext i
    by_contra hi
    have : i ∈ x.diff y := (mem_diff x y i).2 hi
    simpa [h] using this
  · rintro rfl
    exact diff_self x

theorem diff_flipAt_eq_erase (x y : BoolWord ι) {target : ι} (h : target ∈ x.diff y) :
    (x.flipAt target).diff y = (x.diff y).erase target := by
  have hne : x target ≠ y target := (mem_diff x y target).1 h
  have htarget : (!(x target)) = y target := by
    cases hx : x target <;> cases hy : y target <;> simp_all
  ext i
  by_cases hi : i = target
  · subst i
    simp [htarget]
  · simp [mem_diff, BoolWord.flipAt_apply_of_ne _ hi, hi]

theorem card_diff_flipAt_lt (x y : BoolWord ι) {target : ι} (h : target ∈ x.diff y) :
    ((x.flipAt target).diff y).card < (x.diff y).card := by
  rw [diff_flipAt_eq_erase x y h]
  exact Finset.card_erase_lt_of_mem h

end BoolWord

/-- Reachability by a finite sequence of Boolean-cube edge steps. -/
abbrev GrayReachable {ι : Type u} [DecidableEq ι] :=
  Relation.ReflTransGen (@CubeAdjacent ι _)

namespace GrayReachable

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Every two vertices of a finite Boolean cube are connected by a Gray path. -/
theorem all (x y : BoolWord ι) : GrayReachable x y := by
  classical
  induction hcard : (x.diff y).card using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hxy : x = y
      · subst x
        exact Relation.ReflTransGen.refl
      · have hnonempty : (x.diff y).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          exact fun hempty => hxy ((BoolWord.diff_eq_empty_iff x y).1 hempty)
        obtain ⟨target, htarget⟩ := hnonempty
        apply Relation.ReflTransGen.head (CubeAdjacent.flipAt x target)
        apply ih ((x.flipAt target).diff y).card
        · simpa [hcard] using BoolWord.card_diff_flipAt_lt x y htarget
        · rfl

end GrayReachable

end Toffoli
