import Mathlib.Data.Fintype.BigOperators
import Toffoli.Bool.Defs

/-!
# Finite facts about Boolean words

Cardinality and empty-arity facts live outside `Toffoli.Bool.Defs` so consumers of the basic
types do not inherit finite big-operator imports.
-/

namespace Toffoli

universe u

variable {ι : Type u}

/-- Boolean words on a finite index type have `2 ^ card ι` elements. -/
theorem card_boolWord [Fintype ι] [DecidableEq ι] :
    Fintype.card (BoolWord ι) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun, Fintype.card_bool]

/-- There is exactly one empty Boolean word. -/
@[simp]
theorem card_boolVec_zero : Fintype.card (BoolVec 0) = 1 := by
  rw [card_boolWord]
  simp

/-- Any two empty Boolean words coincide. -/
theorem boolVec_zero_unique (x y : BoolVec 0) : x = y := by
  funext i
  exact Fin.elim0 i

/-- The empty Boolean cube has only the identity permutation. -/
theorem boolPermN_zero_eq_refl (p : BoolPermN 0) : p = Equiv.refl (BoolVec 0) := by
  apply Equiv.ext
  intro x
  exact boolVec_zero_unique _ _

end Toffoli
