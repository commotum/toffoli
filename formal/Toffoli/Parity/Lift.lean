import Mathlib.GroupTheory.Perm.Sign
import Toffoli.Bool.Finite
import Toffoli.Bool.Reindex
import Toffoli.Component.Tensor

/-!
# Sign of Boolean identity extensions

This proof-side leaf contains the exact repetition formula behind the paper's parity argument.
It is intentionally generic in the local permutation: AND/NAND enters only in the obstruction
leaf.
-/

namespace Toffoli

universe u v

namespace BoolPerm

variable {ι : Type u} {κ : Type v}

@[simp]
theorem sign_reindex [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (p : BoolPerm ι) :
    Equiv.Perm.sign (reindex e p) = Equiv.Perm.sign p := by
  classical
  exact Equiv.Perm.sign_permCongr (BoolWord.reindex e) p

/-- Extending by unused Boolean coordinates repeats the local permutation once for each word on
the unused factor. -/
theorem sign_extendRight [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : BoolPerm ι) :
    Equiv.Perm.sign (extendRight p κ) =
      Equiv.Perm.sign p ^ Fintype.card (BoolWord κ) := by
  classical
  rw [extendRight, tensor, Equiv.Perm.sign_permCongr, Equiv.prodCongr_refl_right,
    Equiv.Perm.sign_prodCongrLeft]
  simp

/-- The same formula expressed in terms of the number of unused coordinates. -/
theorem sign_extendRight_eq_pow_two [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (p : BoolPerm ι) :
    Equiv.Perm.sign (extendRight p κ) =
      Equiv.Perm.sign p ^ (2 ^ Fintype.card κ) := by
  rw [sign_extendRight, card_boolWord]

/-- A permutation extended across at least one unused Boolean coordinate is even. -/
theorem sign_extendRight_of_nonempty [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (p : BoolPerm ι) :
    Equiv.Perm.sign (extendRight p κ) = 1 := by
  rw [sign_extendRight_eq_pow_two, Int.units_pow_eq_pow_mod_two]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := κ))
  simp [hm, pow_succ]

end BoolPerm

end Toffoli
