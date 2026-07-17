import Mathlib.Logic.Equiv.Basic

/-!
# Finite Boolean words and permutations

This file contains only the low-dependency types used throughout the discrete formalization.
The index type is generic; `BoolVec` and `BoolPermN` specialize it to the paper's natural-number
arities.
-/

namespace Toffoli

universe u

/-- A Boolean word with one component for every index in `ι`. -/
abbrev BoolWord (ι : Type u) := ι → Bool

/-- An `n`-component Boolean word. This includes the empty word at `n = 0`. -/
abbrev BoolVec (n : ℕ) := BoolWord (Fin n)

/-- An invertible Boolean function on words indexed by `ι`. -/
abbrev BoolPerm (ι : Type u) := Equiv.Perm (BoolWord ι)

/-- An invertible Boolean function of arity `n`. -/
abbrev BoolPermN (n : ℕ) := BoolPerm (Fin n)

end Toffoli
