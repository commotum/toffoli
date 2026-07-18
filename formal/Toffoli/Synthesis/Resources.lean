import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Toffoli.Bool.Defs

/-!
# Auxiliary resources for three-bit Toffoli synthesis

The uniform positive-arity construction uses two persistent `true` enable coordinates and
`n - 3` persistent `false` work coordinates.  This module owns only the index type, constant word,
and arithmetic accounting; it imports no circuit, decomposition, parity, or smooth code.
-/

namespace Toffoli.Synthesis

/-- Shared auxiliary coordinates for an `n`-bit target: two enables and `n - 3` work bits. -/
abbrev UniversalAux (n : ℕ) := Fin 2 ⊕ Fin (n - 3)

/-- Data coordinates followed by the shared auxiliary bank. -/
abbrev UniversalIndex (n : ℕ) := Fin n ⊕ UniversalAux n

/-- Embed a data coordinate into the universal ambient index. -/
def dataIndex {n : ℕ} (i : Fin n) : UniversalIndex n :=
  Sum.inl i

/-- Embed one of the two persistent enable coordinates. -/
def enableIndex {n : ℕ} (i : Fin 2) : UniversalIndex n :=
  Sum.inr (Sum.inl i)

/-- Embed a clean work coordinate. -/
def workIndex {n : ℕ} (i : Fin (n - 3)) : UniversalIndex n :=
  Sum.inr (Sum.inr i)

/-- The clean auxiliary word: enable bits are `true` and work bits are `false`. -/
def universalConstants (n : ℕ) : BoolWord (UniversalAux n) :=
  Sum.elim (fun _ => true) (fun _ => false)

@[simp]
theorem universalConstants_enable (n : ℕ) (i : Fin 2) :
    universalConstants n (Sum.inl i) = true :=
  rfl

@[simp]
theorem universalConstants_work (n : ℕ) (i : Fin (n - 3)) :
    universalConstants n (Sum.inr i) = false :=
  rfl

/-- Number of auxiliary wires in the uniform positive-arity construction. -/
def auxCount (n : ℕ) : ℕ :=
  2 + (n - 3)

@[simp]
theorem card_universalAux (n : ℕ) : Fintype.card (UniversalAux n) = auxCount n := by
  simp [auxCount]

theorem auxCount_eq_two {n : ℕ} (h : n ≤ 3) : auxCount n = 2 := by
  simp [auxCount, Nat.sub_eq_zero_of_le h]

theorem auxCount_eq_sub_one {n : ℕ} (h : 3 ≤ n) : auxCount n = n - 1 := by
  unfold auxCount
  omega

/-- The verified resource profile implies the paper's stated bound in its valid range `n ≥ 3`. -/
theorem auxCount_le_two_mul_sub_three {n : ℕ} (h : 3 ≤ n) :
    auxCount n ≤ 2 * n - 3 := by
  unfold auxCount
  omega

end Toffoli.Synthesis
