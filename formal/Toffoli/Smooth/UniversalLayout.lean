import Toffoli.Bool.Reindex
import Toffoli.Synthesis.Resources

/-!
# Flattening the universal synthesis layout

The discrete three-bit synthesis uses the nested index type

`Fin n ⊕ (Fin 2 ⊕ Fin (n - 3))`.

This file identifies it with a single initial segment of natural numbers, with data coordinates
first, followed by the two enable coordinates and then the work coordinates.  The construction is
purely finite: it imports no circuit, permutation-decomposition, or manifold modules.
-/

namespace Toffoli
namespace Synthesis

/-- Flatten the nested universal index into consecutive coordinates: data, enables, then work. -/
def universalIndexFinEquiv (n : ℕ) : UniversalIndex n ≃ Fin (n + auxCount n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n))
      (finSumFinEquiv : Fin 2 ⊕ Fin (n - 3) ≃ Fin (2 + (n - 3)))).trans
    (finSumFinEquiv : Fin n ⊕ Fin (auxCount n) ≃ Fin (n + auxCount n))

/-- Flattened location of a data coordinate. -/
def flatDataIndex {n : ℕ} (i : Fin n) : Fin (n + auxCount n) :=
  Fin.castAdd (auxCount n) i

/-- Flattened location of an enable coordinate. -/
def flatEnableIndex {n : ℕ} (i : Fin 2) : Fin (n + auxCount n) :=
  Fin.natAdd n (Fin.castAdd (n - 3) i)

/-- Flattened location of a work coordinate. -/
def flatWorkIndex {n : ℕ} (i : Fin (n - 3)) : Fin (n + auxCount n) :=
  Fin.natAdd n (Fin.natAdd 2 i)

@[simp]
theorem universalIndexFinEquiv_data {n : ℕ} (i : Fin n) :
    universalIndexFinEquiv n (dataIndex i) = flatDataIndex i := by
  rfl

@[simp]
theorem universalIndexFinEquiv_enable {n : ℕ} (i : Fin 2) :
    universalIndexFinEquiv n (enableIndex i) = flatEnableIndex i := by
  rfl

@[simp]
theorem universalIndexFinEquiv_work {n : ℕ} (i : Fin (n - 3)) :
    universalIndexFinEquiv n (workIndex i) = flatWorkIndex i := by
  rfl

@[simp]
theorem universalIndexFinEquiv_symm_data {n : ℕ} (i : Fin n) :
    (universalIndexFinEquiv n).symm (flatDataIndex i) = dataIndex i := by
  rw [← universalIndexFinEquiv_data]
  exact (universalIndexFinEquiv n).symm_apply_apply (dataIndex i)

@[simp]
theorem universalIndexFinEquiv_symm_enable {n : ℕ} (i : Fin 2) :
    (universalIndexFinEquiv n).symm (flatEnableIndex i) = enableIndex i := by
  rw [← universalIndexFinEquiv_enable]
  exact (universalIndexFinEquiv n).symm_apply_apply (enableIndex i)

@[simp]
theorem universalIndexFinEquiv_symm_work {n : ℕ} (i : Fin (n - 3)) :
    (universalIndexFinEquiv n).symm (flatWorkIndex i) = workIndex i := by
  rw [← universalIndexFinEquiv_work]
  exact (universalIndexFinEquiv n).symm_apply_apply (workIndex i)

@[simp]
theorem flatDataIndex_val {n : ℕ} (i : Fin n) : (flatDataIndex i : ℕ) = i :=
  rfl

@[simp]
theorem flatEnableIndex_val {n : ℕ} (i : Fin 2) :
    (flatEnableIndex (n := n) i : ℕ) = n + i :=
  rfl

@[simp]
theorem flatWorkIndex_val {n : ℕ} (i : Fin (n - 3)) :
    (flatWorkIndex i : ℕ) = n + 2 + i := by
  simp [flatWorkIndex, Nat.add_assoc]

/-- The flattened ambient size, written without the `auxCount` abbreviation. -/
theorem totalCount_eq (n : ℕ) : n + auxCount n = n + 2 + (n - 3) := by
  simp [auxCount, Nat.add_assoc]

@[simp]
theorem card_universalIndex (n : ℕ) :
    Fintype.card (UniversalIndex n) = n + auxCount n := by
  simpa using Fintype.card_congr (universalIndexFinEquiv n)

/-- Insert a data word and the shared clean constants into the nested universal index. -/
def universalInput {n : ℕ} (x : BoolVec n) : BoolWord (UniversalIndex n) :=
  Sum.elim x (universalConstants n)

@[simp]
theorem universalInput_data {n : ℕ} (x : BoolVec n) (i : Fin n) :
    universalInput x (dataIndex i) = x i :=
  rfl

@[simp]
theorem universalInput_enable {n : ℕ} (x : BoolVec n) (i : Fin 2) :
    universalInput x (enableIndex i) = true :=
  rfl

@[simp]
theorem universalInput_work {n : ℕ} (x : BoolVec n) (i : Fin (n - 3)) :
    universalInput x (workIndex i) = false :=
  rfl

/-- The same data-and-constant word in the flattened coordinate layout. -/
def flatUniversalInput {n : ℕ} (x : BoolVec n) : BoolVec (n + auxCount n) :=
  BoolWord.reindex (universalIndexFinEquiv n) (universalInput x)

@[simp]
theorem flatUniversalInput_layout {n : ℕ} (x : BoolVec n) (i : UniversalIndex n) :
    flatUniversalInput x (universalIndexFinEquiv n i) = universalInput x i := by
  simp [flatUniversalInput]

@[simp]
theorem universalInput_layout_symm {n : ℕ} (x : BoolVec n)
    (i : Fin (n + auxCount n)) :
    universalInput x ((universalIndexFinEquiv n).symm i) = flatUniversalInput x i := by
  simp [flatUniversalInput]

@[simp]
theorem flatUniversalInput_data {n : ℕ} (x : BoolVec n) (i : Fin n) :
    flatUniversalInput x (flatDataIndex i) = x i := by
  simp [flatUniversalInput]

@[simp]
theorem flatUniversalInput_enable {n : ℕ} (x : BoolVec n) (i : Fin 2) :
    flatUniversalInput x (flatEnableIndex i) = true := by
  simp [flatUniversalInput]

@[simp]
theorem flatUniversalInput_work {n : ℕ} (x : BoolVec n) (i : Fin (n - 3)) :
    flatUniversalInput x (flatWorkIndex i) = false := by
  simp [flatUniversalInput]

end Synthesis
end Toffoli
