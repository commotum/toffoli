import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Basic
import Toffoli.Gate.Toffoli

/-!
# The paper's AND/NAND family

`andNandSpec target` controls every coordinate other than `target`. `thetaSucc n` is the paper's
order-`n + 1` gate, with the last coordinate as target. Thus `thetaSucc 0` is NOT,
`thetaSucc 1` is CNOT, and `thetaSucc 2` is the usual three-bit Toffoli gate. There is no
order-zero member because a gate must have a target.
-/

namespace Toffoli

universe u

namespace ToffoliGate

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The AND/NAND specification with every coordinate except `target` as a positive control. -/
def andNandSpec (target : ι) : ToffoliGate ι where
  controls := Finset.univ.erase target
  target := target
  target_not_mem := Finset.notMem_erase target Finset.univ

@[simp]
theorem andNandSpec_active_iff (target : ι) (x : BoolWord ι) :
    (andNandSpec target).Active x ↔ ∀ i, i ≠ target → x i = true := by
  simp [Active, andNandSpec]

/-- The AND/NAND permutation with the specified target. -/
def andNand (target : ι) : BoolPerm ι :=
  (andNandSpec target).perm

@[simp]
theorem andNand_apply_target (target : ι) (x : BoolWord ι) :
    andNand target x target =
      if (∀ i, i ≠ target → x i = true) then !(x target) else x target := by
  rw [andNand, perm_apply]
  change
    (andNandSpec target).run x (andNandSpec target).target =
      if (∀ i, i ≠ target → x i = true) then !(x target) else x target
  rw [run_target]
  apply if_congr
  · exact andNandSpec_active_iff target x
  · rfl
  · rfl

theorem andNand_apply_of_ne (target : ι) (x : BoolWord ι) {i : ι} (hi : i ≠ target) :
    andNand target x i = x i :=
  (andNandSpec target).run_of_ne_target x hi

end ToffoliGate

namespace AndNand

/-- The specification of the paper's order-`n + 1` AND/NAND gate. The parameter counts controls. -/
def thetaSuccSpec (n : ℕ) : ToffoliGate (Fin (n + 1)) :=
  ToffoliGate.andNandSpec (Fin.last n)

/-- The paper's order-`n + 1` AND/NAND permutation. The parameter counts controls. -/
def thetaSucc (n : ℕ) : BoolPermN (n + 1) :=
  (thetaSuccSpec n).perm

@[simp]
theorem thetaSucc_active_iff (n : ℕ) (x : BoolVec (n + 1)) :
    (thetaSuccSpec n).Active x ↔ ∀ i : Fin n, x i.castSucc = true := by
  change
    (ToffoliGate.andNandSpec (Fin.last n)).Active x ↔ ∀ i : Fin n, x i.castSucc = true
  rw [ToffoliGate.andNandSpec_active_iff]
  constructor
  · intro h i
    exact h i.castSucc (Fin.castSucc_ne_last i)
  · intro h i hi
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    exact h j

@[simp]
theorem thetaSucc_apply_control (n : ℕ) (x : BoolVec (n + 1)) (i : Fin n) :
    thetaSucc n x i.castSucc = x i.castSucc :=
  (thetaSuccSpec n).run_of_ne_target x (Fin.castSucc_ne_last i)

@[simp]
theorem thetaSucc_apply_target (n : ℕ) (x : BoolVec (n + 1)) :
    thetaSucc n x (Fin.last n) =
      if (∀ i : Fin n, x i.castSucc = true) then !(x (Fin.last n)) else x (Fin.last n) := by
  rw [thetaSucc, ToffoliGate.perm_apply]
  change
    (thetaSuccSpec n).run x (thetaSuccSpec n).target =
      if (∀ i : Fin n, x i.castSucc = true) then !(x (Fin.last n)) else x (Fin.last n)
  rw [ToffoliGate.run_target]
  apply if_congr
  · exact thetaSucc_active_iff n x
  · rfl
  · rfl

@[simp]
theorem thetaSucc_zero_apply (x : BoolVec 1) : thetaSucc 0 x 0 = !(x 0) := by
  simpa using thetaSucc_apply_target 0 x

@[simp]
theorem thetaSucc_one_active (x : BoolVec 2) :
    (thetaSuccSpec 1).Active x ↔ x 0 = true := by
  rw [thetaSucc_active_iff]
  simp [Fin.forall_fin_one]

@[simp]
theorem thetaSucc_two_active (x : BoolVec 3) :
    (thetaSuccSpec 2).Active x ↔ x 0 = true ∧ x 1 = true := by
  rw [thetaSucc_active_iff]
  simp [Fin.forall_fin_two]

end AndNand

end Toffoli
