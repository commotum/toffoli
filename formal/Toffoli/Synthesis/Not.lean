import Mathlib.Data.Finset.Basic
import Toffoli.Circuit.ThreeBit
import Toffoli.Cube.Basic
import Toffoli.Synthesis.FaceRealization
import Toffoli.Synthesis.Resources

/-!
# Clean masked NOT synthesis

Two persistent `true` enable coordinates turn the canonical three-bit Toffoli into a NOT on any
selected data coordinate.  A duplicate-free coordinate list therefore implements a componentwise
NOT mask while returning the entire auxiliary bank unchanged.
-/

namespace Toffoli

namespace Synthesis

/-- A three-bit Toffoli whose two controls are the persistent enable bits and whose target is one
data coordinate. -/
def notInstruction {n : ℕ} (target : Fin n) : ThreeBitInstruction (UniversalIndex n) :=
  ThreeBitInstruction.ofDistinct (enableIndex 0) (enableIndex 1) (dataIndex target)
    (by simp [enableIndex]) (by simp [enableIndex, dataIndex])
    (by simp [enableIndex, dataIndex])

@[simp]
theorem notInstruction_control₁ {n : ℕ} (target : Fin n) :
    (notInstruction target).control₁ = enableIndex 0 := by
  simp [notInstruction]

@[simp]
theorem notInstruction_control₂ {n : ℕ} (target : Fin n) :
    (notInstruction target).control₂ = enableIndex 1 := by
  simp [notInstruction]

@[simp]
theorem notInstruction_target {n : ℕ} (target : Fin n) :
    (notInstruction target).target = dataIndex target := by
  simp [notInstruction]

/-- One enabled instruction flips exactly its selected data coordinate and preserves the clean
auxiliary bank. -/
theorem notInstruction_apply {n : ℕ} (target : Fin n) (x : BoolVec n) :
    (notInstruction target).perm
        (BoolWord.sumEquiv.symm (x, universalConstants n)) =
      BoolWord.sumEquiv.symm (x.flipAt target, universalConstants n) := by
  funext i
  cases i with
  | inl j =>
      by_cases hj : j = target
      · subst j
        rw [show Sum.inl target = (notInstruction target).target by
          simp [dataIndex]]
        rw [(notInstruction target).perm_apply_target]
        simp [dataIndex, enableIndex]
      · rw [(notInstruction target).perm_apply_of_ne_target]
        · exact (BoolWord.flipAt_apply_of_ne x hj).symm
        · simpa [dataIndex] using hj
  | inr aux =>
      rw [(notInstruction target).perm_apply_of_ne_target]
      · rfl
      · simp [dataIndex]

/-- A word of enabled NOT instructions, in list order. -/
def notList {n : ℕ} (targets : List (Fin n)) : List (ThreeBitInstruction (UniversalIndex n)) :=
  targets.map notInstruction

/-- Semantic data update performed by a list of NOT targets. -/
def flipList {n : ℕ} (targets : List (Fin n)) (x : BoolVec n) : BoolVec n :=
  targets.foldl BoolWord.flipAt x

/-- A word of enabled NOTs preserves clean auxiliaries and performs `flipList` on the data. -/
theorem eval_notList_apply {n : ℕ} (targets : List (Fin n)) (x : BoolVec n) :
    ThreeBitCircuit.eval (notList targets)
        (BoolWord.sumEquiv.symm (x, universalConstants n)) =
      BoolWord.sumEquiv.symm (flipList targets x, universalConstants n) := by
  induction targets generalizing x with
  | nil => rfl
  | cons target targets ih =>
      simp only [notList, List.map_cons, ThreeBitCircuit.eval_cons_apply]
      rw [notInstruction_apply]
      simpa [notList, flipList] using ih (x.flipAt target)

/-- Flipping a duplicate-free list changes a component exactly when that component occurs in the
list. -/
theorem flipList_apply_of_nodup {n : ℕ} {targets : List (Fin n)} (h : targets.Nodup)
    (x : BoolVec n) (i : Fin n) :
    flipList targets x i = if i ∈ targets then !(x i) else x i := by
  induction targets generalizing x with
  | nil => simp [flipList]
  | cons target targets ih =>
      have htail := h.tail
      have htarget := h.notMem
      rw [flipList, List.foldl_cons, ← flipList, ih htail]
      by_cases hi : i ∈ targets
      · have hit : i ≠ target := by
          intro hit
          subst i
          exact htarget hi
        simp [hi, hit, BoolWord.flipAt_apply_of_ne]
      · by_cases hit : i = target
        · subst i
          simp [hi]
        · simp [hi, hit, BoolWord.flipAt_apply_of_ne]

/-- Coordinates selected by a Boolean mask, in the finite index order chosen by `Finset.toList`. -/
noncomputable def maskTargets {n : ℕ} (mask : BoolVec n) : List (Fin n) :=
  (Finset.univ.filter fun i => mask i = true).toList

@[simp]
theorem mem_maskTargets {n : ℕ} (mask : BoolVec n) (i : Fin n) :
    i ∈ maskTargets mask ↔ mask i = true := by
  simp [maskTargets]

theorem maskTargets_nodup {n : ℕ} (mask : BoolVec n) : (maskTargets mask).Nodup :=
  Finset.nodup_toList _

/-- The enabled-NOT word selected by a Boolean mask. -/
noncomputable def notMaskWord {n : ℕ}
    (mask : BoolVec n) : List (ThreeBitInstruction (UniversalIndex n)) :=
  notList (maskTargets mask)

/-- The coordinate-list semantics agrees with the reusable finite `flipMask` equivalence. -/
theorem flipList_maskTargets {n : ℕ} (mask x : BoolVec n) :
    flipList (maskTargets mask) x = BoolWord.flipMask mask x := by
  funext i
  rw [flipList_apply_of_nodup (maskTargets_nodup mask)]
  cases hmask : mask i <;> simp [hmask]

/-- A masked-NOT word cleanly realizes the corresponding componentwise Boolean permutation. -/
theorem notMaskWord_cleanRealizes {n : ℕ} (mask : BoolVec n) :
    CleanRealizes (ThreeBitCircuit.eval (notMaskWord mask)) (universalConstants n)
      (BoolWord.flipMaskEquiv mask) := by
  intro x
  rw [notMaskWord, eval_notList_apply, flipList_maskTargets]
  rfl

end Synthesis

end Toffoli
