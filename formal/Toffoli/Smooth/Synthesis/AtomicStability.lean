import Toffoli.Smooth.Synthesis.FlatCircuit
import Toffoli.Smooth.ThreeBitStability
import Toffoli.Smooth.UniversalFace
import Toffoli.Synthesis.Atomic

/-!
# Global auxiliary stability of the discrete three-bit synthesis words

This file proves that the smooth interpretations of the explicit discrete synthesis words return
the universal auxiliary bank for every circle-valued input, not merely on the embedded Boolean
cube.  The higher-arity proof uses the literal compute/target/uncompute word and structural
replacement lemmas; it does not appeal to Boolean clean realization.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension
namespace AtomicStability

open Synthesis

private theorem evalFlattenSingleton_changesOnlyAt {n : ℕ}
    (instruction : ThreeBitInstruction (UniversalIndex n)) (q : Fin (n + auxCount n))
    (htarget :
      (ThreeBitInstruction.reindex (universalIndexFinEquiv n) instruction).target = q) :
    ChangesOnlyAt (FlatCircuit.evalFlattenWord n [instruction]) q := by
  rw [FlatCircuit.evalFlattenWord_eq]
  apply evalThreeBitWord_changesOnlyAt
  intro next hnext
  simp only [FlatCircuit.flattenWord_cons, FlatCircuit.flattenWord_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hnext
  subst next
  exact htarget

private theorem flattenComputeWord_avoids_final (k : ℕ) :
    ThreeBitWordAvoids (FlatCircuit.flattenWord (k + 4) (MultiControl.computeWord k))
      (flatDataIndex (Fin.last (k + 3))) := by
  intro instruction hinstruction
  rw [FlatCircuit.flattenWord, ThreeBitCircuit.reindex] at hinstruction
  simp only [List.mem_map] at hinstruction
  obtain ⟨original, horiginal, rfl⟩ := hinstruction
  have h := MultiControl.computeWord_avoids_final k original horiginal
  constructor
  · intro heq
    exact h.1 ((universalIndexFinEquiv (k + 4)).injective (by
      simpa using heq))
  constructor
  · intro heq
    exact h.2.1 ((universalIndexFinEquiv (k + 4)).injective (by
      simpa using heq))
  · intro heq
    exact h.2.2 ((universalIndexFinEquiv (k + 4)).injective (by
      simpa using heq))

/-- The flattened all-positive multi-control word changes at most its final data coordinate.
This covers NOT, CNOT, the three-bit gate, and every compute/target/uncompute ladder uniformly by
an explicit low-arity split. -/
theorem multiControlWord_changesOnlyAt (m : ℕ) :
    ChangesOnlyAt
      (FlatCircuit.evalFlattenWord (m + 1) (MultiControl.word (m + 1)))
      (flatDataIndex (Fin.last m)) := by
  cases m with
  | zero =>
      apply evalFlattenSingleton_changesOnlyAt
      simp [MultiControl.notInstruction]
  | succ m =>
      cases m with
      | zero =>
          apply evalFlattenSingleton_changesOnlyAt
          simp [MultiControl.cnotInstruction]
      | succ m =>
          cases m with
          | zero =>
              apply evalFlattenSingleton_changesOnlyAt
              simp [MultiControl.threeInstruction]
          | succ k =>
              rw [FlatCircuit.evalFlattenWord_eq]
              change
                ChangesOnlyAt
                  (evalThreeBitWord
                    (FlatCircuit.flattenWord (k + 4)
                      (MultiControl.computeWord k ++
                        MultiControl.targetInstruction k ::
                          (MultiControl.computeWord k).reverse)))
                  (flatDataIndex (Fin.last (k + 3)))
              rw [FlatCircuit.flattenWord_append, FlatCircuit.flattenWord_cons,
                FlatCircuit.flattenWord_reverse]
              apply evalThreeBitWord_append_cons_reverse_changesOnlyAt
              · exact flattenComputeWord_avoids_final k
              · simp

/-- At data arity zero there is no final data coordinate; the explicit multi-control word is the
empty identity and preserves both universal enable coordinates. -/
theorem multiControlWord_zero_preservesUniversalAux :
    PreservesUniversalAux 0
      (FlatCircuit.evalFlattenWord 0 (MultiControl.word 0)) := by
  constructor <;> intros <;> rfl

private def nestedTargetEquiv {m : ℕ} (target : Fin (m + 1)) :
    Equiv.Perm (UniversalIndex (m + 1)) :=
  Equiv.sumCongr (Synthesis.Atomic.targetEquiv target)
    (Equiv.refl (UniversalAux (m + 1)))

private def flatTargetEquiv {m : ℕ} (target : Fin (m + 1)) :
    Equiv.Perm (Fin ((m + 1) + auxCount (m + 1))) :=
  (universalIndexFinEquiv (m + 1)).symm.trans
    ((nestedTargetEquiv target).trans (universalIndexFinEquiv (m + 1)))

@[simp]
private theorem flatTargetEquiv_data {m : ℕ} (target i : Fin (m + 1)) :
    flatTargetEquiv target (flatDataIndex i) =
      flatDataIndex (Synthesis.Atomic.targetEquiv target i) := by
  rw [← universalIndexFinEquiv_data i]
  simp only [flatTargetEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  change
    universalIndexFinEquiv (m + 1)
        (dataIndex (Synthesis.Atomic.targetEquiv target i)) =
      flatDataIndex (Synthesis.Atomic.targetEquiv target i)
  exact universalIndexFinEquiv_data _

private theorem flattenWord_reindex_nestedTarget {m : ℕ} (target : Fin (m + 1))
    (word : List (ThreeBitInstruction (UniversalIndex (m + 1)))) :
    FlatCircuit.flattenWord (m + 1)
        (ThreeBitCircuit.reindex (nestedTargetEquiv target) word) =
      ThreeBitCircuit.reindex (flatTargetEquiv target)
        (FlatCircuit.flattenWord (m + 1) word) := by
  unfold FlatCircuit.flattenWord ThreeBitCircuit.reindex
  simp only [List.map_map]
  apply List.map_congr_left
  intro instruction _hinstruction
  rw [ThreeBitInstruction.mk.injEq]
  ext i
  simp [ThreeBitInstruction.reindex, flatTargetEquiv]

/-- Transporting the canonical positive-control word to an arbitrary data target transports its
unique possible changed coordinate to that target. -/
theorem positiveWord_changesOnlyAt {n : ℕ} (target : Fin n) :
    ChangesOnlyAt
      (FlatCircuit.evalFlattenWord n (Synthesis.Atomic.positiveWord target))
      (flatDataIndex target) := by
  cases n with
  | zero => exact Fin.elim0 target
  | succ m =>
      rw [FlatCircuit.evalFlattenWord_eq]
      change
        ChangesOnlyAt
          (evalThreeBitWord
            (FlatCircuit.flattenWord (m + 1)
              (ThreeBitCircuit.reindex (nestedTargetEquiv target)
                (MultiControl.word (m + 1)))))
          (flatDataIndex target)
      rw [flattenWord_reindex_nestedTarget]
      have hcanonical := multiControlWord_changesOnlyAt m
      rw [FlatCircuit.evalFlattenWord_eq] at hcanonical
      have htransport := evalThreeBitWord_reindex_changesOnlyAt
        (flatTargetEquiv target)
        (FlatCircuit.flattenWord (m + 1) (MultiControl.word (m + 1)))
        (flatDataIndex (Fin.last m)) hcanonical
      simpa using htransport

private theorem flatEnableIndex_ne_flatDataIndex {n : ℕ} (enable : Fin 2)
    (data : Fin n) : flatEnableIndex enable ≠ flatDataIndex data := by
  intro heq
  have h := congrArg (universalIndexFinEquiv n).symm heq
  simp [enableIndex, dataIndex] at h

private theorem flatWorkIndex_ne_flatDataIndex {n : ℕ} (work : Fin (n - 3))
    (data : Fin n) : flatWorkIndex work ≠ flatDataIndex data := by
  intro heq
  have h := congrArg (universalIndexFinEquiv n).symm heq
  simp [workIndex, dataIndex] at h

/-- A map which can change only one data coordinate globally preserves the universal auxiliary
bank. -/
theorem changesOnlyAt_flatData_preservesUniversalAux {n : ℕ} (target : Fin n)
    {F : CirclePower (n + auxCount n) → CirclePower (n + auxCount n)}
    (hF : ChangesOnlyAt F (flatDataIndex target)) : PreservesUniversalAux n F := by
  constructor
  · intro p enable
    exact hF p (flatEnableIndex enable) (flatEnableIndex_ne_flatDataIndex enable target)
  · intro p work
    exact hF p (flatWorkIndex work) (flatWorkIndex_ne_flatDataIndex work target)

/-- The transported positive-control word therefore preserves the full universal auxiliary bank
for arbitrary circle-valued inputs. -/
theorem positiveWord_preservesUniversalAux {n : ℕ} (target : Fin n) :
    PreservesUniversalAux n
      (FlatCircuit.evalFlattenWord n (Synthesis.Atomic.positiveWord target)) :=
  changesOnlyAt_flatData_preservesUniversalAux target (positiveWord_changesOnlyAt target)

private theorem mem_flattenNotList_target {n : ℕ} (targets : List (Fin n))
    (instruction : ThreeBitInstruction (Fin (n + auxCount n)))
    (hinstruction : instruction ∈ FlatCircuit.flattenWord n (notList targets)) :
    ∃ target ∈ targets, instruction.target = flatDataIndex target := by
  rw [FlatCircuit.flattenWord, ThreeBitCircuit.reindex] at hinstruction
  simp only [List.mem_map] at hinstruction
  obtain ⟨original, horiginal, rfl⟩ := hinstruction
  rw [notList, List.mem_map] at horiginal
  obtain ⟨target, htarget, rfl⟩ := horiginal
  exact ⟨target, htarget, by simp⟩

/-- Every flattened masked-NOT word globally preserves both enable coordinates and every work
coordinate.  Enables may be read as controls, but no auxiliary coordinate is ever targeted. -/
theorem notMaskWord_preservesUniversalAux {n : ℕ} (mask : BoolVec n) :
    PreservesUniversalAux n
      (FlatCircuit.evalFlattenWord n (notMaskWord mask)) := by
  constructor
  · intro p enable
    rw [FlatCircuit.evalFlattenWord_eq]
    apply coord_evalThreeBitWord_of_forall_ne_target
    intro instruction hinstruction
    obtain ⟨target, _htarget, htargeteq⟩ :=
      mem_flattenNotList_target (maskTargets mask) instruction (by
        simpa only [notMaskWord] using hinstruction)
    rw [htargeteq]
    exact flatEnableIndex_ne_flatDataIndex enable target
  · intro p work
    rw [FlatCircuit.evalFlattenWord_eq]
    apply coord_evalThreeBitWord_of_forall_ne_target
    intro instruction hinstruction
    obtain ⟨target, _htarget, htargeteq⟩ :=
      mem_flattenNotList_target (maskTargets mask) instruction (by
        simpa only [notMaskWord] using hinstruction)
    rw [htargeteq]
    exact flatWorkIndex_ne_flatDataIndex work target

/-- Auxiliary preservation is closed under concatenating flattened synthesis words in execution
order. -/
theorem evalFlattenWord_append_preservesUniversalAux {n : ℕ}
    (first second : List (ThreeBitInstruction (UniversalIndex n)))
    (hfirst : PreservesUniversalAux n (FlatCircuit.evalFlattenWord n first))
    (hsecond : PreservesUniversalAux n (FlatCircuit.evalFlattenWord n second)) :
    PreservesUniversalAux n (FlatCircuit.evalFlattenWord n (first ++ second)) := by
  rw [FlatCircuit.evalFlattenWord_eq, FlatCircuit.flattenWord_append,
    evalThreeBitWord_append]
  exact hfirst.serial hsecond

/-- The complete normalize/positive-control/denormalize word for an atomic Boolean edge globally
preserves every universal auxiliary circle coordinate. -/
theorem atomicWord_preservesUniversalAux {n : ℕ} (step : AtomicStep (Fin n)) :
    PreservesUniversalAux n
      (FlatCircuit.evalFlattenWord n (Synthesis.Atomic.word step)) := by
  rw [Synthesis.Atomic.word]
  apply evalFlattenWord_append_preservesUniversalAux
  · apply evalFlattenWord_append_preservesUniversalAux
    · exact notMaskWord_preservesUniversalAux _
    · exact positiveWord_preservesUniversalAux step.target
  · exact notMaskWord_preservesUniversalAux _

end AtomicStability
end CircleExtension
end Toffoli
