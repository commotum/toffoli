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

end AtomicStability
end CircleExtension
end Toffoli
