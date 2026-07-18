import Toffoli.Circuit.ThreeBitTransport
import Toffoli.Perm.AtomicWord
import Toffoli.Synthesis.MultiControl
import Toffoli.Synthesis.Not

/-!
# Clean synthesis of atomic Boolean edge permutations

The generalized positive-control circuit is first transported from its canonical last target to
the target named by the atomic instruction.  A componentwise NOT mask then normalizes the chosen
edge to the all-true edge before that gate and denormalizes it afterward.  Circuit lists are in
execution order, so the masked-NOT word occurs on both sides of the transported gate word.
-/

namespace Toffoli

namespace Synthesis

namespace Atomic

/-- Swap the canonical last coordinate with a requested target. -/
def targetEquiv {m : ℕ} (target : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.swap (Fin.last m) target

@[simp]
theorem targetEquiv_apply_last {m : ℕ} (target : Fin (m + 1)) :
    targetEquiv target (Fin.last m) = target := by
  simp [targetEquiv]

/-- The positive-control circuit word with its canonical last target transported to `target`.
The zero-arity branch is eliminated by the impossible target coordinate. -/
noncomputable def positiveWord : {n : ℕ} → Fin n →
    List (ThreeBitInstruction (UniversalIndex n))
  | 0, target => Fin.elim0 target
  | m + 1, target =>
      ThreeBitCircuit.reindex
        (Equiv.sumCongr (targetEquiv target) (Equiv.refl (UniversalAux (m + 1))))
        (MultiControl.word (m + 1))

/-- The transported positive-control word cleanly realizes the AND/NAND gate with the requested
target. -/
theorem positiveWord_cleanRealizes {n : ℕ} (target : Fin n) :
    CleanRealizes (ThreeBitCircuit.eval (positiveWord target)) (universalConstants n)
      (ToffoliGate.andNand target) := by
  cases n with
  | zero => exact Fin.elim0 target
  | succ m =>
      have h := cleanRealizes_reindexData (targetEquiv target)
        (MultiControl.word (m + 1)) (universalConstants (m + 1))
        (AndNand.thetaSucc m) (MultiControl.word_cleanRealizes m)
      change
        CleanRealizes
          (ThreeBitCircuit.eval
            (ThreeBitCircuit.reindex
              (Equiv.sumCongr (targetEquiv target)
                (Equiv.refl (UniversalAux (m + 1))))
              (MultiControl.word (m + 1))))
          (universalConstants (m + 1))
          (BoolPerm.reindex (targetEquiv target)
            (ToffoliGate.andNand (Fin.last m))) at h
      rw [ToffoliGate.reindex_andNand] at h
      simpa [positiveWord] using h

/-- The Boolean mask implementing the verified edge normalizer for an atomic instruction. -/
def normalizerMask {n : ℕ} (step : AtomicStep (Fin n)) : BoolVec n :=
  fun i => !(step.base i)

/-- Explicit left-to-right three-bit circuit word for an atomic edge: normalize, apply the
transported all-positive gate, then denormalize. -/
noncomputable def word {n : ℕ} (step : AtomicStep (Fin n)) :
    List (ThreeBitInstruction (UniversalIndex n)) :=
  (notMaskWord (normalizerMask step) ++ positiveWord step.target) ++
    notMaskWord (normalizerMask step)

/-- Every literal atomic cube edge has a clean realization over the shared universal auxiliary
bank. -/
theorem word_cleanRealizes {n : ℕ} (step : AtomicStep (Fin n)) :
    CleanRealizes (ThreeBitCircuit.eval (word step)) (universalConstants n) step.perm := by
  let mask : BoolVec n := normalizerMask step
  have hnot := notMaskWord_cleanRealizes mask
  have hpositive := positiveWord_cleanRealizes step.target
  have hserial := (hnot.serial hpositive).serial hnot
  have htarget :
      ((BoolWord.flipMaskEquiv mask).trans (ToffoliGate.andNand step.target)).trans
          (BoolWord.flipMaskEquiv mask) =
        step.perm := by
    rw [AtomicStep.perm, ToffoliGate.atomicEdge_eq_edgeNormalizer_permCongr_andNand]
    rfl
  rw [word, ThreeBitCircuit.eval_append, ThreeBitCircuit.eval_append, ← htarget]
  exact hserial

end Atomic

end Synthesis

end Toffoli
