import Toffoli.Circuit.ThreeBitTransport
import Toffoli.Smooth.ThreeBitCircuit
import Toffoli.Smooth.UniversalLayout

/-!
# Flattening universal placed-gate circuits for smooth evaluation

Discrete synthesis words use the nested coordinate type `UniversalIndex n`.  Recursive circle
products are indexed by a natural number, so this bridge transports every instruction along
`universalIndexFinEquiv n` before applying the smooth placed-gate evaluator.

The transport changes only the coordinate presentation.  The theorems below relate evaluation
of the flattened smooth circuit to evaluation of the original nested Boolean circuit on every
Boolean word, with a specialization to the universal data-and-constant input.  No decomposition,
universality, or auxiliary-stability theorem is imported here.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension
namespace FlatCircuit

open Synthesis

/-- Transport a nested universal-index word to the consecutive flat circle coordinates. -/
def flattenWord (n : ℕ) (word : List (ThreeBitInstruction (UniversalIndex n))) :
    List (ThreeBitInstruction (Fin (n + auxCount n))) :=
  ThreeBitCircuit.reindex (universalIndexFinEquiv n) word

@[simp]
theorem flattenedInstruction_control₁ {n : ℕ}
    (instruction : ThreeBitInstruction (UniversalIndex n)) :
    (ThreeBitInstruction.reindex (universalIndexFinEquiv n) instruction).control₁ =
      universalIndexFinEquiv n instruction.control₁ :=
  rfl

@[simp]
theorem flattenedInstruction_control₂ {n : ℕ}
    (instruction : ThreeBitInstruction (UniversalIndex n)) :
    (ThreeBitInstruction.reindex (universalIndexFinEquiv n) instruction).control₂ =
      universalIndexFinEquiv n instruction.control₂ :=
  rfl

@[simp]
theorem flattenedInstruction_target {n : ℕ}
    (instruction : ThreeBitInstruction (UniversalIndex n)) :
    (ThreeBitInstruction.reindex (universalIndexFinEquiv n) instruction).target =
      universalIndexFinEquiv n instruction.target :=
  rfl

@[simp]
theorem flattenWord_nil (n : ℕ) :
    flattenWord n ([] : List (ThreeBitInstruction (UniversalIndex n))) = [] :=
  rfl

@[simp]
theorem flattenWord_cons {n : ℕ} (instruction : ThreeBitInstruction (UniversalIndex n))
    (word : List (ThreeBitInstruction (UniversalIndex n))) :
    flattenWord n (instruction :: word) =
      ThreeBitInstruction.reindex (universalIndexFinEquiv n) instruction ::
        flattenWord n word :=
  rfl

theorem flattenWord_append {n : ℕ} (first second : List (ThreeBitInstruction (UniversalIndex n))) :
    flattenWord n (first ++ second) = flattenWord n first ++ flattenWord n second := by
  simp [flattenWord, ThreeBitCircuit.reindex, List.map_append]

@[simp]
theorem flattenWord_reverse {n : ℕ} (word : List (ThreeBitInstruction (UniversalIndex n))) :
    flattenWord n word.reverse = (flattenWord n word).reverse := by
  simp [flattenWord, ThreeBitCircuit.reindex]

/-- Smooth evaluation of a nested synthesis word after flattening its coordinate layout. -/
def evalFlattenWord (n : ℕ) (word : List (ThreeBitInstruction (UniversalIndex n))) :
    Diffeomorph (circlePowerModel (n + auxCount n)) (circlePowerModel (n + auxCount n))
      (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞ :=
  evalThreeBitWord (flattenWord n word)

/-- Definitional equation exposing the lower smooth word evaluator. -/
theorem evalFlattenWord_eq (n : ℕ) (word : List (ThreeBitInstruction (UniversalIndex n))) :
    evalFlattenWord n word = evalThreeBitWord (flattenWord n word) :=
  rfl

@[simp]
theorem evalFlattenWord_nil (n : ℕ) :
    evalFlattenWord n ([] : List (ThreeBitInstruction (UniversalIndex n))) =
      Diffeomorph.refl (circlePowerModel (n + auxCount n))
        (CirclePower (n + auxCount n)) ∞ :=
  rfl

/-- At the Boolean level, flattening is exactly conjugation by the layout reindexing. -/
theorem boolEval_flattenWord {n : ℕ}
    (word : List (ThreeBitInstruction (UniversalIndex n))) :
    ThreeBitCircuit.eval (flattenWord n word) =
      BoolPerm.reindex (universalIndexFinEquiv n) (ThreeBitCircuit.eval word) := by
  exact ThreeBitCircuit.eval_reindex (universalIndexFinEquiv n) word

/-- Boolean evaluation commutes with flattening when both the input and output words are
transported along the universal layout equivalence. -/
theorem eval_flattenWord_reindex {n : ℕ}
    (word : List (ThreeBitInstruction (UniversalIndex n)))
    (x : BoolWord (UniversalIndex n)) :
    ThreeBitCircuit.eval (flattenWord n word)
        (BoolWord.reindex (universalIndexFinEquiv n) x) =
      BoolWord.reindex (universalIndexFinEquiv n) (ThreeBitCircuit.eval word x) := by
  rw [boolEval_flattenWord]
  funext j
  simp [BoolPerm.reindex_apply]

/-- Exact Boolean interpolation for an arbitrary nested synthesis word and arbitrary nested
Boolean input. -/
theorem evalFlattenWord_interpolates {n : ℕ}
    (word : List (ThreeBitInstruction (UniversalIndex n)))
    (x : BoolWord (UniversalIndex n)) :
    evalFlattenWord n word
        (embed (n + auxCount n) (BoolWord.reindex (universalIndexFinEquiv n) x)) =
      embed (n + auxCount n)
        (BoolWord.reindex (universalIndexFinEquiv n) (ThreeBitCircuit.eval word x)) := by
  rw [evalFlattenWord, evalThreeBitWord_interpolates, eval_flattenWord_reindex]

/-- On the universal data-and-constant input, the flattened smooth circuit interpolates the
original nested Boolean circuit evaluated on `universalInput x`. -/
theorem evalFlattenWord_interpolates_universalInput {n : ℕ}
    (word : List (ThreeBitInstruction (UniversalIndex n))) (x : BoolVec n) :
    evalFlattenWord n word (embed (n + auxCount n) (flatUniversalInput x)) =
      embed (n + auxCount n)
        (BoolWord.reindex (universalIndexFinEquiv n)
          (ThreeBitCircuit.eval word (universalInput x))) := by
  simpa only [flatUniversalInput] using evalFlattenWord_interpolates word (universalInput x)

private theorem noInstructionAtZero (instruction : ThreeBitInstruction (UniversalIndex 0)) :
    False := by
  have hcard := Fintype.card_le_of_embedding instruction.placement
  rw [card_universalIndex] at hcard
  norm_num [auxCount] at hcard

/-- At data arity zero the uniform ambient layout has only its two enable coordinates, so no
three-bit instruction—and hence no nonempty placed-gate word—exists. -/
theorem flattenWord_zero_eq_nil (word : List (ThreeBitInstruction (UniversalIndex 0))) :
    flattenWord 0 word = [] := by
  cases word with
  | nil => rfl
  | cons instruction _ => exact (noInstructionAtZero instruction).elim

/-- Consequently every flattened zero-data word evaluates to the identity on the two-coordinate
uniform ambient product. -/
theorem evalFlattenWord_zero_eq_refl (word : List (ThreeBitInstruction (UniversalIndex 0))) :
    evalFlattenWord 0 word =
      Diffeomorph.refl (circlePowerModel (0 + auxCount 0))
        (CirclePower (0 + auxCount 0)) ∞ := by
  rw [evalFlattenWord, flattenWord_zero_eq_nil]
  rfl

end FlatCircuit
end CircleExtension
end Toffoli
