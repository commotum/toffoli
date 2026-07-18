import Mathlib.Data.Fin.VecNotation
import Toffoli.Bool.Finite
import Toffoli.Perm.Decomposition

/-!
# Gray-decomposition boundary checks

These exhaustive low-dimensional checks guard the declared serial order and Boolean coordinate
conventions.  The public decomposition theorem is proved generically; none of these computations
is imported by the library facades.
-/

namespace Toffoli.Audit

open Toffoli

example : IsEmpty (AtomicStep (Fin 0)) :=
  ⟨fun step => Fin.elim0 step.target⟩

example (p : BoolPermN 0) :
    AtomicWord.eval ([] : List (AtomicStep (Fin 0))) = p := by
  rw [boolPermN_zero_eq_refl p]
  rfl

example : atomicEdge ![false] (0 : Fin 1) ![false] = ![true] := by
  decide

example : atomicEdge ![false] (0 : Fin 1) ![true] = ![false] := by
  decide

/-- The exact palindrome for the path `00 → 10 → 11`, with the first list entry acting first. -/
def twoBitPalindrome : List (AtomicStep (Fin 2)) :=
  [⟨![false, false], 0⟩, ⟨![true, false], 1⟩, ⟨![false, false], 0⟩]

example : AtomicWord.eval twoBitPalindrome ![false, false] = ![true, true] := by
  decide

example : AtomicWord.eval twoBitPalindrome ![true, true] = ![false, false] := by
  decide

example : AtomicWord.eval twoBitPalindrome ![true, false] = ![true, false] := by
  decide

example : AtomicWord.eval twoBitPalindrome ![false, true] = ![false, true] := by
  decide

example (p : BoolPermN 1) : ∃ word, AtomicWord.eval word = p :=
  AtomicWord.exists_eval_eq p

example (p : BoolPermN 2) : ∃ word, AtomicWord.eval word = p :=
  AtomicWord.exists_eval_eq p

end Toffoli.Audit
