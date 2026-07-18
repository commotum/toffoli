import Mathlib.Data.Finite.Prod
import Mathlib.GroupTheory.Perm.Sign
import Toffoli.Perm.AtomicWord

/-!
# Decomposition of Boolean permutations into atomic edge flips

This is the deliberately heavy finite-group leaf of the Boolean development.  Mathlib first
factors a finite permutation by induction on transpositions.  Each transposition is then replaced
by the exact palindromic Boolean-cube word from `Toffoli.Perm.AtomicWord`.
-/

namespace Toffoli

universe u

namespace AtomicWord

variable {ι : Type u} [Finite ι] [DecidableEq ι] [DecidableEq (BoolWord ι)]

/-- Every finite Boolean permutation has a serial decomposition into literal cube-edge
transpositions.  Entries of the returned list act from left to right. -/
theorem exists_eval_eq (p : BoolPerm ι) :
    ∃ word : List (AtomicStep ι), eval word = p := by
  classical
  letI := Fintype.ofFinite ι
  induction p using Equiv.Perm.swap_induction_on with
  | one =>
      exact ⟨[], rfl⟩
  | swap_mul f x y hxy ih =>
      obtain ⟨initial, hinitial⟩ := ih
      refine ⟨initial ++ IsEndpointWord.word x y, ?_⟩
      rw [eval_append, hinitial, IsEndpointWord.eval_word, ← Equiv.Perm.mul_def]

/-- A chosen atomic decomposition.  Use `eval_decompose` rather than relying on the choice of
word or on any particular factorization algorithm. -/
noncomputable def decompose (p : BoolPerm ι) : List (AtomicStep ι) :=
  (exists_eval_eq p).choose

/-- The chosen atomic decomposition evaluates to the original permutation. -/
theorem eval_decompose (p : BoolPerm ι) : eval (decompose p) = p :=
  (exists_eval_eq p).choose_spec

end AtomicWord

end Toffoli
