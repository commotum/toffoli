import Toffoli.Cube.Path

/-!
# Serial words of atomic Boolean edge permutations

The evaluator uses `Equiv.trans`: list entries act from left to right. `IsEndpointWord x y word`
records the exact Gray-path palindrome omitted by the paper. In the recursive case the word is

`edge(x,z) :: middle ++ [edge(x,z)]`,

where `middle` exchanges `z` and `y`. Thus evaluation exchanges only `x` and `y`.
-/

namespace Toffoli

universe u

/-- One oriented Boolean-cube edge instruction. Its permutation is independent of orientation. -/
structure AtomicStep (ι : Type u) where
  base : BoolWord ι
  target : ι

namespace AtomicStep

variable {ι : Type u} [DecidableEq ι] [DecidableEq (BoolWord ι)]

/-- Interpret an atomic instruction as its literal edge transposition. -/
def perm (step : AtomicStep ι) : BoolPerm ι :=
  atomicEdge step.base step.target

end AtomicStep

namespace AtomicWord

variable {ι : Type u} [DecidableEq ι] [DecidableEq (BoolWord ι)]

/-- Evaluate an atomic word in serial order: the list head acts first. -/
def eval : List (AtomicStep ι) → BoolPerm ι
  | [] => Equiv.refl _
  | step :: steps => step.perm.trans (eval steps)

@[simp]
theorem eval_nil : eval ([] : List (AtomicStep ι)) = Equiv.refl _ :=
  rfl

@[simp]
theorem eval_cons (step : AtomicStep ι) (steps : List (AtomicStep ι)) :
    eval (step :: steps) = step.perm.trans (eval steps) :=
  rfl

@[simp]
theorem eval_singleton (step : AtomicStep ι) : eval [step] = step.perm := by
  simp [eval]

theorem eval_append (first second : List (AtomicStep ι)) :
    eval (first ++ second) = (eval first).trans (eval second) := by
  induction first with
  | nil => simp
  | cons step steps ih =>
      simp only [List.cons_append, eval_cons, ih, Equiv.trans_assoc]

end AtomicWord

/-- The exact palindromic atomic word exchanging two endpoints of a Gray path. -/
inductive IsEndpointWord {ι : Type u} [DecidableEq ι] :
    BoolWord ι → BoolWord ι → List (AtomicStep ι) → Prop
  | refl (x : BoolWord ι) : IsEndpointWord x x []
  | edge (x : BoolWord ι) (target : ι) :
      IsEndpointWord x (x.flipAt target) [⟨x, target⟩]
  | palindrome {x z y : BoolWord ι} {target : ι} {middle : List (AtomicStep ι)}
      (hz : z = x.flipAt target) (hxy : x ≠ y) (hzy : z ≠ y)
      (inner : IsEndpointWord z y middle) :
      IsEndpointWord x y (⟨x, target⟩ :: (middle ++ [⟨x, target⟩]))

namespace IsEndpointWord

variable {ι : Type u} [DecidableEq ι] [DecidableEq (BoolWord ι)]

private theorem swap_palindrome {α : Type*} [DecidableEq α] (x z y : α)
    (hxy : x ≠ y) (hzy : z ≠ y) :
    ((Equiv.swap x z).trans (Equiv.swap z y)).trans (Equiv.swap x z) = Equiv.swap x y := by
  have hy : Equiv.swap x z y = y :=
    Equiv.swap_apply_of_ne_of_ne hxy.symm hzy.symm
  simpa [hy] using Equiv.symm_trans_swap_trans z y (Equiv.swap x z)

/-- Every endpoint-word derivation evaluates to the literal transposition of its endpoints. -/
theorem eval_eq_swap {x y : BoolWord ι} {word : List (AtomicStep ι)}
    (h : IsEndpointWord x y word) : AtomicWord.eval word = Equiv.swap x y := by
  induction h with
  | refl x => simp
  | edge x target => simp [AtomicStep.perm, atomicEdge]
  | @palindrome x z y target middle hz hxy hzy inner ih =>
      cases hz
      simp only [AtomicWord.eval]
      rw [AtomicWord.eval_append, AtomicWord.eval_singleton, ih, ← Equiv.trans_assoc]
      exact swap_palindrome x (x.flipAt target) y hxy hzy

/-- A Gray-path palindrome exists between every two vertices of a finite Boolean cube. -/
omit [DecidableEq (BoolWord ι)] in
theorem exists_word [Finite ι] (x y : BoolWord ι) : ∃ word, IsEndpointWord x y word := by
  classical
  letI := Fintype.ofFinite ι
  induction hcard : (x.diff y).card using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hxy : x = y
      · subst x
        exact ⟨[], IsEndpointWord.refl y⟩
      · have hnonempty : (x.diff y).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          exact fun hempty => hxy ((BoolWord.diff_eq_empty_iff x y).1 hempty)
        obtain ⟨target, htarget⟩ := hnonempty
        let z := x.flipAt target
        by_cases hzy : z = y
        · subst y
          exact ⟨[⟨x, target⟩], IsEndpointWord.edge x target⟩
        · obtain ⟨middle, hmiddle⟩ :=
            ih ((z.diff y).card)
              (by
                simpa [z, hcard] using BoolWord.card_diff_flipAt_lt x y htarget)
              z rfl
          exact
            ⟨⟨x, target⟩ :: (middle ++ [⟨x, target⟩]),
              IsEndpointWord.palindrome rfl hxy hzy hmiddle⟩

/-- A chosen endpoint word, useful as a reusable decomposition witness. -/
omit [DecidableEq (BoolWord ι)] in
noncomputable def word [Finite ι] (x y : BoolWord ι) : List (AtomicStep ι) :=
  (exists_word x y).choose

omit [DecidableEq (BoolWord ι)] in
theorem word_spec [Finite ι] (x y : BoolWord ι) : IsEndpointWord x y (word x y) :=
  (exists_word x y).choose_spec

/-- The chosen word evaluates in the documented left-to-right order to `swap x y`. -/
theorem eval_word [Finite ι] (x y : BoolWord ι) :
    AtomicWord.eval (word x y) = Equiv.swap x y :=
  (word_spec x y).eval_eq_swap

end IsEndpointWord

end Toffoli
