import Mathlib.Data.Fin.Tuple.Embedding
import Toffoli.Gate.AndNand
import Toffoli.Gate.Wiring

/-!
# Placed three-bit Toffoli circuits

An instruction carries an embedding of the three canonical gate coordinates into an ambient
coordinate type.  The embedding is the distinctness certificate: coordinate `0` is the first
control, coordinate `1` is the second control, and coordinate `2` is the target.

Circuit words are evaluated from left to right.  Thus the head instruction acts first, matching
the serial-composition convention used by `OneToOneCircuit` and `AtomicWord`.
-/

namespace Toffoli

universe u

/-- One occurrence of the canonical three-bit Toffoli gate in an ambient coordinate type. -/
structure ThreeBitInstruction (ι : Type u) where
  /-- Placement of canonical coordinates `0, 1, 2` into pairwise-distinct ambient coordinates. -/
  placement : Fin 3 ↪ ι

namespace ThreeBitInstruction

variable {ι : Type u}

/-- The first positive control. -/
def control₁ (g : ThreeBitInstruction ι) : ι :=
  g.placement 0

/-- The second positive control. -/
def control₂ (g : ThreeBitInstruction ι) : ι :=
  g.placement 1

/-- The complemented target. -/
def target (g : ThreeBitInstruction ι) : ι :=
  g.placement 2

@[simp]
theorem control₁_ne_control₂ (g : ThreeBitInstruction ι) : g.control₁ ≠ g.control₂ :=
  g.placement.injective.ne (by decide)

@[simp]
theorem control₁_ne_target (g : ThreeBitInstruction ι) : g.control₁ ≠ g.target :=
  g.placement.injective.ne (by decide)

@[simp]
theorem control₂_ne_target (g : ThreeBitInstruction ι) : g.control₂ ≠ g.target :=
  g.placement.injective.ne (by decide)

private theorem target_not_mem_embFinTwo_range (control₁ control₂ target : ι)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target)
    (h₂t : control₂ ≠ target) :
    target ∉ Set.range (Function.Embedding.embFinTwo h₁₂) := by
  rintro ⟨i, hi⟩
  by_cases hzero : i = 0
  · subst i
    exact h₁t hi
  · rw [Fin.eq_one_of_ne_zero i hzero] at hi
    exact h₂t hi

/-- Build a placement from three explicitly distinct coordinates. -/
def ofDistinct (control₁ control₂ target : ι) (h₁₂ : control₁ ≠ control₂)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) : ThreeBitInstruction ι where
  placement := Fin.Embedding.snoc (Function.Embedding.embFinTwo h₁₂)
    (target_not_mem_embFinTwo_range control₁ control₂ target h₁₂ h₁t h₂t)

@[simp]
theorem ofDistinct_control₁ (control₁ control₂ target : ι) (h₁₂ : control₁ ≠ control₂)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    (ofDistinct control₁ control₂ target h₁₂ h₁t h₂t).control₁ = control₁ := by
  change (Fin.Embedding.snoc (Function.Embedding.embFinTwo h₁₂)
    (target_not_mem_embFinTwo_range control₁ control₂ target h₁₂ h₁t h₂t)) 0 = control₁
  rw [show (0 : Fin 3) = (0 : Fin 2).castSucc by rfl, Fin.Embedding.snoc_castSucc]
  exact Function.Embedding.embFinTwo_apply_zero h₁₂

@[simp]
theorem ofDistinct_control₂ (control₁ control₂ target : ι) (h₁₂ : control₁ ≠ control₂)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    (ofDistinct control₁ control₂ target h₁₂ h₁t h₂t).control₂ = control₂ := by
  change (Fin.Embedding.snoc (Function.Embedding.embFinTwo h₁₂)
    (target_not_mem_embFinTwo_range control₁ control₂ target h₁₂ h₁t h₂t)) 1 = control₂
  rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl, Fin.Embedding.snoc_castSucc]
  exact Function.Embedding.embFinTwo_apply_one h₁₂

@[simp]
theorem ofDistinct_target (control₁ control₂ target : ι) (h₁₂ : control₁ ≠ control₂)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    (ofDistinct control₁ control₂ target h₁₂ h₁t h₂t).target = target := by
  change (Fin.Embedding.snoc (Function.Embedding.embFinTwo h₁₂)
    (target_not_mem_embFinTwo_range control₁ control₂ target h₁₂ h₁t h₂t)) 2 = target
  rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.Embedding.snoc_last]

/-- The actual generalized-Toffoli specification of a placed instruction. -/
def gate (g : ThreeBitInstruction ι) : ToffoliGate ι :=
  (AndNand.thetaSuccSpec 2).map g.placement

@[simp]
theorem gate_target (g : ThreeBitInstruction ι) : g.gate.target = g.target :=
  rfl

@[simp]
theorem gate_active_iff (g : ThreeBitInstruction ι) (x : BoolWord ι) :
    g.gate.Active x ↔ x g.control₁ = true ∧ x g.control₂ = true := by
  rw [gate, ToffoliGate.map_active_iff]
  simp [control₁, control₂]

/-- The Boolean permutation implemented by a placed instruction. -/
def perm [DecidableEq ι] (g : ThreeBitInstruction ι) : BoolPerm ι :=
  g.gate.perm

variable [DecidableEq ι]

@[simp]
theorem perm_symm (g : ThreeBitInstruction ι) : g.perm.symm = g.perm :=
  g.gate.perm_symm

@[simp]
theorem perm_trans_self (g : ThreeBitInstruction ι) : g.perm.trans g.perm = Equiv.refl _ :=
  g.gate.perm_trans_self

@[simp]
theorem perm_apply_control₁ (g : ThreeBitInstruction ι) (x : BoolWord ι) :
    g.perm x g.control₁ = x g.control₁ :=
  g.gate.perm_apply_of_ne_target x g.control₁_ne_target

@[simp]
theorem perm_apply_control₂ (g : ThreeBitInstruction ι) (x : BoolWord ι) :
    g.perm x g.control₂ = x g.control₂ :=
  g.gate.perm_apply_of_ne_target x g.control₂_ne_target

@[simp]
theorem perm_apply_target (g : ThreeBitInstruction ι) (x : BoolWord ι) :
    g.perm x g.target =
      if x g.control₁ = true ∧ x g.control₂ = true then !(x g.target) else x g.target := by
  rw [perm]
  simpa only [gate_target, gate_active_iff] using g.gate.perm_apply_target x

theorem perm_apply_of_ne_target (g : ThreeBitInstruction ι) (x : BoolWord ι) {i : ι}
    (hi : i ≠ g.target) : g.perm x i = x i :=
  g.gate.perm_apply_of_ne_target x (by simpa using hi)

end ThreeBitInstruction

namespace ThreeBitCircuit

variable {ι : Type u} [DecidableEq ι]

/-- Evaluate a word of placed gates from left to right. -/
def eval : List (ThreeBitInstruction ι) → BoolPerm ι
  | [] => Equiv.refl _
  | gate :: word => gate.perm.trans (eval word)

@[simp]
theorem eval_nil : eval ([] : List (ThreeBitInstruction ι)) = Equiv.refl _ :=
  rfl

@[simp]
theorem eval_cons (gate : ThreeBitInstruction ι) (word : List (ThreeBitInstruction ι)) :
    eval (gate :: word) = gate.perm.trans (eval word) :=
  rfl

@[simp]
theorem eval_cons_apply (gate : ThreeBitInstruction ι) (word : List (ThreeBitInstruction ι))
    (x : BoolWord ι) : eval (gate :: word) x = eval word (gate.perm x) :=
  rfl

@[simp]
theorem eval_singleton (gate : ThreeBitInstruction ι) : eval [gate] = gate.perm := by
  simp [eval]

/-- Appending words agrees with serial composition: the left word acts first. -/
theorem eval_append (first second : List (ThreeBitInstruction ι)) :
    eval (first ++ second) = (eval first).trans (eval second) := by
  induction first with
  | nil => rfl
  | cons gate first ih =>
      simp only [List.cons_append, eval_cons, ih]
      exact Equiv.trans_assoc _ _ _

@[simp]
theorem eval_reverse (word : List (ThreeBitInstruction ι)) :
    eval word.reverse = (eval word).symm := by
  induction word with
  | nil => rfl
  | cons gate word ih =>
      rw [List.reverse_cons, eval_append, ih]
      simp

@[simp]
theorem eval_append_reverse (word : List (ThreeBitInstruction ι)) :
    eval (word ++ word.reverse) = Equiv.refl _ := by
  rw [eval_append, eval_reverse]
  exact Equiv.self_trans_symm _

/-- A coordinate not targeted anywhere in a word is unchanged by the whole word. -/
theorem eval_apply_of_forall_ne_target (word : List (ThreeBitInstruction ι)) (x : BoolWord ι)
    {i : ι} (hi : ∀ gate ∈ word, i ≠ gate.target) : eval word x i = x i := by
  induction word generalizing x with
  | nil => rfl
  | cons gate word ih =>
      rw [eval_cons_apply, ih]
      · exact gate.perm_apply_of_ne_target x (hi gate (by simp))
      · intro next hnext
        exact hi next (by simp [hnext])

end ThreeBitCircuit

end Toffoli
