import Mathlib.Data.Finset.Basic
import Toffoli.Bool.Defs

/-!
# Generalized Toffoli gates

A gate has one target and finitely many distinct positive controls. It complements the target
exactly when every control is `true`, and leaves every other component unchanged. The
specification itself does not choose a decidable-equality procedure; that is needed only when the
gate is executed.
-/

namespace Toffoli

universe u

/-- The data of a positive-control generalized Toffoli gate. -/
structure ToffoliGate (ι : Type u) where
  /-- Components that must all be `true` to enable the target flip. -/
  controls : Finset ι
  /-- The unique component that may change. -/
  target : ι
  /-- A target cannot also be one of its own controls. -/
  target_not_mem : target ∉ controls

namespace ToffoliGate

variable {ι : Type u}

/-- The positive controls of `g` are all satisfied by `x`. -/
def Active (g : ToffoliGate ι) (x : BoolWord ι) : Prop :=
  ∀ i ∈ g.controls, x i = true

instance activeDecidable (g : ToffoliGate ι) (x : BoolWord ι) : Decidable (g.Active x) := by
  unfold Active
  infer_instance

theorem control_ne_target (g : ToffoliGate ι) {i : ι} (hi : i ∈ g.controls) :
    i ≠ g.target := by
  intro hit
  subst i
  exact g.target_not_mem hi

/-- Complement the target when all positive controls are satisfied. -/
def run [DecidableEq ι] (g : ToffoliGate ι) (x : BoolWord ι) : BoolWord ι :=
  if g.Active x then Function.update x g.target (!(x g.target)) else x

theorem active_update_target [DecidableEq ι] (g : ToffoliGate ι) (x : BoolWord ι) (b : Bool) :
    g.Active (Function.update x g.target b) ↔ g.Active x := by
  constructor
  · intro h i hi
    rw [← Function.update_of_ne (g.control_ne_target hi) b x]
    exact h i hi
  · intro h i hi
    rw [Function.update_of_ne (g.control_ne_target hi) b x]
    exact h i hi

variable [DecidableEq ι]

@[simp]
theorem run_target (g : ToffoliGate ι) (x : BoolWord ι) :
    g.run x g.target = if g.Active x then !(x g.target) else x g.target := by
  by_cases h : g.Active x <;> simp [run, h]

theorem run_of_ne_target (g : ToffoliGate ι) (x : BoolWord ι) {i : ι}
    (hi : i ≠ g.target) : g.run x i = x i := by
  by_cases h : g.Active x <;> simp [run, h, Function.update_of_ne hi]

@[simp]
theorem run_control (g : ToffoliGate ι) (x : BoolWord ι) {i : ι}
    (hi : i ∈ g.controls) : g.run x i = x i :=
  g.run_of_ne_target x (g.control_ne_target hi)

@[simp]
theorem active_run_iff (g : ToffoliGate ι) (x : BoolWord ι) :
    g.Active (g.run x) ↔ g.Active x := by
  constructor
  · intro h i hi
    rw [← g.run_control x hi]
    exact h i hi
  · intro h i hi
    rw [g.run_control x hi]
    exact h i hi

theorem run_involutive (g : ToffoliGate ι) : Function.Involutive g.run := by
  intro x
  by_cases h : g.Active x
  · have hrun : g.run x = Function.update x g.target (!(x g.target)) := by
      simp [run, h]
    have ha : g.Active (g.run x) := (g.active_run_iff x).2 h
    change
      (if g.Active (g.run x) then Function.update (g.run x) g.target (!(g.run x g.target))
        else g.run x) = x
    rw [if_pos ha, hrun]
    simp
  · have hrun : g.run x = x := by simp [run, h]
    have ha : ¬g.Active (g.run x) := fun hx => h ((g.active_run_iff x).1 hx)
    change
      (if g.Active (g.run x) then Function.update (g.run x) g.target (!(g.run x g.target))
        else g.run x) = x
    rw [if_neg ha, hrun]

/-- The Boolean permutation implemented by a generalized Toffoli gate. -/
def perm (g : ToffoliGate ι) : BoolPerm ι where
  toFun := g.run
  invFun := g.run
  left_inv := g.run_involutive
  right_inv := g.run_involutive

@[simp]
theorem perm_apply (g : ToffoliGate ι) (x : BoolWord ι) : g.perm x = g.run x :=
  rfl

@[simp]
theorem perm_symm (g : ToffoliGate ι) : g.perm.symm = g.perm :=
  rfl

@[simp]
theorem perm_trans_self (g : ToffoliGate ι) : g.perm.trans g.perm = Equiv.refl _ := by
  apply Equiv.ext
  exact g.run_involutive

theorem run_target_of_active (g : ToffoliGate ι) (x : BoolWord ι) (h : g.Active x) :
    g.run x g.target = !(x g.target) := by
  simp [h]

theorem run_target_of_not_active (g : ToffoliGate ι) (x : BoolWord ι)
    (h : ¬g.Active x) : g.run x g.target = x g.target := by
  simp [h]

theorem run_eq_self_iff (g : ToffoliGate ι) (x : BoolWord ι) :
    g.run x = x ↔ ¬g.Active x := by
  constructor
  · intro heq hactive
    have htarget := congrFun heq g.target
    rw [g.run_target_of_active x hactive] at htarget
    exact Bool.not_ne_self _ htarget
  · intro h
    simp [run, h]

theorem run_ne_iff (g : ToffoliGate ι) (x : BoolWord ι) (i : ι) :
    g.run x i ≠ x i ↔ i = g.target ∧ g.Active x := by
  by_cases hi : i = g.target
  · subst i
    by_cases hx : g.Active x
    · simp [g.run_target_of_active x hx, hx]
    · simp [g.run_target_of_not_active x hx, hx]
  · simp [g.run_of_ne_target x hi, hi]

/-- With a false target, the target output is the conjunction of the controls. -/
theorem target_false_is_and (g : ToffoliGate ι) (x : BoolWord ι) :
    g.run (Function.update x g.target false) g.target = decide (g.Active x) := by
  by_cases h : g.Active x
  · have hu : g.Active (Function.update x g.target false) := (g.active_update_target x false).2 h
    simp [run, h, hu]
  · have hu : ¬g.Active (Function.update x g.target false) :=
      fun ha => h ((g.active_update_target x false).1 ha)
    simp [run, h, hu]

/-- With a true target, the target output is the NAND of the controls. -/
theorem target_true_is_nand (g : ToffoliGate ι) (x : BoolWord ι) :
    g.run (Function.update x g.target true) g.target = !(decide (g.Active x)) := by
  by_cases h : g.Active x
  · have hu : g.Active (Function.update x g.target true) := (g.active_update_target x true).2 h
    simp [run, h, hu]
  · have hu : ¬g.Active (Function.update x g.target true) :=
      fun ha => h ((g.active_update_target x true).1 ha)
    simp [run, h, hu]

/-- The target-only gate. Its empty conjunction is always active, so this is NOT. -/
def notAt (target : ι) : ToffoliGate ι where
  controls := ∅
  target := target
  target_not_mem := Finset.notMem_empty target

omit [DecidableEq ι] in
@[simp]
theorem notAt_active (target : ι) (x : BoolWord ι) : (notAt target).Active x := by
  simp [Active, notAt]

@[simp]
theorem notAt_apply_target (target : ι) (x : BoolWord ι) :
    (notAt target).perm x target = !(x target) := by
  exact (notAt target).run_target_of_active x (notAt_active target x)

/-- A one-control gate. Distinctness of the control and target is explicit. -/
def cnot (control target : ι) (h : control ≠ target) : ToffoliGate ι where
  controls := {control}
  target := target
  target_not_mem := by simpa [eq_comm] using h

omit [DecidableEq ι] in
@[simp]
theorem cnot_active (control target : ι) (h : control ≠ target) (x : BoolWord ι) :
    (cnot control target h).Active x ↔ x control = true := by
  classical
  simp [Active, cnot]

/-- A two-control, one-target gate on three specified distinct coordinates. -/
def ccnot (control₁ control₂ target : ι) (_h₁₂ : control₁ ≠ control₂)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) : ToffoliGate ι where
  controls := {control₁, control₂}
  target := target
  target_not_mem := by simp [h₁t, h₂t, eq_comm]

@[simp]
theorem ccnot_active (control₁ control₂ target : ι) (h₁₂ : control₁ ≠ control₂)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) (x : BoolWord ι) :
    (ccnot control₁ control₂ target h₁₂ h₁t h₂t).Active x ↔
      x control₁ = true ∧ x control₂ = true := by
  simp [Active, ccnot]

end ToffoliGate

end Toffoli
