import Mathlib.Data.List.OfFn
import Toffoli.Circuit.ThreeBit
import Toffoli.Cube.Basic
import Toffoli.Synthesis.FaceRealization
import Toffoli.Synthesis.Resources

/-!
# Clean synthesis of generalized positive-control gates

This leaf constructs the paper's higher-arity AND/NAND permutations from explicitly placed
three-bit Toffoli instructions.  The two left auxiliary coordinates are persistent `true` enable
bits; the remaining auxiliary coordinates are initially `false` work bits.  At arity at least
four, a forward ladder computes prefix conjunctions, one instruction acts on the data target,
and the exact reversed ladder uncomputes every work bit.

Circuit lists are in execution order: their leftmost instruction acts first.
-/

namespace Toffoli

namespace Synthesis

namespace MultiControl

/-- Insert data and the clean auxiliary word into the ambient cube. -/
def inputState {n : ℕ} (x : BoolVec n) : BoolWord (UniversalIndex n) :=
  BoolWord.sumEquiv.symm (x, universalConstants n)

@[simp]
theorem inputState_data {n : ℕ} (x : BoolVec n) (i : Fin n) :
    inputState x (dataIndex i) = x i :=
  rfl

@[simp]
theorem inputState_enable {n : ℕ} (x : BoolVec n) (i : Fin 2) :
    inputState x (enableIndex i) = true :=
  rfl

@[simp]
theorem inputState_work {n : ℕ} (x : BoolVec n) (i : Fin (n - 3)) :
    inputState x (workIndex i) = false :=
  rfl

/-- The three-bit instruction implementing NOT on the sole data bit. -/
def notInstruction : ThreeBitInstruction (UniversalIndex 1) :=
  ThreeBitInstruction.ofDistinct (enableIndex 0) (enableIndex 1) (dataIndex 0)
    (by simp [enableIndex]) (by simp [enableIndex, dataIndex]) (by simp [enableIndex, dataIndex])

/-- The three-bit instruction implementing CNOT on two data bits. -/
def cnotInstruction : ThreeBitInstruction (UniversalIndex 2) :=
  ThreeBitInstruction.ofDistinct (dataIndex 0) (enableIndex 0) (dataIndex 1)
    (by simp [dataIndex, enableIndex]) (by simp [dataIndex]) (by simp [dataIndex, enableIndex])

/-- The canonical three-bit data instruction. -/
def threeInstruction : ThreeBitInstruction (UniversalIndex 3) :=
  ThreeBitInstruction.ofDistinct (dataIndex 0) (dataIndex 1) (dataIndex 2)
    (by simp [dataIndex]) (by simp [dataIndex]) (by simp [dataIndex])

/-- The first prefix instruction computes `x₀ ∧ x₁` into work coordinate zero. -/
def firstPrefix (k : ℕ) : ThreeBitInstruction (UniversalIndex (k + 4)) :=
  ThreeBitInstruction.ofDistinct (dataIndex 0) (dataIndex 1) (workIndex ⟨0, by omega⟩)
    (by simp [dataIndex]) (by simp [dataIndex, workIndex]) (by simp [dataIndex, workIndex])

/-- A later prefix instruction extends the previous conjunction by one data control. -/
def nextPrefix (k : ℕ) (i : Fin k) : ThreeBitInstruction (UniversalIndex (k + 4)) :=
  ThreeBitInstruction.ofDistinct (workIndex i.castSucc) (dataIndex ⟨i + 2, by omega⟩)
    (workIndex i.succ) (by simp [workIndex, dataIndex])
    (by
      simp only [workIndex, ne_eq, Sum.inr.injEq]
      intro h
      have := congrArg Fin.val h
      simp at this)
    (by simp [workIndex, dataIndex])

/-- Prefix instruction number `i`, numbered from zero in execution order. -/
def prefixInstruction (k : ℕ) (i : Fin (k + 1)) :
    ThreeBitInstruction (UniversalIndex (k + 4)) :=
  Fin.cases (firstPrefix k) (nextPrefix k) i

@[simp]
theorem firstPrefix_control₁ (k : ℕ) : (firstPrefix k).control₁ = dataIndex 0 := by
  simp [firstPrefix]

@[simp]
theorem firstPrefix_control₂ (k : ℕ) : (firstPrefix k).control₂ = dataIndex 1 := by
  simp [firstPrefix]

@[simp]
theorem firstPrefix_target (k : ℕ) :
    (firstPrefix k).target = workIndex ⟨0, by omega⟩ := by
  simp [firstPrefix]

@[simp]
theorem nextPrefix_control₁ (k : ℕ) (i : Fin k) :
    (nextPrefix k i).control₁ = workIndex i.castSucc := by
  simp [nextPrefix]

@[simp]
theorem nextPrefix_control₂ (k : ℕ) (i : Fin k) :
    (nextPrefix k i).control₂ = dataIndex ⟨i + 2, by omega⟩ := by
  simp [nextPrefix]

@[simp]
theorem nextPrefix_target (k : ℕ) (i : Fin k) :
    (nextPrefix k i).target = workIndex i.succ := by
  simp [nextPrefix]

@[simp]
theorem prefixInstruction_target (k : ℕ) (i : Fin (k + 1)) :
    (prefixInstruction k i).target = workIndex i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [prefixInstruction, Fin.cases_zero, firstPrefix_target]
    congr
  · simp [prefixInstruction]

/-- The proposition represented by work coordinate `i`: all data coordinates through `i + 1`
are true. -/
def PrefixTrue (k : ℕ) (x : BoolVec (k + 4)) (i : Fin (k + 1)) : Prop :=
  ∀ j : Fin (i.val + 2), x ⟨j, by omega⟩ = true

instance prefixTrueDecidable (k : ℕ) (x : BoolVec (k + 4)) (i : Fin (k + 1)) :
    Decidable (PrefixTrue k x i) := by
  unfold PrefixTrue
  infer_instance

@[simp]
theorem prefixTrue_zero_iff (k : ℕ) (x : BoolVec (k + 4)) :
    PrefixTrue k x 0 ↔ x 0 = true ∧ x 1 = true := by
  simp [PrefixTrue, Fin.forall_fin_two]

theorem prefixTrue_succ_iff (k : ℕ) (x : BoolVec (k + 4)) (i : Fin k) :
    PrefixTrue k x i.succ ↔
      PrefixTrue k x i.castSucc ∧ x ⟨i + 2, by omega⟩ = true := by
  constructor
  · intro h
    constructor
    · intro j
      simpa [PrefixTrue] using h j.castSucc
    · simpa [PrefixTrue] using h (Fin.last (i + 2))
  · rintro ⟨hprefix, hlast⟩ j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simpa [PrefixTrue] using hlast
    · simpa [PrefixTrue] using hprefix l

/-- The target instruction after all `k + 1` prefix work bits have been computed. -/
def targetInstruction (k : ℕ) : ThreeBitInstruction (UniversalIndex (k + 4)) :=
  ThreeBitInstruction.ofDistinct (workIndex (Fin.last k)) (dataIndex ⟨k + 2, by omega⟩)
    (dataIndex (Fin.last (k + 3))) (by simp [workIndex, dataIndex])
    (by simp [workIndex, dataIndex])
    (by
      simp only [dataIndex, ne_eq, Sum.inl.injEq]
      intro h
      have := congrArg Fin.val h
      simp at this)

/-- The forward prefix-conjunction ladder. -/
def computeWord (k : ℕ) : List (ThreeBitInstruction (UniversalIndex (k + 4))) :=
  List.ofFn (prefixInstruction k)

/-- The first `r` instructions of the forward ladder. -/
def computePrefix (k r : ℕ) (hr : r ≤ k + 1) :
    List (ThreeBitInstruction (UniversalIndex (k + 4))) :=
  List.ofFn fun i : Fin r => prefixInstruction k ⟨i, i.isLt.trans_le hr⟩

@[simp]
theorem computePrefix_zero (k : ℕ) (h : 0 ≤ k + 1) : computePrefix k 0 h = [] :=
  rfl

theorem computePrefix_succ (k r : ℕ) (hr : r + 1 ≤ k + 1) :
    computePrefix k (r + 1) hr =
      computePrefix k r (Nat.le_trans (Nat.le_succ r) hr) ++
        [prefixInstruction k ⟨r, by omega⟩] := by
  unfold computePrefix
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  apply congrArg₂ (fun first last => first ++ last)
  · rw [List.ofFn_inj]
    funext i
    congr 1
  · congr 2

/-- State invariant after the first `r` prefix instructions. -/
structure PrefixInvariant (k r : ℕ) (x : BoolVec (k + 4))
    (state : BoolWord (UniversalIndex (k + 4))) : Prop where
  /-- Prefix computation never targets a data coordinate. -/
  data_eq : ∀ i, state (dataIndex i) = x i
  /-- Prefix computation never targets an enable coordinate. -/
  enable_eq : ∀ i, state (enableIndex i) = true
  /-- Every completed work coordinate contains its intended prefix conjunction. -/
  computed_eq : ∀ i, i.val < r → state (workIndex i) = decide (PrefixTrue k x i)
  /-- Every not-yet-computed work coordinate is still clean. -/
  fresh_eq : ∀ i, r ≤ i.val → state (workIndex i) = false

theorem prefixInstruction_apply_target_of_invariant (k : ℕ) (x : BoolVec (k + 4))
    (state : BoolWord (UniversalIndex (k + 4))) (i : Fin (k + 1))
    (h : PrefixInvariant k i.val x state) :
    (prefixInstruction k i).perm state (workIndex i) = decide (PrefixTrue k x i) := by
  cases i using Fin.cases with
  | zero =>
      rw [← prefixInstruction_target]
      rw [ThreeBitInstruction.perm_apply_target]
      simp only [prefixInstruction, Fin.cases_zero, firstPrefix_control₁,
        firstPrefix_control₂, firstPrefix_target]
      rw [h.data_eq, h.data_eq]
      have hwork : state (workIndex ⟨0, by omega⟩) = false :=
        h.fresh_eq ⟨0, by omega⟩ (Nat.le_refl 0)
      rw [hwork]
      by_cases hzero : x 0 = true <;> by_cases hone : x 1 = true <;>
        simp [prefixTrue_zero_iff, hzero, hone]
  | succ i =>
      rw [← prefixInstruction_target]
      rw [ThreeBitInstruction.perm_apply_target]
      simp only [prefixInstruction, Fin.cases_succ, nextPrefix_control₁,
        nextPrefix_control₂, nextPrefix_target]
      rw [h.computed_eq i.castSucc (by simp), h.data_eq]
      have hwork : state (workIndex i.succ) = false :=
        h.fresh_eq i.succ (Nat.le_refl (i.val + 1))
      rw [hwork]
      by_cases hprefix : PrefixTrue k x i.castSucc <;>
        by_cases hnext : x ⟨i + 2, by omega⟩ = true <;>
          simp [prefixTrue_succ_iff, hprefix, hnext]

theorem prefixInvariant_step (k r : ℕ) (hr : r < k + 1) (x : BoolVec (k + 4))
    (state : BoolWord (UniversalIndex (k + 4))) (h : PrefixInvariant k r x state) :
    PrefixInvariant k (r + 1) x
      ((prefixInstruction k ⟨r, hr⟩).perm state) := by
  let current : Fin (k + 1) := ⟨r, hr⟩
  constructor
  · intro i
    rw [(prefixInstruction k current).perm_apply_of_ne_target]
    · exact h.data_eq i
    · rw [prefixInstruction_target]
      simp [dataIndex, workIndex]
  · intro i
    rw [(prefixInstruction k current).perm_apply_of_ne_target]
    · exact h.enable_eq i
    · rw [prefixInstruction_target]
      simp [enableIndex, workIndex]
  · intro i hi
    by_cases hold : i.val < r
    · rw [(prefixInstruction k current).perm_apply_of_ne_target]
      · exact h.computed_eq i hold
      · rw [prefixInstruction_target]
        intro heq
        have := congrArg Fin.val (show i = current from by
          simpa [workIndex] using heq)
        simp [current] at this
        omega
    · have hval : i.val = r := by omega
      have hieq : i = current := Fin.ext hval
      subst i
      exact prefixInstruction_apply_target_of_invariant k x state current (by
        simpa [current] using h)
  · intro i hi
    rw [(prefixInstruction k current).perm_apply_of_ne_target]
    · exact h.fresh_eq i (by omega)
    · rw [prefixInstruction_target]
      intro heq
      have := congrArg Fin.val (show i = current from by
        simpa [workIndex] using heq)
      simp [current] at this
      omega

theorem eval_computePrefix_invariant (k r : ℕ) (hr : r ≤ k + 1)
    (x : BoolVec (k + 4)) :
    PrefixInvariant k r x (ThreeBitCircuit.eval (computePrefix k r hr) (inputState x)) := by
  induction r with
  | zero =>
      constructor
      · intro i
        rfl
      · intro i
        rfl
      · intro i hi
        omega
      · intro i hi
        rfl
  | succ r ih =>
      rw [computePrefix_succ, ThreeBitCircuit.eval_append]
      change PrefixInvariant k (r + 1) x
        ((prefixInstruction k ⟨r, by omega⟩).perm
          (ThreeBitCircuit.eval
            (computePrefix k r (Nat.le_trans (Nat.le_succ r) hr)) (inputState x)))
      exact prefixInvariant_step k r (by omega) x _
        (ih (Nat.le_trans (Nat.le_succ r) hr))

theorem computeWord_eq_computePrefix (k : ℕ) :
    computeWord k = computePrefix k (k + 1) (Nat.le_refl _) := by
  unfold computeWord computePrefix
  rw [List.ofFn_inj]

theorem eval_computeWord_invariant (k : ℕ) (x : BoolVec (k + 4)) :
    PrefixInvariant k (k + 1) x (ThreeBitCircuit.eval (computeWord k) (inputState x)) := by
  rw [computeWord_eq_computePrefix]
  exact eval_computePrefix_invariant k (k + 1) (Nat.le_refl _) x

/-- A placed instruction commutes with a NOT on a coordinate that is neither a control nor its
target. -/
theorem instruction_perm_flipAt (g : ThreeBitInstruction (UniversalIndex (k + 4)))
    (target : UniversalIndex (k + 4)) (ht : target ≠ g.target)
    (hc₁ : target ≠ g.control₁) (hc₂ : target ≠ g.control₂)
    (state : BoolWord (UniversalIndex (k + 4))) :
    g.perm (state.flipAt target) = (g.perm state).flipAt target := by
  funext i
  by_cases hit : i = g.target
  · subst i
    rw [g.perm_apply_target, BoolWord.flipAt_apply_of_ne _ (Ne.symm ht)]
    rw [BoolWord.flipAt_apply_of_ne _ (Ne.symm hc₁),
      BoolWord.flipAt_apply_of_ne _ (Ne.symm hc₂)]
    rw [BoolWord.flipAt_apply_of_ne _ (Ne.symm ht), g.perm_apply_target]
  · rw [g.perm_apply_of_ne_target _ hit]
    by_cases hi : i = target
    · subst i
      rw [BoolWord.flipAt_apply_self, BoolWord.flipAt_apply_self]
      rw [g.perm_apply_of_ne_target _ ht]
    · rw [BoolWord.flipAt_apply_of_ne _ hi, BoolWord.flipAt_apply_of_ne _ hi]
      exact (g.perm_apply_of_ne_target state hit).symm

/-- A circuit word commutes with a NOT coordinate avoided by every instruction. -/
theorem eval_flipAt_of_avoids (instructions : List (ThreeBitInstruction (UniversalIndex (k + 4))))
    (target : UniversalIndex (k + 4))
    (havoid : ∀ g ∈ instructions,
      target ≠ g.target ∧ target ≠ g.control₁ ∧ target ≠ g.control₂)
    (state : BoolWord (UniversalIndex (k + 4))) :
    ThreeBitCircuit.eval instructions (state.flipAt target) =
      (ThreeBitCircuit.eval instructions state).flipAt target := by
  induction instructions generalizing state with
  | nil => rfl
  | cons g instructions ih =>
      rw [ThreeBitCircuit.eval_cons_apply]
      obtain ⟨ht, hc₁, hc₂⟩ := havoid g (by simp)
      rw [instruction_perm_flipAt g target ht hc₁ hc₂]
      have htail : ∀ next ∈ instructions,
          target ≠ next.target ∧ target ≠ next.control₁ ∧ target ≠ next.control₂ := by
        intro next hnext
        exact havoid next (by simp [hnext])
      rw [ih htail]
      rfl

theorem prefixInstruction_avoids_final (k : ℕ) (i : Fin (k + 1)) :
    let target := dataIndex (Fin.last (k + 3))
    target ≠ (prefixInstruction k i).target ∧
      target ≠ (prefixInstruction k i).control₁ ∧
      target ≠ (prefixInstruction k i).control₂ := by
  cases i using Fin.cases with
  | zero =>
      simp only [prefixInstruction, Fin.cases_zero, firstPrefix_target, firstPrefix_control₁,
        firstPrefix_control₂]
      constructor
      · simp [dataIndex, workIndex]
      constructor
      · simp only [dataIndex, ne_eq, Sum.inl.injEq]
        intro h
        have := congrArg Fin.val h
        simp at this
      · simp only [dataIndex, ne_eq, Sum.inl.injEq]
        intro h
        have := congrArg Fin.val h
        simp at this
  | succ i =>
      simp only [prefixInstruction, Fin.cases_succ, nextPrefix_target, nextPrefix_control₁,
        nextPrefix_control₂]
      constructor
      · simp [dataIndex, workIndex]
      constructor
      · simp [dataIndex, workIndex]
      · simp only [dataIndex, ne_eq, Sum.inl.injEq]
        intro h
        have := congrArg Fin.val h
        simp at this
        omega

theorem computeWord_avoids_final (k : ℕ) (g : ThreeBitInstruction (UniversalIndex (k + 4)))
    (hg : g ∈ computeWord k) :
    let target := dataIndex (Fin.last (k + 3))
    target ≠ g.target ∧ target ≠ g.control₁ ∧ target ≠ g.control₂ := by
  rw [computeWord, List.mem_ofFn] at hg
  obtain ⟨i, rfl⟩ := hg
  exact prefixInstruction_avoids_final k i

/-- The all-arity clean circuit word.  Arity zero is deliberately the empty identity word. -/
def word : (n : ℕ) → List (ThreeBitInstruction (UniversalIndex n))
  | 0 => []
  | 1 => [notInstruction]
  | 2 => [cnotInstruction]
  | 3 => [threeInstruction]
  | k + 4 => computeWord k ++ targetInstruction k :: (computeWord k).reverse

/-- Ambient permutation evaluated from the explicit left-to-right circuit word. -/
def perm (n : ℕ) : BoolPerm (UniversalIndex n) :=
  ThreeBitCircuit.eval (word n)

end MultiControl

end Synthesis

end Toffoli
