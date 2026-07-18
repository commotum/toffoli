import Mathlib.Data.List.OfFn
import Toffoli.Circuit.ThreeBit
import Toffoli.Cube.Basic
import Toffoli.Synthesis.FaceRealization
import Toffoli.Synthesis.Not
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
  Toffoli.Synthesis.notInstruction 0

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

@[simp]
theorem targetInstruction_control₁ (k : ℕ) :
    (targetInstruction k).control₁ = workIndex (Fin.last k) := by
  simp [targetInstruction]

@[simp]
theorem targetInstruction_control₂ (k : ℕ) :
    (targetInstruction k).control₂ = dataIndex ⟨k + 2, by omega⟩ := by
  simp [targetInstruction]

@[simp]
theorem targetInstruction_target (k : ℕ) :
    (targetInstruction k).target = dataIndex (Fin.last (k + 3)) := by
  simp [targetInstruction]

theorem prefixTrue_last_and_iff (k : ℕ) (x : BoolVec (k + 4)) :
    PrefixTrue k x (Fin.last k) ∧ x ⟨k + 2, by omega⟩ = true ↔
      ∀ i : Fin (k + 3), x i.castSucc = true := by
  constructor
  · rintro ⟨hprefix, hlast⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show (Fin.last (k + 2)).castSucc = ⟨k + 2, by omega⟩ by
          apply Fin.ext
          rfl]
      exact hlast
    · rw [show j.castSucc.castSucc = ⟨j, by omega⟩ by
          apply Fin.ext
          rfl]
      exact hprefix j
  · intro h
    constructor
    · intro i
      rw [show (⟨i, by omega⟩ : Fin (k + 4)) = i.castSucc.castSucc by
        apply Fin.ext
        rfl]
      exact h i.castSucc
    · rw [show (⟨k + 2, by omega⟩ : Fin (k + 4)) = (Fin.last (k + 2)).castSucc by
          apply Fin.ext
          rfl]
      exact h (Fin.last (k + 2))

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

theorem targetInstruction_apply_of_invariant (k : ℕ) (x : BoolVec (k + 4))
    (state : BoolWord (UniversalIndex (k + 4)))
    (h : PrefixInvariant k (k + 1) x state) :
    (targetInstruction k).perm state =
      if ∀ i : Fin (k + 3), x i.castSucc = true then
        state.flipAt (dataIndex (Fin.last (k + 3)))
      else state := by
  by_cases hall : ∀ i : Fin (k + 3), x i.castSucc = true
  · rw [if_pos hall]
    have hparts := (prefixTrue_last_and_iff k x).2 hall
    funext i
    by_cases hi : i = dataIndex (Fin.last (k + 3))
    · subst i
      rw [show dataIndex (Fin.last (k + 3)) = (targetInstruction k).target by simp]
      rw [(targetInstruction k).perm_apply_target]
      simp only [targetInstruction_control₁, targetInstruction_control₂]
      rw [h.computed_eq (Fin.last k) (by simp), h.data_eq]
      simp [hparts.1, hparts.2, targetInstruction_target]
    · rw [(targetInstruction k).perm_apply_of_ne_target]
      · exact (BoolWord.flipAt_apply_of_ne state hi).symm
      · simpa using hi
  · rw [if_neg hall]
    have hparts : ¬(PrefixTrue k x (Fin.last k) ∧ x ⟨k + 2, by omega⟩ = true) :=
      fun hp => hall ((prefixTrue_last_and_iff k x).1 hp)
    funext i
    by_cases hi : i = dataIndex (Fin.last (k + 3))
    · subst i
      rw [show dataIndex (Fin.last (k + 3)) = (targetInstruction k).target by simp]
      rw [(targetInstruction k).perm_apply_target]
      simp only [targetInstruction_control₁, targetInstruction_control₂]
      rw [h.computed_eq (Fin.last k) (by simp), h.data_eq]
      simp [hparts, targetInstruction_target]
    · exact (targetInstruction k).perm_apply_of_ne_target state (by simpa using hi)

@[simp]
theorem inputState_flipAt_data {n : ℕ} (x : BoolVec n) (target : Fin n) :
    (inputState x).flipAt (dataIndex target) = inputState (x.flipAt target) := by
  funext i
  cases i with
  | inl j =>
      simp only [inputState, dataIndex, BoolWord.flipAt, Sum.update_inl_apply_inl,
        BoolWord.sumEquiv_symm_apply_inl]
      rw [show BoolWord.sumEquiv.symm (x, universalConstants n) ∘ Sum.inl = x by rfl]
  | inr aux => simp [inputState, dataIndex, BoolWord.flipAt]

theorem thetaSucc_apply_eq_if_flip (m : ℕ) (x : BoolVec (m + 1)) :
    AndNand.thetaSucc m x =
      if ∀ i : Fin m, x i.castSucc = true then x.flipAt (Fin.last m) else x := by
  by_cases h : ∀ i : Fin m, x i.castSucc = true
  · rw [if_pos h]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [AndNand.thetaSucc_apply_target]
      simp [h]
    · rw [AndNand.thetaSucc_apply_control]
      exact (BoolWord.flipAt_apply_of_ne x (Fin.castSucc_ne_last j)).symm
  · rw [if_neg h]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [AndNand.thetaSucc_apply_target]
      simp [h]
    · rw [AndNand.thetaSucc_apply_control]

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

theorem eval_word_one_apply (x : BoolVec 1) :
    ThreeBitCircuit.eval (word 1) (inputState x) =
      inputState (AndNand.thetaSucc 0 x) := by
  rw [show word 1 = [notInstruction] by rfl, ThreeBitCircuit.eval_singleton]
  rw [show notInstruction = Toffoli.Synthesis.notInstruction 0 by rfl]
  simp only [inputState]
  rw [Toffoli.Synthesis.notInstruction_apply]
  rw [thetaSucc_apply_eq_if_flip]
  simp

theorem eval_word_two_apply (x : BoolVec 2) :
    ThreeBitCircuit.eval (word 2) (inputState x) =
      inputState (AndNand.thetaSucc 1 x) := by
  rw [show word 2 = [cnotInstruction] by rfl, ThreeBitCircuit.eval_singleton]
  funext i
  cases i with
  | inl j =>
      refine Fin.cases ?_ (fun j => ?_) j
      · change cnotInstruction.perm (inputState x) (dataIndex 0) = _
        rw [show dataIndex (0 : Fin 2) = cnotInstruction.control₁ by
          simp [cnotInstruction, dataIndex]]
        rw [cnotInstruction.perm_apply_control₁]
        change x 0 = AndNand.thetaSucc 1 x 0
        exact (AndNand.thetaSucc_apply_control 1 x 0).symm
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change cnotInstruction.perm (inputState x) (dataIndex 1) = _
        rw [show dataIndex (1 : Fin 2) = cnotInstruction.target by
          simp [cnotInstruction, dataIndex]]
        rw [cnotInstruction.perm_apply_target]
        simp only [cnotInstruction, ThreeBitInstruction.ofDistinct_control₁,
          ThreeBitInstruction.ofDistinct_control₂, ThreeBitInstruction.ofDistinct_target,
          inputState_data, inputState_enable, and_true]
        change (if x 0 = true then !x 1 else x 1) = AndNand.thetaSucc 1 x (Fin.last 1)
        rw [AndNand.thetaSucc_apply_target]
        simp [Fin.forall_fin_one]
  | inr aux =>
      rw [cnotInstruction.perm_apply_of_ne_target]
      · rfl
      · simp [cnotInstruction, dataIndex]

theorem eval_word_three_apply (x : BoolVec 3) :
    ThreeBitCircuit.eval (word 3) (inputState x) =
      inputState (AndNand.thetaSucc 2 x) := by
  rw [show word 3 = [threeInstruction] by rfl, ThreeBitCircuit.eval_singleton]
  funext i
  cases i with
  | inl j =>
      by_cases hj : j = Fin.last 2
      · subst j
        change threeInstruction.perm (inputState x) (dataIndex (Fin.last 2)) = _
        rw [show dataIndex (Fin.last 2) = threeInstruction.target by
          simp [threeInstruction, dataIndex]]
        rw [threeInstruction.perm_apply_target]
        simp only [threeInstruction, ThreeBitInstruction.ofDistinct_control₁,
          ThreeBitInstruction.ofDistinct_control₂, ThreeBitInstruction.ofDistinct_target,
          inputState_data]
        change (if x 0 = true ∧ x 1 = true then !x 2 else x 2) =
          AndNand.thetaSucc 2 x (Fin.last 2)
        rw [AndNand.thetaSucc_apply_target]
        simp [Fin.forall_fin_two]
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        rw [threeInstruction.perm_apply_of_ne_target]
        · change x j.castSucc = AndNand.thetaSucc 2 x j.castSucc
          exact (AndNand.thetaSucc_apply_control 2 x j).symm
        · simp only [threeInstruction, ThreeBitInstruction.ofDistinct_target, dataIndex,
            ne_eq, Sum.inl.injEq]
          change j.castSucc ≠ Fin.last 2
          exact Fin.castSucc_ne_last j
  | inr aux =>
      rw [threeInstruction.perm_apply_of_ne_target]
      · rfl
      · simp [threeInstruction, dataIndex]

theorem eval_word_add_four_apply (k : ℕ) (x : BoolVec (k + 4)) :
    ThreeBitCircuit.eval (word (k + 4)) (inputState x) =
      inputState (AndNand.thetaSucc (k + 3) x) := by
  rw [show word (k + 4) =
      computeWord k ++ targetInstruction k :: (computeWord k).reverse by rfl]
  rw [ThreeBitCircuit.eval_append]
  change ThreeBitCircuit.eval (computeWord k).reverse
      ((targetInstruction k).perm (ThreeBitCircuit.eval (computeWord k) (inputState x))) = _
  let state := ThreeBitCircuit.eval (computeWord k) (inputState x)
  have hinvariant : PrefixInvariant k (k + 1) x state := eval_computeWord_invariant k x
  have hrestore : ThreeBitCircuit.eval (computeWord k).reverse state = inputState x := by
    rw [ThreeBitCircuit.eval_reverse]
    exact (ThreeBitCircuit.eval (computeWord k)).symm_apply_apply (inputState x)
  have hcommute (z : BoolWord (UniversalIndex (k + 4))) :
      ThreeBitCircuit.eval (computeWord k).reverse
          (z.flipAt (dataIndex (Fin.last (k + 3)))) =
        (ThreeBitCircuit.eval (computeWord k).reverse z).flipAt
          (dataIndex (Fin.last (k + 3))) := by
    apply eval_flipAt_of_avoids
    intro g hg
    exact computeWord_avoids_final k g (by simpa using hg)
  rw [targetInstruction_apply_of_invariant k x state hinvariant]
  rw [thetaSucc_apply_eq_if_flip]
  by_cases hall : ∀ i : Fin (k + 3), x i.castSucc = true
  · rw [if_pos hall, if_pos hall, hcommute, hrestore, inputState_flipAt_data]
  · rw [if_neg hall, if_neg hall, hrestore]

/-- The first nontrivial ladder is exactly the corrected Figure 7 order: compute the first
conjunction, act on the data target, then uncompute the same work bit. -/
theorem figureSeven_word :
    word 4 = [firstPrefix 0, targetInstruction 0, firstPrefix 0] := by
  rfl

/-- Semantic verification of the corrected five-essential-wire Figure 7 construction.  The
uniform circuit carries two additional enable wires, which this three-instruction word leaves
untouched. -/
theorem figureSeven_apply (x : BoolVec 4) :
    ThreeBitCircuit.eval [firstPrefix 0, targetInstruction 0, firstPrefix 0] (inputState x) =
      inputState (AndNand.thetaSucc 3 x) := by
  rw [← figureSeven_word]
  exact eval_word_add_four_apply 0 x

/-- The explicit placed-three-bit word cleanly realizes every positive-arity member of the
paper's AND/NAND family.  The argument `m` is the number of controls, so the data arity is
`m + 1`. -/
theorem word_cleanRealizes (m : ℕ) :
    CleanRealizes (ThreeBitCircuit.eval (word (m + 1))) (universalConstants (m + 1))
      (AndNand.thetaSucc m) := by
  intro x
  change ThreeBitCircuit.eval (word (m + 1)) (inputState x) =
    inputState (AndNand.thetaSucc m x)
  cases m with
  | zero => exact eval_word_one_apply x
  | succ m =>
      cases m with
      | zero => exact eval_word_two_apply x
      | succ m =>
          cases m with
          | zero => exact eval_word_three_apply x
          | succ k => exact eval_word_add_four_apply k x

theorem perm_cleanRealizes (m : ℕ) :
    CleanRealizes (perm (m + 1)) (universalConstants (m + 1)) (AndNand.thetaSucc m) :=
  word_cleanRealizes m

@[simp]
theorem eval_word_zero :
    ThreeBitCircuit.eval (word 0) = Equiv.refl (BoolWord (UniversalIndex 0)) :=
  rfl

end MultiControl

end Synthesis

end Toffoli
