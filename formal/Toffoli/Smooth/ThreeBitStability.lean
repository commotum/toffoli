import Toffoli.Circuit.ThreeBitTransport
import Toffoli.Smooth.CircleReindex
import Toffoli.Smooth.ThreeBitCircuit

/-!
# Structural stability of smooth three-bit circuits

This file records coordinatewise facts used to reason about smooth fixed faces independently of
the discrete synthesis compiler.  Replacing a coordinate unused by a placed three-bit gate
commutes with that gate, and the result lifts to words that uniformly avoid the coordinate.

The final section proves smooth equivariance for the shared instruction and word reindexing API.
It imports no decomposition or universality theorem.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-! ## Replacing one circle coordinate -/

/-- Replace coordinate `q` of a recursive circle product by `z`, leaving every other coordinate
unchanged. -/
def replaceCoord {n : ℕ} (p : CirclePower n) (q : Fin n) (z : Circle) : CirclePower n :=
  assemble n fun i => if i = q then z else coord n p i

@[simp]
theorem coord_replaceCoord {n : ℕ} (p : CirclePower n) (q : Fin n) (z : Circle)
    (i : Fin n) :
    coord n (replaceCoord p q z) i = if i = q then z else coord n p i := by
  simp [replaceCoord]

@[simp]
theorem coord_replaceCoord_same {n : ℕ} (p : CirclePower n) (q : Fin n) (z : Circle) :
    coord n (replaceCoord p q z) q = z := by
  simp

@[simp]
theorem coord_replaceCoord_of_ne {n : ℕ} (p : CirclePower n) (q : Fin n) (z : Circle)
    {i : Fin n} (hi : i ≠ q) :
    coord n (replaceCoord p q z) i = coord n p i := by
  simp [hi]

@[simp]
theorem replaceCoord_self {n : ℕ} (p : CirclePower n) (q : Fin n) :
    replaceCoord p q (coord n p q) = p := by
  apply coord_ext
  intro i
  by_cases hi : i = q <;> simp [hi]

@[simp]
theorem replaceCoord_replace {n : ℕ} (p : CirclePower n) (q : Fin n) (z w : Circle) :
    replaceCoord (replaceCoord p q z) q w = replaceCoord p q w := by
  apply coord_ext
  intro i
  by_cases hi : i = q <;> simp [hi]

/-- Replacing a coordinate commutes with transporting coordinate labels. -/
theorem reindex_replaceCoord {n m : ℕ} (e : Fin n ≃ Fin m) (p : CirclePower n)
    (q : Fin n) (z : Circle) :
    reindex e (replaceCoord p q z) = replaceCoord (reindex e p) (e q) z := by
  apply coord_ext
  intro j
  by_cases hj : j = e q
  · subst j
    simp
  · have hold : e.symm j ≠ q := by
      intro h
      apply hj
      rw [← h, e.apply_symm_apply]
    simp [hj, hold]

/-! ## Gate and word stability under replacement -/

/-- One placed smooth gate commutes with replacement of a coordinate that is neither its target
nor either of its controls. -/
theorem threeBitMap_replaceCoord {n : ℕ} (instruction : ThreeBitInstruction (Fin n))
    (p : CirclePower n) (q : Fin n) (z : Circle)
    (ht : q ≠ instruction.target) (hc₁ : q ≠ instruction.control₁)
    (hc₂ : q ≠ instruction.control₂) :
    threeBitMap instruction (replaceCoord p q z) =
      replaceCoord (threeBitMap instruction p) q z := by
  apply coord_ext
  intro i
  by_cases hiq : i = q
  · subst i
    simp [coord_threeBitMap_of_ne, ht]
  · by_cases hit : i = instruction.target
    · subst i
      simp [coord_threeBitMap_target, hiq, hc₁.symm, hc₂.symm]
    · simp [coord_threeBitMap_of_ne, hiq, hit]

/-- A placed gate changes its input only by replacing its target coordinate with the computed
target value. -/
theorem threeBitMap_eq_replaceCoord_target {n : ℕ}
    (instruction : ThreeBitInstruction (Fin n)) (p : CirclePower n) :
    threeBitMap instruction p =
      replaceCoord p instruction.target
        (coord n (threeBitMap instruction p) instruction.target) := by
  apply coord_ext
  intro i
  by_cases hi : i = instruction.target
  · subst i
    simp
  · simp [hi, coord_threeBitMap_of_ne]

/-- Every instruction in `word` avoids `q` as target and as either control. -/
def ThreeBitWordAvoids {n : ℕ} (word : List (ThreeBitInstruction (Fin n)))
    (q : Fin n) : Prop :=
  ∀ instruction ∈ word,
    q ≠ instruction.target ∧ q ≠ instruction.control₁ ∧ q ≠ instruction.control₂

@[simp]
theorem threeBitWordAvoids_nil {n : ℕ} (q : Fin n) :
    ThreeBitWordAvoids ([] : List (ThreeBitInstruction (Fin n))) q := by
  simp [ThreeBitWordAvoids]

@[simp]
theorem threeBitWordAvoids_cons {n : ℕ} (instruction : ThreeBitInstruction (Fin n))
    (word : List (ThreeBitInstruction (Fin n))) (q : Fin n) :
    ThreeBitWordAvoids (instruction :: word) q ↔
      (q ≠ instruction.target ∧ q ≠ instruction.control₁ ∧ q ≠ instruction.control₂) ∧
        ThreeBitWordAvoids word q := by
  simp [ThreeBitWordAvoids]

@[simp]
theorem threeBitWordAvoids_reverse {n : ℕ}
    (word : List (ThreeBitInstruction (Fin n))) (q : Fin n) :
    ThreeBitWordAvoids word.reverse q ↔ ThreeBitWordAvoids word q := by
  simp [ThreeBitWordAvoids]

/-- A smooth word commutes with replacement of a coordinate avoided by every instruction. -/
theorem evalThreeBitWord_replaceCoord {n : ℕ}
    (word : List (ThreeBitInstruction (Fin n))) (p : CirclePower n) (q : Fin n) (z : Circle)
    (h : ThreeBitWordAvoids word q) :
    evalThreeBitWord word (replaceCoord p q z) =
      replaceCoord (evalThreeBitWord word p) q z := by
  induction word generalizing p with
  | nil => rfl
  | cons instruction word ih =>
      rw [threeBitWordAvoids_cons] at h
      rcases h with ⟨⟨ht, hc₁, hc₂⟩, hword⟩
      change
        evalThreeBitWord word (threeBitMap instruction (replaceCoord p q z)) =
          replaceCoord (evalThreeBitWord word (threeBitMap instruction p)) q z
      rw [threeBitMap_replaceCoord instruction p q z ht hc₁ hc₂]
      exact ih (threeBitMap instruction p) hword

/-- A coordinate avoided by every instruction is unchanged by the smooth word. -/
theorem coord_evalThreeBitWord_of_avoids {n : ℕ}
    (word : List (ThreeBitInstruction (Fin n))) (p : CirclePower n) (q : Fin n)
    (h : ThreeBitWordAvoids word q) :
    coord n (evalThreeBitWord word p) q = coord n p q := by
  induction word generalizing p with
  | nil => rfl
  | cons instruction word ih =>
      rw [threeBitWordAvoids_cons] at h
      rcases h with ⟨⟨ht, _hc₁, _hc₂⟩, hword⟩
      change coord n (evalThreeBitWord word (threeBitMap instruction p)) q = coord n p q
      rw [ih (threeBitMap instruction p) hword]
      exact coord_threeBitMap_of_ne instruction p ht

/-! ## Transport along coordinate equivalences -/

@[simp]
theorem threeBitInstruction_reindex_control₁ {n m : ℕ} (e : Fin n ≃ Fin m)
    (instruction : ThreeBitInstruction (Fin n)) :
    (ThreeBitInstruction.reindex e instruction).control₁ = e instruction.control₁ :=
  rfl

@[simp]
theorem threeBitInstruction_reindex_control₂ {n m : ℕ} (e : Fin n ≃ Fin m)
    (instruction : ThreeBitInstruction (Fin n)) :
    (ThreeBitInstruction.reindex e instruction).control₂ = e instruction.control₂ :=
  rfl

@[simp]
theorem threeBitInstruction_reindex_target {n m : ℕ} (e : Fin n ≃ Fin m)
    (instruction : ThreeBitInstruction (Fin n)) :
    (ThreeBitInstruction.reindex e instruction).target = e instruction.target :=
  rfl

/-- Placed smooth gates are equivariant under coordinate reindexing. -/
theorem reindex_threeBitMap {n m : ℕ} (e : Fin n ≃ Fin m)
    (instruction : ThreeBitInstruction (Fin n)) (p : CirclePower n) :
    reindex e (threeBitMap instruction p) =
      threeBitMap (ThreeBitInstruction.reindex e instruction) (reindex e p) := by
  apply coord_ext
  intro j
  by_cases hj : j = e instruction.target
  · subst j
    rw [coord_reindex, Equiv.symm_apply_apply, coord_threeBitMap_target]
    rw [show e instruction.target =
      (ThreeBitInstruction.reindex e instruction).target by rfl]
    rw [coord_threeBitMap_target]
    simp
  · have hold : e.symm j ≠ instruction.target := by
      intro h
      apply hj
      rw [← h, e.apply_symm_apply]
    have hnew : j ≠ (ThreeBitInstruction.reindex e instruction).target := by
      simpa using hj
    rw [coord_reindex, coord_threeBitMap_of_ne instruction _ hold,
      coord_threeBitMap_of_ne _ _ hnew, coord_reindex]

@[simp]
theorem threeBitCircuit_reindex_reverse {n m : ℕ} (e : Fin n ≃ Fin m)
    (word : List (ThreeBitInstruction (Fin n))) :
    ThreeBitCircuit.reindex e word.reverse = (ThreeBitCircuit.reindex e word).reverse := by
  simp [ThreeBitCircuit.reindex]

/-- Smooth evaluation of a transported word is coordinatewise conjugate to evaluation of the
original word. -/
theorem reindex_evalThreeBitWord {n m : ℕ} (e : Fin n ≃ Fin m)
    (word : List (ThreeBitInstruction (Fin n))) (p : CirclePower n) :
    reindex e (evalThreeBitWord word p) =
      evalThreeBitWord (ThreeBitCircuit.reindex e word) (reindex e p) := by
  induction word generalizing p with
  | nil => rfl
  | cons instruction word ih =>
      change
        reindex e (evalThreeBitWord word (threeBitMap instruction p)) =
          evalThreeBitWord (ThreeBitCircuit.reindex e word)
            (threeBitMap (ThreeBitInstruction.reindex e instruction) (reindex e p))
      rw [ih, reindex_threeBitMap]

/-- Diffeomorphism-level conjugation form of `reindex_evalThreeBitWord`. -/
theorem evalThreeBitWord_reindex_eq_conj {n m : ℕ} (e : Fin n ≃ Fin m)
    (word : List (ThreeBitInstruction (Fin n))) :
    evalThreeBitWord (ThreeBitCircuit.reindex e word) =
      (reindexDiffeomorph e).symm.trans
        ((evalThreeBitWord word).trans (reindexDiffeomorph e)) := by
  apply Diffeomorph.ext
  intro p
  change
    evalThreeBitWord (ThreeBitCircuit.reindex e word) p =
      reindex e (evalThreeBitWord word (reindex e.symm p))
  rw [reindex_evalThreeBitWord, reindex_apply_reindex_symm]

/-- Word-wide avoidance is invariant under transporting the coordinate and the word together. -/
theorem threeBitWordAvoids_reindex_iff {n m : ℕ} (e : Fin n ≃ Fin m)
    (word : List (ThreeBitInstruction (Fin n))) (q : Fin n) :
    ThreeBitWordAvoids (ThreeBitCircuit.reindex e word) (e q) ↔
      ThreeBitWordAvoids word q := by
  simp [ThreeBitWordAvoids, ThreeBitCircuit.reindex]

/-! ## Transporting “changes only one coordinate” certificates -/

/-- A circle-product map changes at most coordinate `q`. -/
def ChangesOnlyAt {n : ℕ} (F : CirclePower n → CirclePower n) (q : Fin n) : Prop :=
  ∀ p i, i ≠ q → coord n (F p) i = coord n p i

/-- Exact compute/act/uncompute formula.  If the compute prefix neither reads nor changes `q`
and the middle gate targets `q`, then uncomputation restores every other coordinate and leaves
only the newly computed target value at `q`. -/
theorem evalThreeBitWord_append_cons_reverse_eq_replaceCoord {n : ℕ}
    (prefix : List (ThreeBitInstruction (Fin n)))
    (instruction : ThreeBitInstruction (Fin n)) (p : CirclePower n) (q : Fin n)
    (hprefix : ThreeBitWordAvoids prefix q) (htarget : instruction.target = q) :
    evalThreeBitWord (prefix ++ instruction :: prefix.reverse) p =
      replaceCoord p q
        (coord n (threeBitMap instruction (evalThreeBitWord prefix p)) q) := by
  calc
    evalThreeBitWord (prefix ++ instruction :: prefix.reverse) p =
        evalThreeBitWord prefix.reverse
          (threeBitMap instruction (evalThreeBitWord prefix p)) := by
      rw [evalThreeBitWord_append]
      rfl
    _ = evalThreeBitWord prefix.reverse
          (replaceCoord (evalThreeBitWord prefix p) q
            (coord n (threeBitMap instruction (evalThreeBitWord prefix p)) q)) := by
      congr 1
      simpa [htarget] using
        threeBitMap_eq_replaceCoord_target instruction (evalThreeBitWord prefix p)
    _ = replaceCoord
          (evalThreeBitWord prefix.reverse (evalThreeBitWord prefix p)) q
          (coord n (threeBitMap instruction (evalThreeBitWord prefix p)) q) :=
      evalThreeBitWord_replaceCoord prefix.reverse (evalThreeBitWord prefix p) q _
        ((threeBitWordAvoids_reverse prefix q).2 hprefix)
    _ = replaceCoord p q
          (coord n (threeBitMap instruction (evalThreeBitWord prefix p)) q) := by
      simp

/-- The compute/act/uncompute word in the preceding theorem changes at most its middle target. -/
theorem evalThreeBitWord_append_cons_reverse_changesOnlyAt {n : ℕ}
    (prefix : List (ThreeBitInstruction (Fin n)))
    (instruction : ThreeBitInstruction (Fin n)) (q : Fin n)
    (hprefix : ThreeBitWordAvoids prefix q) (htarget : instruction.target = q) :
    ChangesOnlyAt (evalThreeBitWord (prefix ++ instruction :: prefix.reverse)) q := by
  intro p i hi
  rw [evalThreeBitWord_append_cons_reverse_eq_replaceCoord prefix instruction p q
    hprefix htarget]
  exact coord_replaceCoord_of_ne p q _ hi

/-- If every instruction targets `q`, then the whole word changes at most `q`. -/
theorem evalThreeBitWord_changesOnlyAt {n : ℕ}
    (word : List (ThreeBitInstruction (Fin n))) (q : Fin n)
    (h : ∀ instruction ∈ word, instruction.target = q) :
    ChangesOnlyAt (evalThreeBitWord word) q := by
  intro p i hi
  induction word generalizing p with
  | nil => rfl
  | cons instruction word ih =>
      have htarget : instruction.target = q := h instruction (by simp)
      have hword : ∀ next ∈ word, next.target = q := by
        intro next hnext
        exact h next (by simp [hnext])
      change coord n (evalThreeBitWord word (threeBitMap instruction p)) i = coord n p i
      rw [ih hword (threeBitMap instruction p)]
      exact coord_threeBitMap_of_ne instruction p (by simpa [htarget] using hi)

/-- A changes-only certificate transports along any equivalence of finite coordinate labels. -/
theorem ChangesOnlyAt.reindex {n m : ℕ} {F : CirclePower n → CirclePower n} {q : Fin n}
    (h : ChangesOnlyAt F q) (e : Fin n ≃ Fin m) :
    ChangesOnlyAt (fun p => reindex e (F (reindex e.symm p))) (e q) := by
  intro p j hj
  rw [coord_reindex]
  have hold : e.symm j ≠ q := by
    intro heq
    apply hj
    rw [← heq, e.apply_symm_apply]
  rw [h _ _ hold]
  simp

/-- Consequently, a circuit known to change only `q` still changes only `e q` after transporting
its instructions along `e`. -/
theorem evalThreeBitWord_reindex_changesOnlyAt {n m : ℕ} (e : Fin n ≃ Fin m)
    (word : List (ThreeBitInstruction (Fin n))) (q : Fin n)
    (h : ChangesOnlyAt (evalThreeBitWord word) q) :
    ChangesOnlyAt (evalThreeBitWord (ThreeBitCircuit.reindex e word)) (e q) := by
  rw [evalThreeBitWord_reindex_eq_conj]
  exact h.reindex e

end CircleExtension
end Toffoli
