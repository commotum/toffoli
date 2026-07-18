import Toffoli.Circuit.ThreeBit
import Toffoli.Smooth.CircleCoordinates
import Toffoli.Smooth.CircleGate

/-!
# Smooth circuits of placed three-bit Toffoli gates

A `ThreeBitInstruction (Fin n)` names two controls and a distinct target in an ambient recursive
circle product.  Its smooth interpretation is the canonical `gateDiffeomorph 2` formula on those
three coordinates and the identity on every other coordinate.  Circuit lists are evaluated from
left to right, matching `ThreeBitCircuit.eval` exactly.

This module contains no finite-permutation decomposition or universality proof.  It is the narrow
semantic layer on which the later stable-face synthesis argument can be built.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- The canonical smooth three-bit gate placed at the coordinates named by `instruction`. -/
def threeBitMap {n : ℕ} (instruction : ThreeBitInstruction (Fin n))
    (p : CirclePower n) : CirclePower n :=
  assemble n fun i =>
    if i = instruction.target then
      (coord n p i)⁻¹ * Circle.exp
        (Real.pi *
          (signal (coord n p instruction.control₁) *
            signal (coord n p instruction.control₂)))
    else coord n p i

@[simp]
theorem coord_threeBitMap_target {n : ℕ} (instruction : ThreeBitInstruction (Fin n))
    (p : CirclePower n) :
    coord n (threeBitMap instruction p) instruction.target =
      (coord n p instruction.target)⁻¹ * Circle.exp
        (Real.pi *
          (signal (coord n p instruction.control₁) *
            signal (coord n p instruction.control₂))) := by
  simp [threeBitMap]

@[simp]
theorem coord_threeBitMap_of_ne {n : ℕ} (instruction : ThreeBitInstruction (Fin n))
    (p : CirclePower n) {i : Fin n} (hi : i ≠ instruction.target) :
    coord n (threeBitMap instruction p) i = coord n p i := by
  simp [threeBitMap, hi]

theorem threeBitMap_involutive {n : ℕ} (instruction : ThreeBitInstruction (Fin n)) :
    Function.Involutive (threeBitMap instruction) := by
  intro p
  apply coord_ext
  intro i
  by_cases hi : i = instruction.target
  · subst i
    rw [coord_threeBitMap_target, coord_threeBitMap_target]
    rw [coord_threeBitMap_of_ne _ _ instruction.control₁_ne_target,
      coord_threeBitMap_of_ne _ _ instruction.control₂_ne_target]
    simp [mul_inv_rev, mul_assoc]
  · rw [coord_threeBitMap_of_ne _ _ hi, coord_threeBitMap_of_ne _ _ hi]

/-- A placed three-bit gate is smooth on the full ambient recursive product. -/
theorem contMDiff_threeBitMap {n : ℕ} (instruction : ThreeBitInstruction (Fin n)) :
    ContMDiff (circlePowerModel n) (circlePowerModel n) ∞ (threeBitMap instruction) := by
  unfold threeBitMap
  apply contMDiff_assemble
  intro i
  by_cases hi : i = instruction.target
  · subst i
    simp only [if_pos]
    apply (contMDiff_coord n instruction.target).inv.mul
    apply contMDiff_circleExp.comp
    apply contMDiff_const.mul
    exact
      (contMDiff_signal.comp (contMDiff_coord n instruction.control₁)).mul
        (contMDiff_signal.comp (contMDiff_coord n instruction.control₂))
  · simp only [hi]
    exact contMDiff_coord n i

/-- The placed smooth gate packaged as a self-inverse diffeomorphism. -/
def threeBitDiffeomorph {n : ℕ} (instruction : ThreeBitInstruction (Fin n)) :
    Diffeomorph (circlePowerModel n) (circlePowerModel n)
      (CirclePower n) (CirclePower n) ∞ where
  toEquiv :=
    { toFun := threeBitMap instruction
      invFun := threeBitMap instruction
      left_inv := threeBitMap_involutive instruction
      right_inv := threeBitMap_involutive instruction }
  contMDiff_toFun := contMDiff_threeBitMap instruction
  contMDiff_invFun := contMDiff_threeBitMap instruction

@[simp]
theorem threeBitDiffeomorph_apply {n : ℕ} (instruction : ThreeBitInstruction (Fin n))
    (p : CirclePower n) :
    threeBitDiffeomorph instruction p = threeBitMap instruction p :=
  rfl

@[simp]
theorem threeBitDiffeomorph_symm_apply {n : ℕ}
    (instruction : ThreeBitInstruction (Fin n)) (p : CirclePower n) :
    (threeBitDiffeomorph instruction).symm p = threeBitMap instruction p :=
  rfl

/-- A placed smooth instruction agrees exactly with its placed Boolean instruction on embedded
Boolean words. -/
theorem threeBitDiffeomorph_interpolates {n : ℕ}
    (instruction : ThreeBitInstruction (Fin n)) (x : BoolVec n) :
    threeBitDiffeomorph instruction (embed n x) = embed n (instruction.perm x) := by
  apply coord_ext
  intro i
  by_cases hi : i = instruction.target
  · subst i
    rw [threeBitDiffeomorph_apply, coord_threeBitMap_target]
    simp only [coord_embed]
    rw [ThreeBitInstruction.perm_apply_target]
    cases hc₁ : x instruction.control₁ <;>
      cases hc₂ : x instruction.control₂ <;>
        cases ht : x instruction.target <;>
          norm_num [hc₁, hc₂, ht, signal, boolPoint]
  · rw [threeBitDiffeomorph_apply, coord_threeBitMap_of_ne _ _ hi, coord_embed, coord_embed]
    rw [ThreeBitInstruction.perm_apply_of_ne_target _ _ hi]

/-- Evaluate a word of placed smooth gates from left to right. -/
def evalThreeBitWord {n : ℕ} : List (ThreeBitInstruction (Fin n)) →
    Diffeomorph (circlePowerModel n) (circlePowerModel n)
      (CirclePower n) (CirclePower n) ∞
  | [] => Diffeomorph.refl (circlePowerModel n) (CirclePower n) ∞
  | instruction :: word =>
      (threeBitDiffeomorph instruction).trans (evalThreeBitWord word)

@[simp]
theorem evalThreeBitWord_nil {n : ℕ} :
    evalThreeBitWord ([] : List (ThreeBitInstruction (Fin n))) =
      Diffeomorph.refl (circlePowerModel n) (CirclePower n) ∞ :=
  rfl

@[simp]
theorem evalThreeBitWord_cons {n : ℕ} (instruction : ThreeBitInstruction (Fin n))
    (word : List (ThreeBitInstruction (Fin n))) :
    evalThreeBitWord (instruction :: word) =
      (threeBitDiffeomorph instruction).trans (evalThreeBitWord word) :=
  rfl

/-- Appending smooth words is serial composition in execution order. -/
theorem evalThreeBitWord_append {n : ℕ} (first second : List (ThreeBitInstruction (Fin n))) :
    evalThreeBitWord (first ++ second) =
      (evalThreeBitWord first).trans (evalThreeBitWord second) := by
  induction first with
  | nil => simp
  | cons instruction first ih =>
      simp only [List.cons_append, evalThreeBitWord_cons, ih]
      apply Diffeomorph.ext
      intro p
      rfl

/-- Smooth word evaluation agrees exactly with Boolean placed-circuit evaluation at every
embedded Boolean point. -/
theorem evalThreeBitWord_interpolates {n : ℕ}
    (word : List (ThreeBitInstruction (Fin n))) (x : BoolVec n) :
    evalThreeBitWord word (embed n x) = embed n (ThreeBitCircuit.eval word x) := by
  induction word generalizing x with
  | nil => rfl
  | cons instruction word ih =>
      change
        evalThreeBitWord word
            (threeBitDiffeomorph instruction (embed n x)) =
          embed n (ThreeBitCircuit.eval word (instruction.perm x))
      rw [threeBitDiffeomorph_interpolates, ih]

end CircleExtension
end Toffoli
