import Toffoli.Smooth.CircleModel

/-!
# Coordinates for recursive circle products

`CirclePower n` is a recursively nested binary product rather than a Pi type.  This file supplies
the missing conversion between a finite family of circle points and that recursive product.  It
also proves the coordinatewise criterion used to construct smooth maps into `CirclePower n`.

The construction and all theorems include the zero-fold product.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- Assemble a finite family of circle points into the right-nested recursive product. -/
def assemble : (n : ℕ) → (Fin n → Circle) → CirclePower n
  | 0, _ => 0
  | n + 1, x => (assemble n (Fin.init x), x (Fin.last n))

@[simp]
theorem coord_assemble (n : ℕ) (x : Fin n → Circle) (i : Fin n) :
    coord n (assemble n x) i = x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [coord, assemble]
      · simpa only [coord, assemble, Fin.lastCases_castSucc, Fin.init] using
          ih (Fin.init x) j

@[simp]
theorem assemble_coord (n : ℕ) (p : CirclePower n) :
    assemble n (coord n p) = p := by
  induction n with
  | zero =>
      exact Subsingleton.elim _ _
  | succ n ih =>
      apply Prod.ext
      · simpa only [assemble, coord, Fin.init, Fin.lastCases_castSucc] using ih p.1
      · simp [assemble, coord]

/-- Coordinate families and recursively nested circle products contain the same data. -/
def coordEquiv (n : ℕ) : CirclePower n ≃ (Fin n → Circle) where
  toFun := coord n
  invFun := assemble n
  left_inv := assemble_coord n
  right_inv := coord_assemble n

@[simp]
theorem coordEquiv_apply (n : ℕ) (p : CirclePower n) : coordEquiv n p = coord n p :=
  rfl

@[simp]
theorem coordEquiv_symm_apply (n : ℕ) (x : Fin n → Circle) :
    (coordEquiv n).symm x = assemble n x :=
  rfl

/-- Two recursive circle products are equal when all their coordinates are equal. -/
theorem ext {n : ℕ} {p q : CirclePower n} (h : ∀ i, coord n p i = coord n q i) : p = q := by
  rw [← assemble_coord n p, ← assemble_coord n q]
  congr 1
  funext i
  exact h i

/-- Every coordinate projection from a recursive circle product is smooth. -/
theorem contMDiff_coord (n : ℕ) (i : Fin n) :
    ContMDiff (circlePowerModel n) ManifoldSpace.circle.modelWithCorners ∞
      (fun p : CirclePower n => coord n p i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [coord, Fin.lastCases_last] using
          (contMDiff_snd :
            ContMDiff (circlePowerModel (n + 1)) ManifoldSpace.circle.modelWithCorners ∞
              (fun p : CirclePower (n + 1) => p.2))
      · simpa only [coord, Fin.lastCases_castSucc] using
          (ih j).comp
            (contMDiff_fst :
              ContMDiff (circlePowerModel (n + 1)) (circlePowerModel n) ∞
                (fun p : CirclePower (n + 1) => p.1))

/-- A map between recursive circle products is smooth when each assembled coordinate is smooth. -/
theorem contMDiff_assemble {m n : ℕ} (f : CirclePower m → Fin n → Circle)
    (hf : ∀ i,
      ContMDiff (circlePowerModel m) ManifoldSpace.circle.modelWithCorners ∞
        (fun p => f p i)) :
    ContMDiff (circlePowerModel m) (circlePowerModel n) ∞
      (fun p => assemble n (f p)) := by
  induction n with
  | zero =>
      simpa only [assemble] using
        (contMDiff_const :
          ContMDiff (circlePowerModel m) (circlePowerModel 0) ∞
            (fun _ : CirclePower m => (0 : CirclePower 0)))
  | succ n ih =>
      simpa only [assemble] using
        ContMDiff.prodMk
          (ih (fun p i => f p i.castSucc) (fun i => hf i.castSucc))
          (hf (Fin.last n))

/-- Coordinatewise smoothness is equivalent to smoothness of a map into a recursive product. -/
theorem contMDiff_iff_coord {m n : ℕ} (f : CirclePower m → CirclePower n) :
    ContMDiff (circlePowerModel m) (circlePowerModel n) ∞ f ↔
      ∀ i,
        ContMDiff (circlePowerModel m) ManifoldSpace.circle.modelWithCorners ∞
          (fun p => coord n (f p) i) := by
  constructor
  · intro hf i
    exact (contMDiff_coord n i).comp hf
  · intro hf
    simpa only [assemble_coord] using
      contMDiff_assemble (fun p => coord n (f p)) hf

end CircleExtension
end Toffoli
