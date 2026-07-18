import Toffoli.Bool.Reindex
import Toffoli.Smooth.CircleCoordinates

/-!
# Reindexing recursive circle products

The recursive representation `CirclePower n` does not expose a Pi-type reindexing operation.
This file reconstructs it from `coord` and `assemble`: an equivalence `e : Fin n ≃ Fin m`
moves old coordinate `i` to new coordinate `e i`.  The resulting map is a smooth
diffeomorphism, including at the empty product, and agrees with `BoolWord.reindex` on embedded
Boolean points.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

/-- Move old coordinate `i` to new coordinate `e i`. -/
def reindex {n m : ℕ} (e : Fin n ≃ Fin m) (p : CirclePower n) : CirclePower m :=
  assemble m fun j => coord n p (e.symm j)

@[simp]
theorem coord_reindex {n m : ℕ} (e : Fin n ≃ Fin m) (p : CirclePower n) (j : Fin m) :
    coord m (reindex e p) j = coord n p (e.symm j) := by
  simp [reindex]

@[simp]
theorem reindex_symm_apply_reindex {n m : ℕ} (e : Fin n ≃ Fin m) (p : CirclePower n) :
    reindex e.symm (reindex e p) = p := by
  apply coord_ext
  intro i
  simp

@[simp]
theorem reindex_apply_reindex_symm {n m : ℕ} (e : Fin n ≃ Fin m) (p : CirclePower m) :
    reindex e (reindex e.symm p) = p := by
  apply coord_ext
  intro j
  simp

/-- Coordinate reindexing is smooth in the recursive product models. -/
theorem contMDiff_reindex {n m : ℕ} (e : Fin n ≃ Fin m) :
    ContMDiff (circlePowerModel n) (circlePowerModel m) ∞ (reindex e) := by
  apply contMDiff_assemble
  intro j
  exact contMDiff_coord n (e.symm j)

/-- Coordinate reindexing packaged as a diffeomorphism, with inverse reindexing by `e.symm`. -/
def reindexDiffeomorph {n m : ℕ} (e : Fin n ≃ Fin m) :
    Diffeomorph (circlePowerModel n) (circlePowerModel m)
      (CirclePower n) (CirclePower m) ∞ where
  toEquiv :=
    { toFun := reindex e
      invFun := reindex e.symm
      left_inv := reindex_symm_apply_reindex e
      right_inv := reindex_apply_reindex_symm e }
  contMDiff_toFun := contMDiff_reindex e
  contMDiff_invFun := contMDiff_reindex e.symm

@[simp]
theorem reindexDiffeomorph_apply {n m : ℕ} (e : Fin n ≃ Fin m) (p : CirclePower n) :
    reindexDiffeomorph e p = reindex e p :=
  rfl

@[simp]
theorem reindexDiffeomorph_symm_apply {n m : ℕ} (e : Fin n ≃ Fin m)
    (p : CirclePower m) :
    (reindexDiffeomorph e).symm p = reindex e.symm p :=
  rfl

/-- Smooth coordinate reindexing and Boolean-word reindexing commute with the embedding. -/
@[simp]
theorem reindex_embed {n m : ℕ} (e : Fin n ≃ Fin m) (x : BoolVec n) :
    reindex e (embed n x) = embed m (BoolWord.reindex e x) := by
  apply coord_ext
  intro j
  simp [BoolWord.reindex]

end CircleExtension
end Toffoli
