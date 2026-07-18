import Mathlib.Geometry.Manifold.Diffeomorph
import Toffoli.Smooth.CircleCoordinates
import Toffoli.Smooth.UniversalLayout

/-!
# The smooth universal auxiliary face

The discrete universality construction uses a data block followed by two `true` enable bits and
`n - 3` clean `false` work bits.  This file embeds the corresponding smooth face into the flat
circle product, projects it back to the data block, and gives a generic restriction constructor
for ambient diffeomorphisms preserving that face.

This leaf does not import circuits, atomic decompositions, or synthesis proofs.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension

open Synthesis

/-- Insert a recursive circle product into the universal flat ambient product, fixing enable
coordinates at Boolean `true` and work coordinates at Boolean `false`. -/
def insertUniversal (n : ℕ) (p : CirclePower n) : CirclePower (n + auxCount n) :=
  assemble (n + auxCount n) fun j =>
    match (universalIndexFinEquiv n).symm j with
    | Sum.inl i => coord n p i
    | Sum.inr (Sum.inl _) => boolPoint true
    | Sum.inr (Sum.inr _) => boolPoint false

/-- Project the flat universal ambient product onto its initial data block. -/
def projectUniversal (n : ℕ) (p : CirclePower (n + auxCount n)) : CirclePower n :=
  assemble n fun i => coord (n + auxCount n) p (flatDataIndex i)

@[simp]
theorem coord_insertUniversal_data (n : ℕ) (p : CirclePower n) (i : Fin n) :
    coord (n + auxCount n) (insertUniversal n p) (flatDataIndex i) = coord n p i := by
  simp [insertUniversal, flatDataIndex, universalIndexFinEquiv]

@[simp]
theorem coord_insertUniversal_enable (n : ℕ) (p : CirclePower n) (i : Fin 2) :
    coord (n + auxCount n) (insertUniversal n p) (flatEnableIndex i) = boolPoint true := by
  simp [insertUniversal, flatEnableIndex, universalIndexFinEquiv]

@[simp]
theorem coord_insertUniversal_work (n : ℕ) (p : CirclePower n) (i : Fin (n - 3)) :
    coord (n + auxCount n) (insertUniversal n p) (flatWorkIndex i) = boolPoint false := by
  simp [insertUniversal, flatWorkIndex, universalIndexFinEquiv]

@[simp]
theorem coord_projectUniversal (n : ℕ) (p : CirclePower (n + auxCount n)) (i : Fin n) :
    coord n (projectUniversal n p) i = coord (n + auxCount n) p (flatDataIndex i) := by
  simp [projectUniversal]

theorem contMDiff_insertUniversal (n : ℕ) :
    ContMDiff (circlePowerModel n) (circlePowerModel (n + auxCount n)) ∞
      (insertUniversal n) := by
  unfold insertUniversal
  apply contMDiff_assemble
  intro j
  generalize hindex : (universalIndexFinEquiv n).symm j = index
  rcases index with i | i
  · simpa only [hindex] using contMDiff_coord n i
  · rcases i with i | i <;> simp only [hindex] <;> exact contMDiff_const

theorem contMDiff_projectUniversal (n : ℕ) :
    ContMDiff (circlePowerModel (n + auxCount n)) (circlePowerModel n) ∞
      (projectUniversal n) := by
  unfold projectUniversal
  apply contMDiff_assemble
  intro i
  exact contMDiff_coord (n + auxCount n) (flatDataIndex i)

@[simp]
theorem projectUniversal_insertUniversal (n : ℕ) (p : CirclePower n) :
    projectUniversal n (insertUniversal n p) = p := by
  apply coord_ext
  intro i
  simp

theorem insertUniversal_injective (n : ℕ) : Function.Injective (insertUniversal n) :=
  Function.LeftInverse.injective (projectUniversal_insertUniversal n)

/-- The universal data-and-constant Boolean word embeds into exactly the smooth universal face. -/
theorem insertUniversal_embed (n : ℕ) (x : BoolVec n) :
    insertUniversal n (embed n x) = embed (n + auxCount n) (flatUniversalInput x) := by
  apply coord_ext
  intro j
  rw [← (universalIndexFinEquiv n).apply_symm_apply j]
  generalize hindex : (universalIndexFinEquiv n).symm j = index
  rcases index with i | i
  · simp
  · rcases i with i | i <;> simp

/-- Points of the universal face have the two enables fixed at Boolean `true` and every work
coordinate fixed at Boolean `false`. -/
def OnUniversalFace (n : ℕ) (p : CirclePower (n + auxCount n)) : Prop :=
  (∀ i : Fin 2,
      coord (n + auxCount n) p (flatEnableIndex i) = boolPoint true) ∧
    (∀ i : Fin (n - 3),
      coord (n + auxCount n) p (flatWorkIndex i) = boolPoint false)

@[simp]
theorem onUniversalFace_insertUniversal (n : ℕ) (p : CirclePower n) :
    OnUniversalFace n (insertUniversal n p) := by
  constructor <;> intro i <;> simp

/-- Reconstructing from the data projection is exact precisely on the fixed auxiliary face. -/
theorem insertUniversal_projectUniversal_iff (n : ℕ)
    (p : CirclePower (n + auxCount n)) :
    insertUniversal n (projectUniversal n p) = p ↔ OnUniversalFace n p := by
  constructor
  · intro hp
    constructor
    · intro i
      rw [← hp]
      simp
    · intro i
      rw [← hp]
      simp
  · rintro ⟨henable, hwork⟩
    apply coord_ext
    intro j
    rw [← (universalIndexFinEquiv n).apply_symm_apply j]
    generalize hindex : (universalIndexFinEquiv n).symm j = index
    rcases index with i | i
    · simp
    · rcases i with i | i
      · simpa using henable i
      · simpa using hwork i

theorem insertUniversal_projectUniversal_of_face (n : ℕ)
    {p : CirclePower (n + auxCount n)} (hp : OnUniversalFace n p) :
    insertUniversal n (projectUniversal n p) = p :=
  (insertUniversal_projectUniversal_iff n p).2 hp

/-- An ambient map sends the universal face into itself. -/
def MapsUniversalFace (n : ℕ)
    (F : CirclePower (n + auxCount n) → CirclePower (n + auxCount n)) : Prop :=
  ∀ p, OnUniversalFace n p → OnUniversalFace n (F p)

/-- Restrict an ambient diffeomorphism to the data block when both it and its inverse preserve the
universal auxiliary face. -/
def restrictUniversalOfMapsFace (n : ℕ)
    (F : Diffeomorph (circlePowerModel (n + auxCount n))
      (circlePowerModel (n + auxCount n))
      (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞)
    (hforward : MapsUniversalFace n F)
    (hinverse : MapsUniversalFace n F.symm) :
    Diffeomorph (circlePowerModel n) (circlePowerModel n) (CirclePower n) (CirclePower n) ∞ where
  toEquiv :=
    { toFun := fun p => projectUniversal n (F (insertUniversal n p))
      invFun := fun p => projectUniversal n (F.symm (insertUniversal n p))
      left_inv := by
        intro p
        have hface : OnUniversalFace n (F (insertUniversal n p)) :=
          hforward _ (onUniversalFace_insertUniversal n p)
        rw [insertUniversal_projectUniversal_of_face n hface]
        simp
      right_inv := by
        intro p
        have hface : OnUniversalFace n (F.symm (insertUniversal n p)) :=
          hinverse _ (onUniversalFace_insertUniversal n p)
        rw [insertUniversal_projectUniversal_of_face n hface]
        simp }
  contMDiff_toFun :=
    (contMDiff_projectUniversal n).comp
      (F.contMDiff.comp (contMDiff_insertUniversal n))
  contMDiff_invFun :=
    (contMDiff_projectUniversal n).comp
      (F.symm.contMDiff.comp (contMDiff_insertUniversal n))

@[simp]
theorem restrictUniversalOfMapsFace_apply (n : ℕ)
    (F : Diffeomorph (circlePowerModel (n + auxCount n))
      (circlePowerModel (n + auxCount n))
      (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞)
    (hforward : MapsUniversalFace n F) (hinverse : MapsUniversalFace n F.symm)
    (p : CirclePower n) :
    restrictUniversalOfMapsFace n F hforward hinverse p =
      projectUniversal n (F (insertUniversal n p)) :=
  rfl

/-- Strong componentwise hypothesis: an ambient diffeomorphism leaves every auxiliary coordinate
unchanged globally. -/
def PreservesUniversalAux (n : ℕ)
    (F : CirclePower (n + auxCount n) → CirclePower (n + auxCount n)) : Prop :=
  (∀ p (i : Fin 2),
      coord (n + auxCount n) (F p) (flatEnableIndex i) =
        coord (n + auxCount n) p (flatEnableIndex i)) ∧
    (∀ p (i : Fin (n - 3)),
      coord (n + auxCount n) (F p) (flatWorkIndex i) =
        coord (n + auxCount n) p (flatWorkIndex i))

theorem PreservesUniversalAux.mapsUniversalFace {n : ℕ}
    {F : CirclePower (n + auxCount n) → CirclePower (n + auxCount n)}
    (hF : PreservesUniversalAux n F) : MapsUniversalFace n F := by
  intro p hp
  constructor
  · intro i
    rw [hF.1 p i]
    exact hp.1 i
  · intro i
    rw [hF.2 p i]
    exact hp.2 i

theorem PreservesUniversalAux.diffeomorph_symm {n : ℕ}
    {F : Diffeomorph (circlePowerModel (n + auxCount n))
      (circlePowerModel (n + auxCount n))
      (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞}
    (hF : PreservesUniversalAux n F) : PreservesUniversalAux n F.symm := by
  constructor
  · intro p i
    have h := hF.1 (F.symm p) i
    rw [F.apply_symm_apply] at h
    exact h.symm
  · intro p i
    have h := hF.2 (F.symm p) i
    rw [F.apply_symm_apply] at h
    exact h.symm

/-- Restrict an ambient diffeomorphism which globally preserves every auxiliary coordinate. -/
def restrictUniversal (n : ℕ)
    (F : Diffeomorph (circlePowerModel (n + auxCount n))
      (circlePowerModel (n + auxCount n))
      (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞)
    (hF : PreservesUniversalAux n F) :
    Diffeomorph (circlePowerModel n) (circlePowerModel n) (CirclePower n) (CirclePower n) ∞ :=
  restrictUniversalOfMapsFace n F hF.mapsUniversalFace
    hF.diffeomorph_symm.mapsUniversalFace

@[simp]
theorem restrictUniversal_apply (n : ℕ)
    (F : Diffeomorph (circlePowerModel (n + auxCount n))
      (circlePowerModel (n + auxCount n))
      (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞)
    (hF : PreservesUniversalAux n F) (p : CirclePower n) :
    restrictUniversal n F hF p = projectUniversal n (F (insertUniversal n p)) :=
  rfl

end CircleExtension
end Toffoli
