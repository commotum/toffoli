import Toffoli.Smooth.Synthesis.Universality

/-!
# Qualified smooth-synthesis boundary checks

These non-public checks pin down the empty- and low-data-arity behavior of the universal smooth
face, global preservation of every auxiliary circle coordinate, exact restriction on the whole
smooth face, and Boolean interpolation.  They state qualified universality with its ambient word,
fixed constants, returned auxiliaries, restriction, and projection all visible.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli.Audit

open Toffoli CircleExtension Synthesis
open CircleExtension.ThreeBitUniversal

/-! ## Empty and low data arities -/

example (p : BoolPermN 0) : flatWord p = [] :=
  flatWord_zero_eq_nil p

example (p : BoolPermN 0) :
    ambient p =
      Diffeomorph.refl (circlePowerModel (0 + auxCount 0))
        (CirclePower (0 + auxCount 0)) ∞ :=
  ambient_zero_eq_refl p

example (p : BoolPermN 0) :
    restricted p = Diffeomorph.refl (circlePowerModel 0) (CirclePower 0) ∞ :=
  restricted_zero_eq_refl p

example (p : BoolPermN 0) :
    ∃ F : Diffeomorph (circlePowerModel 0) (circlePowerModel 0)
        (CirclePower 0) (CirclePower 0) ∞,
      Interpolates F p :=
  exists_zero_extension_noAux p

example {n : ℕ} (h : n ≤ 3) : Fintype.card (UniversalAux n) = 2 :=
  auxiliary_card_eq_two h

example (x : CirclePower 1) : OnUniversalFace 1 (insertUniversal 1 x) :=
  onUniversalFace_insertUniversal 1 x

example (x : CirclePower 1) (enable : Fin 2) :
    coord (1 + auxCount 1) (insertUniversal 1 x) (flatEnableIndex enable) =
      boolPoint true :=
  coord_insertUniversal_enable 1 x enable

/-! ## Global auxiliary preservation -/

example {n : ℕ} (p : BoolPermN n) : PreservesUniversalAux n (ambient p) :=
  ambient_preservesUniversalAux p

example {n : ℕ} (p : BoolPermN n) (x : CirclePower (n + auxCount n))
    (enable : Fin 2) :
    coord (n + auxCount n) (ambient p x) (flatEnableIndex enable) =
      coord (n + auxCount n) x (flatEnableIndex enable) :=
  (ambient_preservesUniversalAux p).1 x enable

example {n : ℕ} (p : BoolPermN n) (x : CirclePower (n + auxCount n))
    (work : Fin (n - 3)) :
    coord (n + auxCount n) (ambient p x) (flatWorkIndex work) =
      coord (n + auxCount n) x (flatWorkIndex work) :=
  (ambient_preservesUniversalAux p).2 x work

/-! ## Exact smooth-face behavior and Boolean interpolation -/

example {n : ℕ} (p : BoolPermN n) (x : CirclePower n) :
    ambient p (insertUniversal n x) = insertUniversal n (restricted p x) :=
  ambient_insert_eq_insert_restricted p x

example (p : BoolPermN 1) (x : CirclePower 1) :
    ambient p (insertUniversal 1 x) = insertUniversal 1 (restricted p x) :=
  ambient_insert_eq_insert_restricted p x

example {n : ℕ} (p : BoolPermN n) (x : BoolVec n) :
    ambient p (insertUniversal n (embed n x)) =
      insertUniversal n (embed n (p x)) :=
  ambient_interpolates_insertedBoolean p x

example {n : ℕ} (p : BoolPermN n) : Interpolates (restricted p) p :=
  restricted_interpolates p

example {n : ℕ} (p : BoolPermN n) (x : BoolVec n) :
    restricted p (embed n x) = embed n (p x) :=
  restricted_interpolates p x

/-! ## Qualified existential theorem -/

example {n : ℕ} (p : BoolPermN n) :
    ∃ word : List (ThreeBitInstruction (Fin (n + auxCount n))),
      ∃ F : Diffeomorph (circlePowerModel (n + auxCount n))
          (circlePowerModel (n + auxCount n))
          (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞,
        F = evalThreeBitWord word ∧
          ∃ hF : PreservesUniversalAux n F,
            Interpolates (restrictUniversal n F hF) p :=
  exists_restricted_extension_from_threeBit p

example {n : ℕ} (p : BoolPermN n) :
    ∃ word : List (ThreeBitInstruction (Fin (n + auxCount n))),
      ∃ A : Diffeomorph (circlePowerModel (n + auxCount n))
          (circlePowerModel (n + auxCount n))
          (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞,
        ∃ hA : PreservesUniversalAux n A,
          ∃ F : Diffeomorph (circlePowerModel n) (circlePowerModel n)
              (CirclePower n) (CirclePower n) ∞,
            A = evalThreeBitWord word ∧
            F = restrictUniversal n A hA ∧
            (∀ x, A (insertUniversal n x) = insertUniversal n (F x)) ∧
            Interpolates F p :=
  exists_qualified_smooth_realization p

end Toffoli.Audit
