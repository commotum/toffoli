import Toffoli.Smooth.CircleAtomic
import Toffoli.Smooth.Synthesis.AtomicStability
import Toffoli.Smooth.UniversalFace
import Toffoli.Synthesis.Universality

/-!
# Qualified smooth universality of the three-bit Toffoli gate

This deliberately heavy terminal leaf combines the chosen finite atomic decomposition with the
explicit three-bit synthesis compiler.  The nested discrete word is flattened into consecutive
circle coordinates and interpreted as a composition of placed copies of `gateDiffeomorph 2`.
Its two enable coordinates and all work coordinates are preserved for every circle-valued
ambient input.  Restriction to their fixed Boolean values therefore produces a data
diffeomorphism interpolating the requested Boolean permutation.

This is a qualified result: it uses fixed constants, returned clean auxiliaries, componentwise
restriction, and deletion by projection.  It does not assert ancilla-free three-bit universality.
For arity at least four, the restricted smooth circuit is generally not equal away from the
Boolean cube to the separate direct higher-arity circle formula; only exact Boolean interpolation
is asserted.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Toffoli
namespace CircleExtension
namespace ThreeBitUniversal

open Synthesis

/-- The chosen nested-index word from discrete three-bit universality. -/
noncomputable def nestedWord {n : ℕ} (p : BoolPermN n) :
    List (ThreeBitInstruction (UniversalIndex n)) :=
  Synthesis.ThreeBitUniversal.word p

/-- The chosen word transported to the consecutive coordinates of the recursive circle product. -/
noncomputable def flatWord {n : ℕ} (p : BoolPermN n) :
    List (ThreeBitInstruction (Fin (n + auxCount n))) :=
  FlatCircuit.flattenWord n (nestedWord p)

/-- The ambient smooth circuit obtained by evaluating the chosen flattened three-bit word. -/
noncomputable def ambient {n : ℕ} (p : BoolPermN n) :
    Diffeomorph (circlePowerModel (n + auxCount n)) (circlePowerModel (n + auxCount n))
      (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞ :=
  FlatCircuit.evalFlattenWord n (nestedWord p)

theorem ambient_eq_evalThreeBitWord {n : ℕ} (p : BoolPermN n) :
    ambient p = evalThreeBitWord (flatWord p) :=
  rfl

/-- Compiling a list of atomic Boolean edges preserves every universal auxiliary circle
coordinate for arbitrary ambient inputs.  This is the only induction that combines atomic
stability certificates; arbitrary-permutation decomposition remains confined to this terminal
leaf. -/
theorem compileAtomicWord_preservesUniversalAux {n : ℕ}
    (steps : List (AtomicStep (Fin n))) :
    PreservesUniversalAux n
      (FlatCircuit.evalFlattenWord n
        (Synthesis.ThreeBitUniversal.compileAtomicWord steps)) := by
  induction steps with
  | nil =>
      change PreservesUniversalAux n (fun p => p)
      exact preservesUniversalAux_id n
  | cons step steps ih =>
      rw [Synthesis.ThreeBitUniversal.compileAtomicWord_cons]
      exact AtomicStability.evalFlattenWord_append_preservesUniversalAux _ _
        (AtomicStability.atomicWord_preservesUniversalAux step) ih

/-- The chosen ambient three-bit circuit globally preserves both enables and every work
coordinate, not only their Boolean values and not only on the fixed face. -/
theorem ambient_preservesUniversalAux {n : ℕ} (p : BoolPermN n) :
    PreservesUniversalAux n (ambient p) := by
  rw [ambient, nestedWord, Synthesis.ThreeBitUniversal.word]
  exact compileAtomicWord_preservesUniversalAux (AtomicWord.decompose p)

/-- The ambient three-bit circuit consequently maps the whole fixed smooth auxiliary face into
itself. -/
theorem ambient_mapsUniversalFace {n : ℕ} (p : BoolPermN n) :
    MapsUniversalFace n (ambient p) :=
  (ambient_preservesUniversalAux p).mapsUniversalFace

/-- The inverse ambient circuit preserves the same auxiliary coordinates globally. -/
theorem ambient_symm_preservesUniversalAux {n : ℕ} (p : BoolPermN n) :
    PreservesUniversalAux n (ambient p).symm :=
  (ambient_preservesUniversalAux p).diffeomorph_symm

/-- Restrict the chosen ambient placed-three-bit circuit to the fixed universal auxiliary face
and delete the returned auxiliary components.  The result is a genuine diffeomorphism because
the entire smooth face, in both directions, is stable. -/
noncomputable def restricted {n : ℕ} (p : BoolPermN n) :
    Diffeomorph (circlePowerModel n) (circlePowerModel n)
      (CirclePower n) (CirclePower n) ∞ :=
  restrictUniversal n (ambient p) (ambient_preservesUniversalAux p)

@[simp]
theorem restricted_apply {n : ℕ} (p : BoolPermN n) (x : CirclePower n) :
    restricted p x = projectUniversal n (ambient p (insertUniversal n x)) :=
  rfl

/-- Discrete clean realization, restated using the nested universal input word. -/
theorem nestedWord_cleanRealizes {n : ℕ} (p : BoolPermN n) (x : BoolVec n) :
    ThreeBitCircuit.eval (nestedWord p) (universalInput x) = universalInput (p x) := by
  exact Synthesis.ThreeBitUniversal.word_cleanRealizes p x

/-- On embedded Boolean data, the ambient smooth circuit maps the fixed universal face exactly
as the requested Boolean permutation. -/
theorem ambient_interpolates_insertedBoolean {n : ℕ} (p : BoolPermN n) (x : BoolVec n) :
    ambient p (insertUniversal n (embed n x)) =
      insertUniversal n (embed n (p x)) := by
  rw [insertUniversal_embed, ambient]
  rw [FlatCircuit.evalFlattenWord_interpolates_universalInput]
  rw [nestedWord_cleanRealizes]
  change embed (n + auxCount n) (flatUniversalInput (p x)) = _
  exact (insertUniversal_embed n (p x)).symm

/-- Exact smooth face equation: for every circle-valued data point, not merely an embedded
Boolean point, ambient evaluation agrees with inserting the restricted output. -/
theorem ambient_insert_eq_insert_restricted {n : ℕ} (p : BoolPermN n)
    (x : CirclePower n) :
    ambient p (insertUniversal n x) = insertUniversal n (restricted p x) := by
  apply (insertUniversal_projectUniversal_of_face n ?_).symm
  exact ambient_mapsUniversalFace p _ (onUniversalFace_insertUniversal n x)

/-- The diffeomorphism obtained by restriction and certified auxiliary deletion interpolates the
requested finite Boolean permutation. -/
theorem restricted_interpolates {n : ℕ} (p : BoolPermN n) :
    Interpolates (restricted p) p := by
  intro x
  rw [restricted_apply, ambient_interpolates_insertedBoolean]
  exact projectUniversal_insertUniversal n (embed n (p x))

/-- Qualified smooth three-bit universality.  The witness is an explicit word of placed
three-bit instructions.  Its ambient smooth evaluation globally preserves the named auxiliary
bank, and restriction to the corresponding fixed face followed by certified projection gives a
diffeomorphism extending `p`.

This statement deliberately exposes the constants/restriction/deletion certificate; it is not an
ancilla-free universality theorem. -/
theorem exists_restricted_extension_from_threeBit {n : ℕ} (p : BoolPermN n) :
    ∃ word : List (ThreeBitInstruction (Fin (n + auxCount n))),
      ∃ F : Diffeomorph (circlePowerModel (n + auxCount n))
          (circlePowerModel (n + auxCount n))
          (CirclePower (n + auxCount n)) (CirclePower (n + auxCount n)) ∞,
        F = evalThreeBitWord word ∧
          ∃ hF : PreservesUniversalAux n F,
            Interpolates (restrictUniversal n F hF) p := by
  refine ⟨flatWord p, ambient p, ambient_eq_evalThreeBitWord p,
    ambient_preservesUniversalAux p, ?_⟩
  exact restricted_interpolates p

/-! ## Qualified realization witness -/

/-- Qualified smooth three-bit universality.  The witnesses expose the flattened three-bit word,
its ambient diffeomorphism, global preservation of the fixed auxiliary bank, the resulting data
diffeomorphism, exact agreement on the inserted smooth face, and Boolean interpolation. -/
theorem exists_qualified_smooth_realization {n : ℕ} (p : BoolPermN n) :
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
            Interpolates F p := by
  refine ⟨flatWord p, ambient p, ambient_preservesUniversalAux p, restricted p, ?_⟩
  exact ⟨rfl, rfl, ambient_insert_eq_insert_restricted p, restricted_interpolates p⟩

/-! ## Resource accounting inherited from the verified discrete compiler -/

theorem auxiliary_card (n : ℕ) :
    Fintype.card (UniversalAux n) = auxCount n :=
  Synthesis.ThreeBitUniversal.circuit_aux_card n

theorem auxiliary_card_eq_two {n : ℕ} (h : n ≤ 3) :
    Fintype.card (UniversalAux n) = 2 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_eq_two h

theorem auxiliary_card_eq_sub_one {n : ℕ} (h : 3 ≤ n) :
    Fintype.card (UniversalAux n) = n - 1 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_eq_sub_one h

theorem auxiliary_card_le_paper_bound {n : ℕ} (h : 3 ≤ n) :
    Fintype.card (UniversalAux n) ≤ 2 * n - 3 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_le_paper_bound h

/-! ## Empty-data boundary -/

theorem flatWord_zero_eq_nil (p : BoolPermN 0) : flatWord p = [] :=
  FlatCircuit.flattenWord_zero_eq_nil _

theorem ambient_zero_eq_refl (p : BoolPermN 0) :
    ambient p =
      Diffeomorph.refl (circlePowerModel (0 + auxCount 0))
        (CirclePower (0 + auxCount 0)) ∞ :=
  FlatCircuit.evalFlattenWord_zero_eq_refl _

/-- Although the uniform construction retains its two enable coordinates at arity zero, its
restricted data diffeomorphism is the identity of the singleton empty product. -/
theorem restricted_zero_eq_refl (p : BoolPermN 0) :
    restricted p =
      Diffeomorph.refl (circlePowerModel 0) (CirclePower 0) ∞ := by
  apply Diffeomorph.ext
  intro x
  exact Subsingleton.elim _ _

/-- At data arity zero no auxiliary circle is actually necessary: the identity diffeomorphism of
the singleton empty product interpolates the unique Boolean permutation. -/
theorem exists_zero_extension_noAux (p : BoolPermN 0) :
    ∃ F : Diffeomorph (circlePowerModel 0) (circlePowerModel 0)
        (CirclePower 0) (CirclePower 0) ∞,
      Interpolates F p := by
  refine ⟨Diffeomorph.refl (circlePowerModel 0) (CirclePower 0) ∞, ?_⟩
  intro x
  exact Subsingleton.elim _ _

end ThreeBitUniversal
end CircleExtension
end Toffoli
