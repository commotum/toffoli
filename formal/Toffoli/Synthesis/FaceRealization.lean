import Toffoli.Component.Dummy

/-!
# Realization on fixed auxiliary faces

This file gives the low-dependency semantics used by the qualified universality theorem.  An
ambient Boolean permutation realizes a data permutation when it maps every input with a specified
auxiliary word to the requested data output with a specified auxiliary output word.  Requiring the
two auxiliary words to agree is the stronger, garbage-free notion of clean realization.

The certificate records both input and output constants.  Restriction to a face and deletion of
dummy output components are derived operations, not part of the definition.
-/

namespace Toffoli

universe u v

namespace Synthesis

variable {ι : Type u} {κ : Type v}

/-- `ambient` realizes `target` between the faces fixing the right auxiliary coordinates to
`input` and `output`, respectively. -/
def FaceRealizes (ambient : BoolPerm (ι ⊕ κ)) (input output : BoolWord κ)
    (target : BoolPerm ι) : Prop :=
  ∀ x, ambient (BoolWord.sumEquiv.symm (x, input)) =
    BoolWord.sumEquiv.symm (target x, output)

/-- A clean realization returns every auxiliary coordinate to its input value. -/
def CleanRealizes (ambient : BoolPerm (ι ⊕ κ)) (constants : BoolWord κ)
    (target : BoolPerm ι) : Prop :=
  FaceRealizes ambient constants constants target

namespace FaceRealizes

variable {ambient first second : BoolPerm (ι ⊕ κ)}
variable {input middle output : BoolWord κ}
variable {target p q : BoolPerm ι}

/-- Identity realizes identity on every fixed auxiliary face. -/
theorem identity (constants : BoolWord κ) :
    FaceRealizes (Equiv.refl (BoolWord (ι ⊕ κ))) constants constants
      (Equiv.refl (BoolWord ι)) := by
  intro x
  rfl

/-- Serial composition applies the first realization and then the second realization. -/
theorem serial (hfirst : FaceRealizes first input middle p)
    (hsecond : FaceRealizes second middle output q) :
    FaceRealizes (first.trans second) input output (p.trans q) := by
  intro x
  change second (first (BoolWord.sumEquiv.symm (x, input))) =
    BoolWord.sumEquiv.symm (q (p x), output)
  rw [hfirst x, hsecond (p x)]

/-- Reversing the ambient and data permutations reverses a face realization. -/
theorem symm (h : FaceRealizes ambient input output target) :
    FaceRealizes ambient.symm output input target.symm := by
  intro y
  apply ambient.injective
  simpa using (h (target.symm y)).symm

/-- A realization maps every point of its specified source face into its target face. -/
theorem maps_source_to_target (h : FaceRealizes ambient input output target)
    {z : BoolWord (ι ⊕ κ)} (hz : z ∈ (Face.right input).carrier) :
    ambient z ∈ (Face.right output).carrier := by
  let x : BoolWord ι := (BoolWord.sumEquiv z).1
  have hz_eq : z = BoolWord.sumEquiv.symm (x, input) := by
    funext j
    cases j with
    | inl i => rfl
    | inr k => exact (Face.mem_right_iff input z).1 hz k
  rw [hz_eq, h x]
  exact (Face.mem_right_iff output _).2 fun _ => rfl

/-- Exact face membership: an input is in the source face exactly when its image is in the target
face.  The reverse implication uses bijectivity of the ambient permutation, not an extra
assumption. -/
theorem maps_faces (h : FaceRealizes ambient input output target) (z : BoolWord (ι ⊕ κ)) :
    ambient z ∈ (Face.right output).carrier ↔ z ∈ (Face.right input).carrier := by
  constructor
  · intro hz
    have hback := h.symm.maps_source_to_target (z := ambient z) hz
    simpa using hback
  · exact h.maps_source_to_target

/-- Restricting the ambient permutation to the two fixed faces is exactly the target permutation,
transported through the canonical insertion/deletion equivalences for those faces. -/
theorem restrictFaces_eq (h : FaceRealizes ambient input output target) :
    Component.restrictFaces ambient (Face.right input) (Face.right output) h.maps_faces =
      (Component.fixRightEquiv input).symm.trans
        (target.trans (Component.fixRightEquiv output)) := by
  apply Equiv.ext
  intro z
  apply Subtype.ext
  let x : BoolWord ι := (BoolWord.sumEquiv z.val).1
  have hz_eq : z.val = BoolWord.sumEquiv.symm (x, input) := by
    funext j
    cases j with
    | inl i => rfl
    | inr k => exact (Face.mem_right_iff input z.val).1 z.property k
  change ambient z.val = BoolWord.sumEquiv.symm (target x, output)
  rw [hz_eq]
  exact h x

/-- Running the ambient permutation only on inputs with the fixed auxiliary word gives certified
constant right outputs. -/
theorem rightDummy (h : FaceRealizes ambient input output target) :
    Component.RightDummy
      (fun x : BoolWord ι => ambient (BoolWord.sumEquiv.symm (x, input))) output where
  eq_const x k := by
    rw [h x]
    rfl

/-- Certified deletion of the fixed auxiliary outputs leaves exactly the target permutation. -/
theorem deleteRight_eq (h : FaceRealizes ambient input output target) :
    h.rightDummy.deleteRight = target := by
  funext x i
  change ambient (BoolWord.sumEquiv.symm (x, input)) (Sum.inl i) = target x i
  rw [h x]
  rfl

end FaceRealizes

namespace CleanRealizes

variable {first second : BoolPerm (ι ⊕ κ)}
variable {constants : BoolWord κ}
variable {p q : BoolPerm ι}

/-- Identity is a clean realization of identity. -/
theorem identity (constants : BoolWord κ) :
    CleanRealizes (Equiv.refl (BoolWord (ι ⊕ κ))) constants
      (Equiv.refl (BoolWord ι)) :=
  FaceRealizes.identity constants

/-- Clean realizations are closed under serial composition. -/
theorem serial (hfirst : CleanRealizes first constants p)
    (hsecond : CleanRealizes second constants q) :
    CleanRealizes (first.trans second) constants (p.trans q) :=
  FaceRealizes.serial hfirst hsecond

end CleanRealizes

end Synthesis

end Toffoli
