import Mathlib.Data.Fin.VecNotation
import Toffoli.Synthesis.Obstruction
import Toffoli.Synthesis.Universality

/-!
# Qualified-universality boundary checks

These diagnostics exercise the exact Figure 7 order, empty and low arities, the qualified clean
face theorem and its restriction/deletion consequences, and the structural one-auxiliary
obstruction.  The generic synthesis and obstruction proofs live in public theorem leaves; the
small computations below only guard conventions and corrected resource boundaries.
-/

namespace Toffoli.Audit

open Toffoli

/-! ## Corrected Figure 7 order -/

example :
    Synthesis.MultiControl.word 4 =
      [Synthesis.MultiControl.firstPrefix 0, Synthesis.MultiControl.targetInstruction 0,
        Synthesis.MultiControl.firstPrefix 0] :=
  Synthesis.MultiControl.figureSeven_word

example (x : BoolVec 4) :
    ThreeBitCircuit.eval
        [Synthesis.MultiControl.firstPrefix 0, Synthesis.MultiControl.targetInstruction 0,
          Synthesis.MultiControl.firstPrefix 0]
        (Synthesis.MultiControl.inputState x) =
      Synthesis.MultiControl.inputState (AndNand.thetaSucc 3 x) :=
  Synthesis.MultiControl.figureSeven_apply x

/-! ## Empty and low arities -/

example : Synthesis.MultiControl.word 0 = [] :=
  rfl

example :
    ThreeBitCircuit.eval (Synthesis.MultiControl.word 0) =
      Equiv.refl (BoolWord (Synthesis.UniversalIndex 0)) :=
  Synthesis.MultiControl.eval_word_zero

example : Fintype.card (Synthesis.UniversalAux 0) = 2 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_eq_two (by decide)

example : Fintype.card (Synthesis.UniversalAux 1) = 2 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_eq_two (by decide)

example : Fintype.card (Synthesis.UniversalAux 2) = 2 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_eq_two (by decide)

example : Fintype.card (Synthesis.UniversalAux 3) = 2 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_eq_two (by decide)

example : Fintype.card (Synthesis.UniversalAux 4) = 3 :=
  Synthesis.ThreeBitUniversal.circuit_aux_card_eq_sub_one (by decide)

/-- The paper's literal `2n - 3` count fails at arity one. -/
example : ¬Fintype.card (Synthesis.UniversalAux 1) ≤ 2 * 1 - 3 := by
  decide

/-- The paper's literal `2n - 3` count also fails at arity two. -/
example : ¬Fintype.card (Synthesis.UniversalAux 2) ≤ 2 * 2 - 3 := by
  decide

example (p : BoolPermN 0) :
    ∃ c : OneToOneCircuit CanonicalThreeBitAtom (Fin 0),
      OneToOneCircuit.eval CanonicalThreeBitAtom.eval c = p :=
  Synthesis.ThreeBitUniversal.exists_zero_circuit_noAux p

/-! ## Qualified clean universality and its permitted post-processing -/

example {n : ℕ} (p : BoolPermN n) :
    ∃ c : OneToOneCircuit CanonicalThreeBitAtom (Synthesis.UniversalIndex n),
      Synthesis.CleanRealizes (OneToOneCircuit.eval CanonicalThreeBitAtom.eval c)
        (Synthesis.universalConstants n) p :=
  Synthesis.ThreeBitUniversal.exists_circuit_cleanRealizes p

example {n : ℕ} (p : BoolPermN n) :
    Synthesis.CleanRealizes
      (OneToOneCircuit.eval CanonicalThreeBitAtom.eval
        (Synthesis.ThreeBitUniversal.circuit p))
      (Synthesis.universalConstants n) p :=
  Synthesis.ThreeBitUniversal.circuit_cleanRealizes p

example {n : ℕ} (p : BoolPermN n) (x : BoolWord (Synthesis.UniversalIndex n)) :
    OneToOneCircuit.eval CanonicalThreeBitAtom.eval
          (Synthesis.ThreeBitUniversal.circuit p) x ∈
        (Face.right (Synthesis.universalConstants n)).carrier ↔
      x ∈ (Face.right (Synthesis.universalConstants n)).carrier :=
  Synthesis.ThreeBitUniversal.circuit_maps_faces p x

example {n : ℕ} (p : BoolPermN n) :
    Component.restrictFaces
        (OneToOneCircuit.eval CanonicalThreeBitAtom.eval
          (Synthesis.ThreeBitUniversal.circuit p))
        (Face.right (Synthesis.universalConstants n))
        (Face.right (Synthesis.universalConstants n))
        (Synthesis.ThreeBitUniversal.circuit_maps_faces p) =
      (Component.fixRightEquiv (Synthesis.universalConstants n)).symm.trans
        (p.trans (Component.fixRightEquiv (Synthesis.universalConstants n))) :=
  Synthesis.ThreeBitUniversal.circuit_restrictFaces_eq p

example {n : ℕ} (p : BoolPermN n) :
    Component.RightDummy
      (fun x : BoolVec n ↦
        OneToOneCircuit.eval CanonicalThreeBitAtom.eval
          (Synthesis.ThreeBitUniversal.circuit p)
          (BoolWord.sumEquiv.symm (x, Synthesis.universalConstants n)))
      (Synthesis.universalConstants n) :=
  Synthesis.ThreeBitUniversal.circuit_rightDummy p

example {n : ℕ} (p : BoolPermN n) :
    (Synthesis.ThreeBitUniversal.circuit_rightDummy p).deleteRight = p :=
  Synthesis.ThreeBitUniversal.circuit_deleteRight_eq p

/-! ## One clean auxiliary is structurally insufficient at two data bits -/

example (ambient : BoolPerm (Fin 2 ⊕ Fin 1))
    (hgenerated : Synthesis.ThreeBitGenerated (Fin 2 ⊕ Fin 1) ambient)
    (input output : BoolWord (Fin 1)) :
    ¬Synthesis.FaceRealizes ambient input output Synthesis.twoBitDoubleNot :=
  Synthesis.oneAux_not_faceRealizes_twoBitDoubleNot ambient hgenerated input output

end Toffoli.Audit
