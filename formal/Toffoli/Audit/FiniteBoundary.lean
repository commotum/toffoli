import Toffoli.Bool.Finite
import Toffoli.Bool.Reindex
import Toffoli.Component.Dummy
import Toffoli.Component.OneToOne

/-!
# Finite-core boundary checks

This diagnostic leaf checks empty arity, disjoint tensoring, fixed-face insertion/deletion, semantic
dummy reconstruction, and one-to-one circuit evaluation. Public modules do not import it.
-/

namespace Toffoli.Audit

open Toffoli

example : Fintype.card (BoolVec 0) = 1 := card_boolVec_zero

example (p : BoolPermN 0) : p = Equiv.refl (BoolVec 0) :=
  boolPermN_zero_eq_refl p

example {ι κ : Type} (e : ι ≃ κ) (x : BoolWord ι) (i : ι) :
    BoolWord.reindex e x (e i) = x i := by
  simp

example {ι κ : Type} (p : BoolPerm ι) (q : BoolPerm κ) (x : BoolWord (ι ⊕ κ)) (i : ι) :
    BoolPerm.tensor p q x (Sum.inl i) = p (fun j => x (Sum.inl j)) i :=
  rfl

example {ι κ : Type} (c : BoolWord κ) (x : BoolWord ι) :
    (Component.fixRightEquiv c).symm (Component.fixRightEquiv c x) = x := by
  exact Equiv.symm_apply_apply _ _

def sampleOutputs : Bool → BoolWord (PUnit ⊕ PUnit) :=
  Component.assembleRight (fun b _ => b) (fun _ => false)

theorem sampleOutputs_rightDummy :
    Component.RightDummy sampleOutputs (fun _ : PUnit => false) where
  eq_const _ _ := rfl

example :
    Component.assembleRight (Component.keepLeft sampleOutputs) (fun _ : PUnit => false) =
      sampleOutputs :=
  sampleOutputs_rightDummy.reconstruct

def noAtomEval {ι : Type} : Empty → BoolPerm ι :=
  Empty.elim

example (circuit : OneToOneCircuit (fun _ : Type => Empty) (Fin 0)) :
    circuit.eval noAtomEval = Equiv.refl (BoolVec 0) :=
  boolPermN_zero_eq_refl _

end Toffoli.Audit
