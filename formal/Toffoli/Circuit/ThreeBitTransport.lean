import Toffoli.Circuit.ThreeBit
import Toffoli.Bool.Reindex
import Toffoli.Synthesis.FaceRealization

/-!
# Transporting placed three-bit circuits

An equivalence of ambient coordinate types transports the placement carried by each instruction.
The resulting instruction and word evaluate to conjugation by the induced equivalence of Boolean
word spaces.  A final helper specializes this construction to a reindexing of data coordinates
that fixes a shared auxiliary bank pointwise.
-/

namespace Toffoli

universe u v w

namespace ThreeBitInstruction

variable {ι : Type u} {κ : Type v}

/-- Transport a placed instruction along an equivalence of its ambient coordinate type. -/
def reindex (e : ι ≃ κ) (gate : ThreeBitInstruction ι) : ThreeBitInstruction κ where
  placement := gate.placement.trans e.toEmbedding

@[simp]
theorem reindex_placement_apply (e : ι ≃ κ) (gate : ThreeBitInstruction ι) (i : Fin 3) :
    (reindex e gate).placement i = e (gate.placement i) :=
  rfl

private theorem map_map {α : Type u} {β : Type v} {γ : Type w} (first : α ↪ β)
    (second : β ↪ γ) (gate : ToffoliGate α) :
    (gate.map first).map second = gate.map (first.trans second) := by
  cases gate
  simp [ToffoliGate.map, Finset.map_map]

/-- Transporting a placement agrees with mapping its generalized-Toffoli specification. -/
theorem gate_reindex (e : ι ≃ κ) (gate : ThreeBitInstruction ι) :
    (reindex e gate).gate = gate.gate.map e.toEmbedding := by
  rw [ThreeBitInstruction.gate, ThreeBitInstruction.gate, reindex, map_map]

variable [DecidableEq ι] [DecidableEq κ]

/-- The transported instruction implements coordinate conjugation of the original permutation. -/
theorem perm_reindex (e : ι ≃ κ) (gate : ThreeBitInstruction ι) :
    (reindex e gate).perm = BoolPerm.reindex e gate.perm := by
  rw [ThreeBitInstruction.perm, gate_reindex, ToffoliGate.perm_map_equiv]
  rfl

end ThreeBitInstruction

namespace ThreeBitCircuit

variable {ι : Type u} {κ : Type v}

/-- Transport every placed instruction in a circuit word along an ambient coordinate
equivalence.  List order is unchanged. -/
def reindex (e : ι ≃ κ) (word : List (ThreeBitInstruction ι)) :
    List (ThreeBitInstruction κ) :=
  word.map (ThreeBitInstruction.reindex e)

@[simp]
theorem reindex_nil (e : ι ≃ κ) :
    reindex e ([] : List (ThreeBitInstruction ι)) = [] :=
  rfl

@[simp]
theorem reindex_cons (e : ι ≃ κ) (gate : ThreeBitInstruction ι)
    (word : List (ThreeBitInstruction ι)) :
    reindex e (gate :: word) = ThreeBitInstruction.reindex e gate :: reindex e word :=
  rfl

variable [DecidableEq ι] [DecidableEq κ]

/-- Evaluating a transported word agrees with reindexing the evaluated Boolean permutation. -/
theorem eval_reindex (e : ι ≃ κ) (word : List (ThreeBitInstruction ι)) :
    eval (reindex e word) = BoolPerm.reindex e (eval word) := by
  induction word with
  | nil => simp [reindex, BoolPerm.reindex]
  | cons gate word ih =>
      rw [reindex_cons, eval_cons, ThreeBitInstruction.perm_reindex, ih, eval_cons]
      exact (BoolPerm.reindex_serial e gate.perm (eval word)).symm

end ThreeBitCircuit

namespace Synthesis

variable {ι : Type u} {κ : Type v} {α : Type w}

/-- Reindexing only the data coordinates commutes with inserting a fixed right auxiliary word. -/
theorem reindexData_fixedRight (e : ι ≃ κ) (constants : BoolWord α) (x : BoolWord ι) :
    BoolWord.reindex (Equiv.sumCongr e (Equiv.refl α))
        (BoolWord.sumEquiv.symm (x, constants)) =
      BoolWord.sumEquiv.symm (BoolWord.reindex e x, constants) := by
  funext index
  cases index <;> simp [BoolWord.reindex]

/-- The inverse data-only reindexing also commutes with insertion of fixed right auxiliaries. -/
theorem reindexData_fixedRight_symm (e : ι ≃ κ) (constants : BoolWord α)
    (x : BoolWord κ) :
    (BoolWord.reindex (Equiv.sumCongr e (Equiv.refl α))).symm
        (BoolWord.sumEquiv.symm (x, constants)) =
      BoolWord.sumEquiv.symm ((BoolWord.reindex e).symm x, constants) := by
  funext index
  cases index <;> simp [BoolWord.reindex]

namespace CleanRealizes

variable {ambient : BoolPerm (ι ⊕ α)} {constants : BoolWord α} {target : BoolPerm ι}

/-- A clean realization remains clean after reindexing only its data coordinates and leaving the
auxiliary coordinate type and constants fixed. -/
theorem reindexData (h : CleanRealizes ambient constants target) (e : ι ≃ κ) :
    CleanRealizes
      (BoolPerm.reindex (Equiv.sumCongr e (Equiv.refl α)) ambient) constants
      (BoolPerm.reindex e target) := by
  intro x
  change
    BoolWord.reindex (Equiv.sumCongr e (Equiv.refl α))
        (ambient
          ((BoolWord.reindex (Equiv.sumCongr e (Equiv.refl α))).symm
            (BoolWord.sumEquiv.symm (x, constants)))) =
      BoolWord.sumEquiv.symm
        (BoolWord.reindex e (target ((BoolWord.reindex e).symm x)), constants)
  rw [reindexData_fixedRight_symm, h, reindexData_fixedRight]

end CleanRealizes

/-- Transport a cleanly realizing placed-gate word along a data-coordinate equivalence while
fixing the auxiliary bank pointwise. -/
theorem cleanRealizes_reindexData [DecidableEq (ι ⊕ α)] [DecidableEq (κ ⊕ α)]
    (e : ι ≃ κ) (word : List (ThreeBitInstruction (ι ⊕ α)))
    (constants : BoolWord α) (target : BoolPerm ι)
    (h : CleanRealizes (ThreeBitCircuit.eval word) constants target) :
    CleanRealizes
      (ThreeBitCircuit.eval
        (ThreeBitCircuit.reindex (Equiv.sumCongr e (Equiv.refl α)) word))
      constants (BoolPerm.reindex e target) := by
  rw [ThreeBitCircuit.eval_reindex]
  exact h.reindexData e

end Synthesis

end Toffoli
