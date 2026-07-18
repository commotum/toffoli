import Mathlib.Logic.Equiv.Fintype
import Toffoli.Circuit.ThreeBit
import Toffoli.Component.OneToOne

/-!
# Lowering placed three-bit gates to the canonical primitive

The complement of a placement range supplies the unused coordinates.  Splitting the ambient
coordinate type into the canonical three coordinates and that complement expresses every placed
instruction as identity extension followed by coordinate reindexing.
-/

namespace Toffoli

universe u

namespace ThreeBitInstruction

variable {ι : Type u} [DecidableEq ι]

/-- Ambient coordinates not occupied by this instruction. -/
abbrev Complement (g : ThreeBitInstruction ι) :=
  {i : ι // i ∉ Set.range g.placement}

/-- Split the ambient coordinates into the placed canonical triple and its complement. -/
def placementEquiv (g : ThreeBitInstruction ι) : Fin 3 ⊕ g.Complement ≃ ι :=
  (Equiv.sumCongr g.placement.toEquivRange (Equiv.refl g.Complement)).trans
    (Equiv.sumCompl (fun i ↦ i ∈ Set.range g.placement))

@[simp]
theorem placementEquiv_apply_inl (g : ThreeBitInstruction ι) (i : Fin 3) :
    g.placementEquiv (Sum.inl i) = g.placement i :=
  rfl

@[simp]
theorem placementEquiv_apply_inr (g : ThreeBitInstruction ι) (i : g.Complement) :
    g.placementEquiv (Sum.inr i) = i :=
  rfl

private theorem map_map {a b c : Type u} (first : a ↪ b) (second : b ↪ c)
    (gate : ToffoliGate a) :
    (gate.map first).map second = gate.map (first.trans second) := by
  apply ToffoliGate.ext
  · simp [ToffoliGate.map, Finset.map_map]
  · rfl

private theorem inl_trans_placementEquiv (g : ThreeBitInstruction ι) :
    Function.Embedding.inl.trans g.placementEquiv.toEmbedding = g.placement := by
  ext i
  rfl

/-- At the specification level, placement is canonical left-summand extension plus reindexing. -/
theorem gate_eq_map_inl (g : ThreeBitInstruction ι) :
    g.gate = ((AndNand.thetaSuccSpec 2).inl (g.Complement)).map g.placementEquiv.toEmbedding := by
  rw [ToffoliGate.inl, map_map, inl_trans_placementEquiv]
  rfl

/-- A placed instruction is the canonical three-bit gate, extended by identity and reindexed. -/
theorem perm_eq_reindex_extendRight (g : ThreeBitInstruction ι) :
    g.perm = BoolPerm.reindex g.placementEquiv
      (BoolPerm.extendRight (AndNand.thetaSucc 2) g.Complement) := by
  rw [← ToffoliGate.perm_inl (g := AndNand.thetaSuccSpec 2)]
  rw [← ToffoliGate.perm_map_equiv]
  exact congrArg ToffoliGate.perm g.gate_eq_map_inl

end ThreeBitInstruction

/-- The sole primitive family used by lowered circuits.  It has exactly one constructor, at the
canonical three-coordinate index type. -/
inductive CanonicalThreeBitAtom : Type u → Type u
  | gate : CanonicalThreeBitAtom (Fin 3)

namespace CanonicalThreeBitAtom

/-- Interpret the sole primitive as the paper's canonical three-bit Toffoli permutation. -/
def eval : {ι : Type u} → CanonicalThreeBitAtom ι → BoolPerm ι
  | _, .gate => AndNand.thetaSucc 2

@[simp]
theorem eval_gate : eval (.gate : CanonicalThreeBitAtom (Fin 3)) = AndNand.thetaSucc 2 :=
  rfl

end CanonicalThreeBitAtom

namespace ThreeBitLowering

variable {ι : Type u} [DecidableEq ι]

/-- Lower one placed instruction using a canonical primitive, identity extension, and reindexing. -/
def lowerInstruction (gate : ThreeBitInstruction ι) :
    OneToOneCircuit CanonicalThreeBitAtom ι :=
  .reindex gate.placementEquiv
    (.tensor (.primitive CanonicalThreeBitAtom.gate) (.identity :
      OneToOneCircuit CanonicalThreeBitAtom gate.Complement))

theorem eval_lowerInstruction (gate : ThreeBitInstruction ι) :
    OneToOneCircuit.eval CanonicalThreeBitAtom.eval (lowerInstruction gate) = gate.perm := by
  rw [lowerInstruction, OneToOneCircuit.eval_reindex, OneToOneCircuit.eval_tensor,
    OneToOneCircuit.eval_primitive, OneToOneCircuit.eval_identity]
  exact gate.perm_eq_reindex_extendRight.symm

/-- Lower a left-to-right placed-gate word to a one-to-one circuit over the sole canonical atom. -/
def lower : List (ThreeBitInstruction ι) → OneToOneCircuit CanonicalThreeBitAtom ι
  | [] => .identity
  | gate :: word => .serial (lowerInstruction gate) (lower word)

@[simp]
theorem lower_nil : lower ([] : List (ThreeBitInstruction ι)) = .identity :=
  rfl

@[simp]
theorem lower_cons (gate : ThreeBitInstruction ι) (word : List (ThreeBitInstruction ι)) :
    lower (gate :: word) = .serial (lowerInstruction gate) (lower word) :=
  rfl

/-- Lowering preserves the documented left-to-right word semantics. -/
theorem eval_lower (word : List (ThreeBitInstruction ι)) :
    OneToOneCircuit.eval CanonicalThreeBitAtom.eval (lower word) = ThreeBitCircuit.eval word := by
  induction word with
  | nil => rfl
  | cons gate word ih =>
      rw [lower_cons, OneToOneCircuit.eval_serial, eval_lowerInstruction, ih]
      rfl

end ThreeBitLowering

end Toffoli
