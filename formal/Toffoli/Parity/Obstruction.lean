import Toffoli.Gate.Atomic
import Toffoli.Parity.Generated

/-!
# Lower-arity parity obstruction

The theorem is stronger than the AND/NAND-only claim: even if every proper-arity local primitive
is allowed to be an arbitrary permutation, placement plus serial composition cannot produce a
full-arity atomic edge.  Placement is represented by conjugation inside `ProperLift`; bare wiring
permutations are intentionally not smuggled into this closure.
-/

namespace Toffoli

universe u

variable {ι : Type u}

/-- Every lower-order AND/NAND gate placed into a larger coordinate space is one of the allowed
proper lifts. -/
theorem properlyGenerated_placed_andNand {κ μ : Type u} [Fintype κ] [DecidableEq κ] [Finite μ]
    [Nonempty μ] (target : κ) (wiring : κ ⊕ μ ≃ ι) :
    ProperlyGenerated
      (BoolPerm.reindex wiring (BoolPerm.extendRight (ToffoliGate.andNand target) μ)) :=
  ProperlyGenerated.reindex_extendRight (ToffoliGate.andNand target) wiring

/-- A literal Boolean-cube edge transposition is odd. -/
theorem sign_atomicEdge [Fintype ι] [DecidableEq ι] (x : BoolWord ι) (target : ι) :
    Equiv.Perm.sign (atomicEdge x target) = -1 := by
  classical
  exact Equiv.Perm.sign_swap (BoolWord.flipAt_ne x target).symm

/-- No serial composition of strict-coordinate lifts can produce an atomic edge. -/
theorem not_properlyGenerated_atomicEdge [Fintype ι] [DecidableEq ι]
    (x : BoolWord ι) (target : ι) :
    ¬ProperlyGenerated (atomicEdge x target) := by
  intro hgenerated
  have heven := hgenerated.sign_eq_one
  have hodd := sign_atomicEdge x target
  have : (-1 : ℤˣ) = 1 := hodd.symm.trans heven
  exact (by decide : (-1 : ℤˣ) ≠ 1) this

/-- The full all-other-controls AND/NAND gate is therefore outside the closure of arbitrary
proper-arity lifts. -/
theorem not_properlyGenerated_andNand [Fintype ι] [DecidableEq ι] (target : ι) :
    ¬ProperlyGenerated (ToffoliGate.andNand target) := by
  rw [ToffoliGate.andNand_eq_atomicEdge]
  exact not_properlyGenerated_atomicEdge (fun _ => true) target

/-- On every nonempty finite coordinate type, some invertible Boolean function cannot be built
from proper-arity primitives by placement and serial composition. -/
theorem exists_not_properlyGenerated [Finite ι] [Nonempty ι] :
    ∃ p : BoolPerm ι, ¬ProperlyGenerated p := by
  classical
  letI := Fintype.ofFinite ι
  let target : ι := Classical.choice inferInstance
  exact ⟨ToffoliGate.andNand target, not_properlyGenerated_andNand target⟩

/-- A proper lift cannot exist over an empty ambient coordinate type: its unused factor is
explicitly nonempty. -/
theorem properLift_false_of_isEmpty [IsEmpty ι] (g : ProperLift ι) : False := by
  obtain ⟨unused⟩ := g.unusedNonempty
  exact isEmptyElim (g.wiring (Sum.inr unused))

end Toffoli
