import Toffoli.Parity.Lift

/-!
# Serial closure of proper-arity Boolean permutations

`ProperLift` makes the local coordinates, nonempty unused factor, and coordinate placement
explicit.  Its `wiring` is used for conjugation/placement; it is not itself inserted as a bare
permutation gate.  The local permutation is arbitrary, so the resulting parity theorem is
strictly stronger than the AND/NAND-only statement needed from the paper.
-/

namespace Toffoli

universe u

/-- A permutation on a strict subcollection of coordinates, extended by identity and placed into
an ambient Boolean word space. -/
structure ProperLift (ι : Type u) where
  active : Type u
  unused : Type u
  activeFintype : Fintype active
  unusedFintype : Fintype unused
  unusedNonempty : Nonempty unused
  wiring : active ⊕ unused ≃ ι
  localPerm : BoolPerm active

namespace ProperLift

variable {ι : Type u}

/-- The ambient permutation represented by a proper lift. -/
def perm (g : ProperLift ι) : BoolPerm ι :=
  BoolPerm.reindex g.wiring (BoolPerm.extendRight g.localPerm g.unused)

/-- Bundle any identity extension with a nonempty unused coordinate type. -/
def ofPerm {κ μ : Type u} [Fintype κ] [Fintype μ] [Nonempty μ]
    (p : BoolPerm κ) (wiring : κ ⊕ μ ≃ ι) : ProperLift ι where
  active := κ
  unused := μ
  activeFintype := inferInstance
  unusedFintype := inferInstance
  unusedNonempty := inferInstance
  wiring := wiring
  localPerm := p

/-- Every proper lift is even because its local action is repeated over an even number of Boolean
assignments to the nonempty unused factor. -/
theorem sign_perm [Fintype ι] [DecidableEq ι] (g : ProperLift ι) :
    Equiv.Perm.sign g.perm = 1 := by
  classical
  letI := g.activeFintype
  letI := g.unusedFintype
  letI := g.unusedNonempty
  rw [perm, BoolPerm.sign_reindex]
  exact BoolPerm.sign_extendRight_of_nonempty g.localPerm

end ProperLift

/-- The source-faithful closure under ordinary serial composition of placed proper-arity
permutations.  Serial composition applies `first` and then `second`. -/
inductive ProperlyGenerated {ι : Type u} : BoolPerm ι → Prop
  | identity : ProperlyGenerated (Equiv.refl _)
  | lift (g : ProperLift ι) : ProperlyGenerated g.perm
  | serial {first second : BoolPerm ι}
      (hfirst : ProperlyGenerated first) (hsecond : ProperlyGenerated second) :
      ProperlyGenerated (first.trans second)

namespace ProperlyGenerated

variable {ι : Type u}

/-- Serial composition of proper lifts can produce only even permutations. -/
theorem sign_eq_one [Fintype ι] [DecidableEq ι] {p : BoolPerm ι}
    (h : ProperlyGenerated p) : Equiv.Perm.sign p = 1 := by
  induction h with
  | identity => simp
  | lift g => exact g.sign_perm
  | serial hfirst hsecond ihfirst ihsecond =>
      rw [Equiv.Perm.sign_trans, ihfirst, ihsecond, mul_one]

/-- A convenient constructor spelling out placement of a proper local permutation. -/
theorem reindex_extendRight {κ μ : Type u} [Finite κ] [Finite μ] [Nonempty μ]
    (p : BoolPerm κ) (wiring : κ ⊕ μ ≃ ι) :
    ProperlyGenerated (BoolPerm.reindex wiring (BoolPerm.extendRight p μ)) := by
  classical
  letI := Fintype.ofFinite κ
  letI := Fintype.ofFinite μ
  change ProperlyGenerated (ProperLift.ofPerm p wiring).perm
  exact ProperlyGenerated.lift (ProperLift.ofPerm p wiring)

end ProperlyGenerated

end Toffoli
