import Toffoli.Cube.Basic
import Toffoli.Gate.AndNand

/-!
# Atomic Boolean cube edges

An atomic permutation is the literal transposition of the two endpoints of one Boolean-cube
edge.  This is deliberately stricter than a lower-control gate extended across unused
coordinates: an atom moves exactly two words.
-/

namespace Toffoli

universe u

variable {ι : Type u} [DecidableEq ι] [DecidableEq (BoolWord ι)]

/-- The atomic permutation supported on the edge from `x` in direction `target`. -/
def atomicEdge (x : BoolWord ι) (target : ι) : BoolPerm ι :=
  Equiv.swap x (x.flipAt target)

@[simp]
theorem atomicEdge_apply_base (x : BoolWord ι) (target : ι) :
    atomicEdge x target x = x.flipAt target := by
  simp [atomicEdge]

@[simp]
theorem atomicEdge_apply_flipAt (x : BoolWord ι) (target : ι) :
    atomicEdge x target (x.flipAt target) = x := by
  simp [atomicEdge]

theorem atomicEdge_apply_of_ne (x y : BoolWord ι) (target : ι) (hyx : y ≠ x)
    (hyflip : y ≠ x.flipAt target) : atomicEdge x target y = y :=
  Equiv.swap_apply_of_ne_of_ne hyx hyflip

theorem atomicEdge_apply_ne_iff (x y : BoolWord ι) (target : ι) :
    atomicEdge x target y ≠ y ↔ y = x ∨ y = x.flipAt target := by
  constructor
  · exact Equiv.eq_or_eq_of_swap_apply_ne_self
  · intro h
    rcases h with h | h
    · subst y
      simpa using BoolWord.flipAt_ne x target
    · subst y
      simpa using (BoolWord.flipAt_ne x target).symm

/-- Reversing the orientation used to name an edge does not change its atomic permutation. -/
theorem atomicEdge_flipAt (x : BoolWord ι) (target : ι) :
    atomicEdge (x.flipAt target) target = atomicEdge x target := by
  rw [atomicEdge, BoolWord.flipAt_involutive, atomicEdge, Equiv.swap_comm]

@[simp]
theorem atomicEdge_symm (x : BoolWord ι) (target : ι) :
    (atomicEdge x target).symm = atomicEdge x target := by
  simp [atomicEdge]

@[simp]
theorem atomicEdge_trans_self (x : BoolWord ι) (target : ι) :
    (atomicEdge x target).trans (atomicEdge x target) = Equiv.refl _ := by
  exact Equiv.swap_swap _ _

theorem cubeAdjacent_atomicEdge_base (x : BoolWord ι) (target : ι) :
    CubeAdjacent x (atomicEdge x target x) := by
  rw [atomicEdge_apply_base]
  exact CubeAdjacent.flipAt x target

namespace ToffoliGate

variable [Fintype ι]

/-- The all-other-controls AND/NAND gate is the atom on the edge incident to the all-`true`
word in the target direction. -/
theorem andNand_eq_atomicEdge (target : ι) :
    andNand target = atomicEdge (fun _ => true) target := by
  apply Equiv.ext
  intro x
  by_cases hactive : ∀ i, i ≠ target → x i = true
  · cases htarget : x target
    · have hx : x = BoolWord.flipAt (fun _ : ι => true) target := by
        funext i
        by_cases hi : i = target
        · subst i
          simp [htarget]
        · rw [BoolWord.flipAt_apply_of_ne _ hi, hactive i hi]
      subst x
      rw [atomicEdge_apply_flipAt]
      funext i
      by_cases hi : i = target
      · subst i
        rw [andNand_apply_target, if_pos hactive]
        simp
      · rw [andNand_apply_of_ne _ _ hi]
        simp [BoolWord.flipAt_apply_of_ne _ hi]
    · have hx : x = (fun _ => true : BoolWord ι) := by
        funext i
        by_cases hi : i = target
        · simpa [hi] using htarget
        · exact hactive i hi
      subst x
      rw [atomicEdge_apply_base]
      funext i
      by_cases hi : i = target
      · subst i
        simp [andNand_apply_target]
      · rw [andNand_apply_of_ne _ _ hi, BoolWord.flipAt_apply_of_ne _ hi]
  · have hbase : x ≠ (fun _ => true : BoolWord ι) := by
      intro hx
      apply hactive
      intro i _
      simp [hx]
    have hflip : x ≠ BoolWord.flipAt (fun _ : ι => true) target := by
      intro hx
      apply hactive
      intro i hi
      rw [hx, BoolWord.flipAt_apply_of_ne _ hi]
    rw [atomicEdge_apply_of_ne _ _ _ hbase hflip]
    funext i
    by_cases hi : i = target
    · subst i
      simp [andNand_apply_target, hactive]
    · exact andNand_apply_of_ne target x hi

/-- Conjugating an arbitrary cube-edge atom by a componentwise NOT mask gives the canonical
all-positive AND/NAND atom.  Both the pre- and post-compositions in this conjugation are
essential; applying NOT only before the gate would not preserve the permutation outside the
chosen edge. -/
theorem edgeNormalizer_permCongr_atomicEdge (base : BoolWord ι) (target : ι) :
    (BoolWord.edgeNormalizer base).permCongr (atomicEdge base target) = andNand target := by
  rw [atomicEdge, Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
  simp only [BoolWord.edgeNormalizer_apply_base,
    BoolWord.edgeNormalizer_apply_flipAt, andNand_eq_atomicEdge, atomicEdge]

/-- Equivalently, every atomic edge is obtained from the AND/NAND atom by the same masked NOT
before and after it. -/
theorem atomicEdge_eq_edgeNormalizer_permCongr_andNand (base : BoolWord ι) (target : ι) :
    atomicEdge base target =
      (BoolWord.edgeNormalizer base).permCongr (andNand target) := by
  simp only [andNand_eq_atomicEdge, atomicEdge, Equiv.permCongr_def,
    Equiv.symm_trans_swap_trans, BoolWord.edgeNormalizer_apply_allTrue,
    BoolWord.edgeNormalizer_apply_allTrue_flipAt]

end ToffoliGate

end Toffoli
