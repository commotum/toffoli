import Toffoli.Circuit.ThreeBitLowering
import Toffoli.Perm.Decomposition
import Toffoli.Synthesis.Atomic

/-!
# Qualified universality of the three-bit Toffoli gate

This deliberately heavy leaf is the only synthesis module that imports the arbitrary-permutation
decomposition.  It replaces each literal cube-edge atom by its clean placed-three-bit word and
then lowers the resulting word to one-to-one circuit syntax whose sole primitive is the canonical
three-bit Toffoli gate.

The theorem is qualified: two persistent `true` enables and `n - 3` clean `false` work bits are
fixed on input and returned unchanged on output.  Restriction to that face and certified deletion
of those dummy outputs are explicit corollaries below.  No ancilla-free universality claim is made.
-/

namespace Toffoli

namespace Synthesis

namespace ThreeBitUniversal

/-- Replace every literal cube-edge instruction by its clean placed-three-bit implementation. -/
noncomputable def compileAtomicWord {n : ℕ} (steps : List (AtomicStep (Fin n))) :
    List (ThreeBitInstruction (UniversalIndex n)) :=
  steps.flatMap Atomic.word

@[simp]
theorem compileAtomicWord_nil {n : ℕ} :
    compileAtomicWord ([] : List (AtomicStep (Fin n))) = [] :=
  rfl

@[simp]
theorem compileAtomicWord_cons {n : ℕ} (step : AtomicStep (Fin n))
    (steps : List (AtomicStep (Fin n))) :
    compileAtomicWord (step :: steps) = Atomic.word step ++ compileAtomicWord steps :=
  rfl

/-- Compiling a serial atomic word preserves its permutation and returns the shared auxiliary
bank clean. -/
theorem compileAtomicWord_cleanRealizes {n : ℕ} (steps : List (AtomicStep (Fin n))) :
    CleanRealizes (ThreeBitCircuit.eval (compileAtomicWord steps)) (universalConstants n)
      (AtomicWord.eval steps) := by
  induction steps with
  | nil => exact CleanRealizes.identity (universalConstants n)
  | cons step steps ih =>
      rw [compileAtomicWord_cons, ThreeBitCircuit.eval_append, AtomicWord.eval_cons]
      exact (Atomic.word_cleanRealizes step).serial ih

/-- A chosen placed-three-bit word implementing an arbitrary Boolean permutation. -/
noncomputable def word {n : ℕ} (p : BoolPermN n) :
    List (ThreeBitInstruction (UniversalIndex n)) :=
  compileAtomicWord (AtomicWord.decompose p)

/-- The chosen word cleanly realizes the requested Boolean permutation. -/
theorem word_cleanRealizes {n : ℕ} (p : BoolPermN n) :
    CleanRealizes (ThreeBitCircuit.eval (word p)) (universalConstants n) p := by
  rw [word]
  simpa only [AtomicWord.eval_decompose] using
    compileAtomicWord_cleanRealizes (AtomicWord.decompose p)

/-- Lower the chosen word to one-to-one syntax over the sole canonical three-bit primitive. -/
noncomputable def circuit {n : ℕ} (p : BoolPermN n) :
    OneToOneCircuit CanonicalThreeBitAtom (UniversalIndex n) :=
  ThreeBitLowering.lower (word p)

/-- Main clean-face normal form: the circuit uses only the canonical three-bit Toffoli primitive
and returns every fixed auxiliary coordinate unchanged. -/
theorem circuit_cleanRealizes {n : ℕ} (p : BoolPermN n) :
    CleanRealizes
      (OneToOneCircuit.eval CanonicalThreeBitAtom.eval (circuit p))
      (universalConstants n) p := by
  rw [circuit, ThreeBitLowering.eval_lower]
  exact word_cleanRealizes p

/-- Existential form of qualified three-bit universality. -/
theorem exists_circuit_cleanRealizes {n : ℕ} (p : BoolPermN n) :
    ∃ c : OneToOneCircuit CanonicalThreeBitAtom (UniversalIndex n),
      CleanRealizes (OneToOneCircuit.eval CanonicalThreeBitAtom.eval c)
        (universalConstants n) p :=
  ⟨circuit p, circuit_cleanRealizes p⟩

/-- The auxiliary type appearing in the main theorem has exactly the documented piecewise
resource count. -/
theorem circuit_aux_card (n : ℕ) :
    Fintype.card (UniversalAux n) = auxCount n :=
  card_universalAux n

/-- The uniform bank has two enable bits at arities at most three; the separate zero-arity theorem
below removes even those when no data coordinate exists. -/
theorem circuit_aux_card_eq_two {n : ℕ} (h : n ≤ 3) :
    Fintype.card (UniversalAux n) = 2 := by
  rw [circuit_aux_card, auxCount_eq_two h]

/-- From arity three onward, the construction uses exactly `n - 1` shared clean auxiliaries. -/
theorem circuit_aux_card_eq_sub_one {n : ℕ} (h : 3 ≤ n) :
    Fintype.card (UniversalAux n) = n - 1 := by
  rw [circuit_aux_card, auxCount_eq_sub_one h]

/-- Consequently the verified construction satisfies the paper's `2n - 3` upper bound in its
valid range `n ≥ 3`.  The low-arity correction is intentionally not hidden by this wrapper. -/
theorem circuit_aux_card_le_paper_bound {n : ℕ} (h : 3 ≤ n) :
    Fintype.card (UniversalAux n) ≤ 2 * n - 3 := by
  rw [circuit_aux_card]
  exact auxCount_le_two_mul_sub_three h

/-- The universal circuit maps the fixed clean face exactly onto itself. -/
theorem circuit_maps_faces {n : ℕ} (p : BoolPermN n)
    (x : BoolWord (UniversalIndex n)) :
    OneToOneCircuit.eval CanonicalThreeBitAtom.eval (circuit p) x ∈
        (Face.right (universalConstants n)).carrier ↔
      x ∈ (Face.right (universalConstants n)).carrier :=
  (circuit_cleanRealizes p).maps_faces x

/-- On the fixed face, restriction of the ambient circuit is exactly the requested permutation,
transported through the canonical insertion/deletion equivalence. -/
theorem circuit_restrictFaces_eq {n : ℕ} (p : BoolPermN n) :
    Component.restrictFaces
        (OneToOneCircuit.eval CanonicalThreeBitAtom.eval (circuit p))
        (Face.right (universalConstants n)) (Face.right (universalConstants n))
        (circuit_maps_faces p) =
      (Component.fixRightEquiv (universalConstants n)).symm.trans
        (p.trans (Component.fixRightEquiv (universalConstants n))) :=
  (circuit_cleanRealizes p).restrictFaces_eq

/-- The auxiliary outputs are certified semantic dummies on the fixed input face. -/
theorem circuit_rightDummy {n : ℕ} (p : BoolPermN n) :
    Component.RightDummy
      (fun x : BoolVec n =>
        OneToOneCircuit.eval CanonicalThreeBitAtom.eval (circuit p)
          (BoolWord.sumEquiv.symm (x, universalConstants n)))
      (universalConstants n) :=
  (circuit_cleanRealizes p).rightDummy

/-- Certified deletion of the returned auxiliary outputs leaves exactly the requested Boolean
permutation. -/
theorem circuit_deleteRight_eq {n : ℕ} (p : BoolPermN n) :
    (circuit_rightDummy p).deleteRight = p :=
  (circuit_cleanRealizes p).deleteRight_eq

/-- At arity zero no auxiliary coordinate is needed: the unique permutation is already the empty
identity circuit.  This is separate from the uniform positive-arity resource profile. -/
theorem exists_zero_circuit_noAux (p : BoolPermN 0) :
    ∃ c : OneToOneCircuit CanonicalThreeBitAtom (Fin 0),
      OneToOneCircuit.eval CanonicalThreeBitAtom.eval c = p := by
  refine ⟨OneToOneCircuit.identity, ?_⟩
  apply Equiv.ext
  intro x
  exact Subsingleton.elim _ _

end ThreeBitUniversal

end Synthesis

end Toffoli
