import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NativeDecide
import Toffoli.Parity.Obstruction

/-!
# Parity boundary checks

These finite computations validate the exponent and expose the two-bit bare-wiring exception.
They are diagnostics, not substitutes for the generic sign proofs.
-/

namespace Toffoli.Audit

open Toffoli

example :
    Equiv.Perm.sign (atomicEdge ![false] (0 : Fin 1)) = -1 := by
  native_decide

example :
    Equiv.Perm.sign
      (BoolPerm.extendRight (atomicEdge ![false] (0 : Fin 1)) (Fin 0)) = -1 := by
  native_decide

example :
    Equiv.Perm.sign
      (BoolPerm.extendRight (atomicEdge ![false] (0 : Fin 1)) (Fin 1)) = 1 := by
  native_decide

/-- A bare swap of the two coordinate labels induces one transposition on the four cube vertices,
so it is odd. This is why the paper's parity proof cannot silently include free wiring at `n=2`. -/
example :
    Equiv.Perm.sign
      (BoolPerm.coordinatePerm (Equiv.swap (0 : Fin 2) (1 : Fin 2))) = -1 := by
  native_decide

/-- With a third ambient bit, the same coordinate swap is repeated on two fibers and is even. -/
example :
    Equiv.Perm.sign
      (BoolPerm.coordinatePerm (Equiv.swap (0 : Fin 3) (1 : Fin 3))) = 1 := by
  native_decide

example (g : ProperLift (Fin 0)) : False :=
  properLift_false_of_isEmpty g

example : ∃ p : BoolPermN 1, ¬ProperlyGenerated p :=
  exists_not_properlyGenerated

example : ∃ p : BoolPermN 2, ¬ProperlyGenerated p :=
  exists_not_properlyGenerated

end Toffoli.Audit
