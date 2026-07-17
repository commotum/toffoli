import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NativeDecide
import Toffoli.Gate.AndNand
import Toffoli.Gate.Wiring

/-!
# Generalized-gate boundary checks

This non-public leaf evaluates the named low-arity gates and checks that the specification has no
order-zero member. Generic correctness is proved in the public leaves; these computations guard
the Boolean and component-order conventions.
-/

namespace Toffoli.Audit

open Toffoli

example : IsEmpty (ToffoliGate (Fin 0)) :=
  ⟨fun gate => Fin.elim0 gate.target⟩

example : (ToffoliGate.notAt (0 : Fin 1)).perm ![false] = ![true] := by
  native_decide

example : AndNand.thetaSucc 0 ![true] = ![false] := by
  native_decide

example : AndNand.thetaSucc 1 ![false, false] = ![false, false] := by
  native_decide

example : AndNand.thetaSucc 1 ![true, false] = ![true, true] := by
  native_decide

example : AndNand.thetaSucc 2 ![true, true, false] = ![true, true, true] := by
  native_decide

example : AndNand.thetaSucc 2 ![true, false, false] = ![true, false, false] := by
  native_decide

example : AndNand.thetaSucc 2 ![false, true, true] = ![false, true, true] := by
  native_decide

example : AndNand.thetaSucc 2 ![true, true, true] = ![true, true, false] := by
  native_decide

example : (AndNand.thetaSuccSpec 0).Active ![false] := by
  native_decide

example : (AndNand.thetaSuccSpec 2).Active ![true, true, false] := by
  native_decide

example : ¬(AndNand.thetaSuccSpec 2).Active ![true, false, true] := by
  native_decide

end Toffoli.Audit
