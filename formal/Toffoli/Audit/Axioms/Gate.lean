import Toffoli.Gate.AndNand
import Toffoli.Gate.Wiring

/-!
# Generalized-gate axiom audit

This non-public leaf reports the axioms used by the main generalized Toffoli declarations and
wiring laws.
-/

#print axioms Toffoli.ToffoliGate.active_update_target
#print axioms Toffoli.ToffoliGate.run_involutive
#print axioms Toffoli.ToffoliGate.perm_trans_self
#print axioms Toffoli.ToffoliGate.run_eq_self_iff
#print axioms Toffoli.ToffoliGate.target_false_is_and
#print axioms Toffoli.ToffoliGate.target_true_is_nand
#print axioms Toffoli.ToffoliGate.andNand_apply_target
#print axioms Toffoli.AndNand.thetaSucc_active_iff
#print axioms Toffoli.AndNand.thetaSucc_apply_target
#print axioms Toffoli.ToffoliGate.perm_map_equiv
#print axioms Toffoli.ToffoliGate.perm_inl
