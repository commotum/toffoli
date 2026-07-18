import Toffoli.Synthesis.Obstruction
import Toffoli.Synthesis.Universality

/-!
# Qualified-universality axiom audit

This diagnostic leaf prints the assumptions of representative lowering, generalized-gate,
atomic-synthesis, qualified-universality, restriction/deletion, and structural-obstruction
theorems.
-/

#print axioms Toffoli.ThreeBitLowering.eval_lowerInstruction
#print axioms Toffoli.ThreeBitLowering.eval_lower
#print axioms Toffoli.Synthesis.MultiControl.figureSeven_apply
#print axioms Toffoli.Synthesis.MultiControl.word_cleanRealizes
#print axioms Toffoli.Synthesis.Atomic.word_cleanRealizes
#print axioms Toffoli.Synthesis.ThreeBitUniversal.exists_circuit_cleanRealizes
#print axioms Toffoli.Synthesis.ThreeBitUniversal.circuit_cleanRealizes
#print axioms Toffoli.Synthesis.ThreeBitUniversal.circuit_restrictFaces_eq
#print axioms Toffoli.Synthesis.ThreeBitUniversal.circuit_deleteRight_eq
#print axioms Toffoli.Synthesis.oneAux_not_faceRealizes_twoBitDoubleNot
