import Toffoli.Smooth.CircleGate

/-!
# Circle-extension axiom audit

This non-public leaf reports the assumptions used by the recursive circle model, corrected direct
control product, smooth self-inverse gate, and Boolean interpolation theorem.
-/

#print axioms Toffoli.CircleExtension.embed_injective
#print axioms Toffoli.CircleExtension.controlProduct_eq_prod_signal
#print axioms Toffoli.CircleExtension.contMDiff_controlProduct
#print axioms Toffoli.CircleExtension.gate_involutive
#print axioms Toffoli.CircleExtension.contMDiff_gate
#print axioms Toffoli.CircleExtension.gateDiffeomorph
#print axioms Toffoli.CircleExtension.gate_interpolates_thetaSucc
#print axioms Toffoli.CircleExtension.gateDiffeomorph_interpolates_thetaSucc
