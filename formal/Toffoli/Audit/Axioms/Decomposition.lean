import Toffoli.Perm.Decomposition

/-!
# Atomic-decomposition axiom audit

This diagnostic leaf reports the assumptions used by the Gray-path, exact endpoint-word, gate
interpretation, and arbitrary finite-permutation theorems.
-/

#print axioms Toffoli.GrayReachable.all
#print axioms Toffoli.IsEndpointWord.exists_word
#print axioms Toffoli.IsEndpointWord.eval_eq_swap
#print axioms Toffoli.ToffoliGate.edgeNormalizer_permCongr_atomicEdge
#print axioms Toffoli.ToffoliGate.atomicEdge_eq_edgeNormalizer_permCongr_andNand
#print axioms Toffoli.AtomicWord.exists_eval_eq
#print axioms Toffoli.AtomicWord.eval_decompose
