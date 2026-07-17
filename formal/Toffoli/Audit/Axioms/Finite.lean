import Toffoli.Bool.Finite
import Toffoli.Component.Dummy
import Toffoli.Component.OneToOne

/-!
# Finite-core axiom audit

This non-public diagnostic leaf reports the axioms used by representative finite-core
declarations. Its terminal imports cover the finite cardinality, reindexing, tensor, face
restriction, certified dummy deletion, and one-to-one circuit dependency graph without importing
the public facade or later smooth-manifold developments.
-/

#print axioms Toffoli.card_boolWord
#print axioms Toffoli.boolPermN_zero_eq_refl
#print axioms Toffoli.BoolWord.reindex_trans
#print axioms Toffoli.BoolPerm.reindex_serial
#print axioms Toffoli.BoolPerm.tensor_serial
#print axioms Toffoli.Component.restrictEquiv
#print axioms Toffoli.Component.restrictFaces_apply_val
#print axioms Toffoli.Component.permCongr_fixRightEquiv
#print axioms Toffoli.Component.RightDummy.reconstruct
#print axioms Toffoli.OneToOneCircuit.eval_reindex_reindex
#print axioms Toffoli.OneToOneCircuit.eval_wire_serial
