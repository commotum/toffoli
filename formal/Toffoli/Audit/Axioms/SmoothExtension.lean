import Toffoli.Smooth.Extension

/-!
# Direct smooth-extension axiom audit

This diagnostic leaf reports assumptions from the recursive coordinate API through atomic smooth
edges, smooth word composition, and the main connected-circle extension theorem.
-/

/-! ## Recursive circle coordinates -/

#print axioms Toffoli.CircleExtension.coord_assemble
#print axioms Toffoli.CircleExtension.assemble_coord
#print axioms Toffoli.CircleExtension.contMDiff_coord
#print axioms Toffoli.CircleExtension.contMDiff_assemble
#print axioms Toffoli.CircleExtension.contMDiff_iff_coord

/-! ## Atomic circle extension -/

#print axioms Toffoli.CircleExtension.atomicActivation_embed
#print axioms Toffoli.CircleExtension.contMDiff_atomicActivation
#print axioms Toffoli.CircleExtension.atomicMap_involutive
#print axioms Toffoli.CircleExtension.contMDiff_atomicMap
#print axioms Toffoli.CircleExtension.atomicDiffeomorph
#print axioms Toffoli.CircleExtension.atomicDiffeomorph_interpolates

/-! ## Smooth atomic words -/

#print axioms Toffoli.CircleExtension.atomicStepDiffeomorph_interpolates
#print axioms Toffoli.CircleExtension.evalAtomicWord_append
#print axioms Toffoli.CircleExtension.evalAtomicWord_interpolates

/-! ## Arbitrary permutations, empty arity, and the connected witness -/

#print axioms Toffoli.CircleExtension.extension_interpolates
#print axioms Toffoli.CircleExtension.exists_extension
#print axioms Toffoli.CircleExtension.extension_zero_eq_refl
#print axioms Toffoli.CircleExtension.refl_zero_interpolates
#print axioms Toffoli.CircleExtension.connected_circle_witness
