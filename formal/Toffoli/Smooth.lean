import Toffoli.Smooth.Extension
import Toffoli.Smooth.Synthesis.Universality

/-!
# Smooth extensions

This thin public facade exposes the direct circle-valued diffeomorphic extension of every finite
Boolean permutation and the qualified three-bit Toffoli extension obtained by fixing the universal
auxiliary face, restricting the ambient circuit, and projecting/deleting returned auxiliaries.

The discrete root facade remains separate for compile-time isolation: ordinary discrete builds do
not import manifold dependencies or the terminal smooth synthesis proof.
-/
