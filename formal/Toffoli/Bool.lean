import Toffoli.Bool.Defs
import Toffoli.Bool.Finite
import Toffoli.Bool.Reindex
import Toffoli.Component.Dummy
import Toffoli.Component.OneToOne
import Toffoli.Component.Restriction
import Toffoli.Component.Tensor

/-!
# Finite Boolean API

Thin public facade for Boolean words, permutations, component wiring, face restriction, and dummy
components. Internal modules must import the exact leaves they use instead of this facade.
-/
