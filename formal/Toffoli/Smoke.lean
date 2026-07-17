/-!
# Project smoke test

This low-dependency leaf validates the pinned Lean/mathlib setup. It deliberately contains no
project definitions or claims from Toffoli's paper.
-/

import Mathlib.GroupTheory.Perm.Basic

#check Equiv.Perm
#check Equiv.swap
