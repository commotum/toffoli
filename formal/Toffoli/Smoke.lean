import Mathlib.Logic.Equiv.Basic

/-!
# Project smoke test

This low-dependency leaf validates the pinned Lean/mathlib setup. It deliberately contains no
project definitions or claims from Toffoli's paper.
-/

example : Equiv.Perm Bool := Equiv.refl Bool

example : Equiv.Perm Bool := Equiv.swap false true
