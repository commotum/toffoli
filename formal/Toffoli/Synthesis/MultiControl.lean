import Mathlib.Data.List.OfFn
import Toffoli.Circuit.ThreeBit
import Toffoli.Synthesis.FaceRealization
import Toffoli.Synthesis.Resources

/-!
# Clean synthesis of generalized positive-control gates

This leaf constructs the paper's higher-arity AND/NAND permutations from explicitly placed
three-bit Toffoli instructions.  The two left auxiliary coordinates are persistent `true` enable
bits; the remaining auxiliary coordinates are initially `false` work bits.  At arity at least
four, a forward ladder computes prefix conjunctions, one instruction acts on the data target,
and the exact reversed ladder uncomputes every work bit.

Circuit lists are in execution order: their leftmost instruction acts first.
-/

namespace Toffoli

namespace Synthesis

namespace MultiControl

/-- The three-bit instruction implementing NOT on the sole data bit. -/
def notInstruction : ThreeBitInstruction (UniversalIndex 1) :=
  ThreeBitInstruction.ofDistinct (enableIndex 0) (enableIndex 1) (dataIndex 0)
    (by simp [enableIndex]) (by simp [enableIndex, dataIndex]) (by simp [enableIndex, dataIndex])

/-- The three-bit instruction implementing CNOT on two data bits. -/
def cnotInstruction : ThreeBitInstruction (UniversalIndex 2) :=
  ThreeBitInstruction.ofDistinct (dataIndex 0) (enableIndex 0) (dataIndex 1)
    (by simp [dataIndex, enableIndex]) (by simp [dataIndex]) (by simp [dataIndex, enableIndex])

/-- The canonical three-bit data instruction. -/
def threeInstruction : ThreeBitInstruction (UniversalIndex 3) :=
  ThreeBitInstruction.ofDistinct (dataIndex 0) (dataIndex 1) (dataIndex 2)
    (by simp [dataIndex]) (by simp [dataIndex]) (by simp [dataIndex])

/-- The first prefix instruction computes `x₀ ∧ x₁` into work coordinate zero. -/
def firstPrefix (k : ℕ) : ThreeBitInstruction (UniversalIndex (k + 4)) :=
  ThreeBitInstruction.ofDistinct (dataIndex 0) (dataIndex 1) (workIndex ⟨0, by omega⟩)
    (by simp [dataIndex]) (by simp [dataIndex, workIndex]) (by simp [dataIndex, workIndex])

/-- A later prefix instruction extends the previous conjunction by one data control. -/
def nextPrefix (k : ℕ) (i : Fin k) : ThreeBitInstruction (UniversalIndex (k + 4)) :=
  ThreeBitInstruction.ofDistinct (workIndex i.castSucc) (dataIndex ⟨i + 2, by omega⟩)
    (workIndex i.succ) (by simp [workIndex, dataIndex])
    (by
      simp only [workIndex, ne_eq, Sum.inr.injEq]
      intro h
      have := congrArg Fin.val h
      simp at this)
    (by simp [workIndex, dataIndex])

/-- Prefix instruction number `i`, numbered from zero in execution order. -/
def prefixInstruction (k : ℕ) (i : Fin (k + 1)) :
    ThreeBitInstruction (UniversalIndex (k + 4)) :=
  Fin.cases (firstPrefix k) (nextPrefix k) i

/-- The target instruction after all `k + 1` prefix work bits have been computed. -/
def targetInstruction (k : ℕ) : ThreeBitInstruction (UniversalIndex (k + 4)) :=
  ThreeBitInstruction.ofDistinct (workIndex (Fin.last k)) (dataIndex ⟨k + 2, by omega⟩)
    (dataIndex (Fin.last (k + 3))) (by simp [workIndex, dataIndex])
    (by simp [workIndex, dataIndex])
    (by
      simp only [dataIndex, ne_eq, Sum.inl.injEq]
      intro h
      have := congrArg Fin.val h
      simp at this)

/-- The forward prefix-conjunction ladder. -/
def computeWord (k : ℕ) : List (ThreeBitInstruction (UniversalIndex (k + 4))) :=
  List.ofFn (prefixInstruction k)

/-- The all-arity clean circuit word.  Arity zero is deliberately the empty identity word. -/
def word : (n : ℕ) → List (ThreeBitInstruction (UniversalIndex n))
  | 0 => []
  | 1 => [notInstruction]
  | 2 => [cnotInstruction]
  | 3 => [threeInstruction]
  | k + 4 => computeWord k ++ targetInstruction k :: (computeWord k).reverse

/-- Ambient permutation evaluated from the explicit left-to-right circuit word. -/
def perm (n : ℕ) : BoolPerm (UniversalIndex n) :=
  ThreeBitCircuit.eval (word n)

end MultiControl

end Synthesis

end Toffoli
