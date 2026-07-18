import Mathlib.Logic.Equiv.Fin.Basic
import Toffoli.Parity.Lift

/-!
# Sign of bare Boolean coordinate wiring

This leaf treats a coordinate permutation as an actual permutation of Boolean words, rather than
as conjugation used only to place another gate.  That distinction matters in arity two: swapping
the two coordinates is an odd permutation of the four Boolean words.  From arity three onward,
every bare coordinate permutation is even.
-/

namespace Toffoli

universe u

namespace BoolPerm

/-- Reindexing Boolean-word coordinates is a group homomorphism from coordinate permutations to
permutations of the Boolean cube. -/
def coordinateHom {ι : Type u} : Equiv.Perm ι →* BoolPerm ι where
  toFun := coordinatePerm
  map_one' := by
    apply Equiv.ext
    intro x
    rfl
  map_mul' e f := by
    apply Equiv.ext
    intro x
    rfl

/-- All nontrivial coordinate transpositions induce Boolean-word permutations with the same sign.
This is conjugacy of transpositions transported through `coordinateHom`. -/
theorem sign_coordinateSwap_congr {ι : Type u} [Fintype ι] [DecidableEq ι]
    {a b c d : ι} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.Perm.sign (coordinatePerm (Equiv.swap a b)) =
      Equiv.Perm.sign (coordinatePerm (Equiv.swap c d)) := by
  apply isConj_iff_eq.mp
  exact (Equiv.Perm.sign.comp coordinateHom).map_isConj
    (Equiv.Perm.isConj_swap hab hcd)

private theorem sign_prodComm_bool :
    Equiv.Perm.sign (Equiv.prodComm Bool Bool) = -1 := by
  rw [show Equiv.prodComm Bool Bool =
      Equiv.swap (false, true) (true, false) by
    apply Equiv.ext
    rintro ⟨a, b⟩
    cases a <;> cases b <;> decide]
  exact Equiv.Perm.sign_swap (by decide)

/-- Split the first two coordinates from a Boolean word on `Fin (2 + k)`. -/
def splitFirstTwo (k : ℕ) :
    BoolWord (Fin (2 + k)) ≃ (Bool × Bool) × BoolWord (Fin k) :=
  (Fin.appendEquiv 2 k).symm.trans
    ((finTwoArrowEquiv Bool).prodCongr (Equiv.refl (BoolWord (Fin k))))

@[simp]
theorem splitFirstTwo_fst_fst (k : ℕ) (x : BoolWord (Fin (2 + k))) :
    (splitFirstTwo k x).1.1 = x (Fin.castAdd k 0) :=
  rfl

@[simp]
theorem splitFirstTwo_fst_snd (k : ℕ) (x : BoolWord (Fin (2 + k))) :
    (splitFirstTwo k x).1.2 = x (Fin.castAdd k 1) :=
  rfl

@[simp]
theorem splitFirstTwo_snd (k : ℕ) (x : BoolWord (Fin (2 + k))) (i : Fin k) :
    (splitFirstTwo k x).2 i = x (Fin.natAdd 2 i) :=
  rfl

/-- The canonical swap of the first two coordinates of `Fin (2 + k)`. -/
def swapFirstTwoCoordinates (k : ℕ) : BoolPermN (2 + k) :=
  coordinatePerm (Equiv.swap (0 : Fin (2 + k)) (1 : Fin (2 + k)))

/-- Under `splitFirstTwo`, swapping the first two coordinates is product commutation on the first
two Boolean values and the identity on all remaining values. -/
theorem splitFirstTwo_swap (k : ℕ) (x : BoolWord (Fin (2 + k))) :
    splitFirstTwo k (swapFirstTwoCoordinates k x) =
      Equiv.prodCongr (Equiv.prodComm Bool Bool)
        (Equiv.refl (BoolWord (Fin k))) (splitFirstTwo k x) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [splitFirstTwo_fst_fst, Equiv.prodCongr_apply]
      simp [swapFirstTwoCoordinates, coordinatePerm,
        BoolWord.reindex, Equiv.swap_apply_def]
      congr 1
      rw [if_pos (by rfl)]
      apply Fin.ext
      change 1 % (2 + k) = 1
      exact Nat.mod_eq_of_lt (by omega)
    · simp only [splitFirstTwo_fst_snd, Equiv.prodCongr_apply]
      simp [swapFirstTwoCoordinates, coordinatePerm,
        BoolWord.reindex, Equiv.swap_apply_def]
      congr 1
      rw [if_neg (by
        intro h
        have hval := congrArg Fin.val h
        change 1 = 0 at hval
        omega), if_pos (by
        apply Fin.ext
        change 1 = 1 % (2 + k)
        rw [Nat.mod_eq_of_lt (by omega)])]
      apply Fin.ext
      change 0 = 0 % (2 + k)
      simp
  · funext i
    simp only [splitFirstTwo_snd, Equiv.prodCongr_apply]
    simp [swapFirstTwoCoordinates, coordinatePerm,
      BoolWord.reindex, Equiv.swap_apply_def]
    congr 1
    rw [if_neg (by
      intro h
      have hval := congrArg Fin.val h
      change 2 + i.val = 0 at hval
      omega), if_neg (by
      intro h
      have hval := congrArg Fin.val h
      have hlt : 1 < 2 + k := by omega
      simp [Nat.mod_eq_of_lt hlt] at hval
      omega)]

private theorem sign_swapFirstTwoCoordinates (k : ℕ) :
    Equiv.Perm.sign (swapFirstTwoCoordinates k) = (-1) ^ (2 ^ k) := by
  calc
    Equiv.Perm.sign (swapFirstTwoCoordinates k) =
        Equiv.Perm.sign (Equiv.prodCongr (Equiv.prodComm Bool Bool)
          (Equiv.refl (BoolWord (Fin k)))) :=
      Equiv.Perm.sign_eq_sign_of_equiv _ _ (splitFirstTwo k)
        (splitFirstTwo_swap k)
    _ = Equiv.Perm.sign (Equiv.prodComm Bool Bool) ^
          Fintype.card (BoolWord (Fin k)) := by
      rw [Equiv.prodCongr_refl_right, Equiv.Perm.sign_prodCongrLeft]
      simp
    _ = (-1) ^ (2 ^ k) := by
      rw [sign_prodComm_bool, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- A transposition of two coordinates of an `(2 + k)`-bit word induces `2 ^ k` transpositions
of Boolean words, so its sign is `(-1) ^ (2 ^ k)`. -/
theorem sign_coordinateSwap (k : ℕ) {a b : Fin (2 + k)} (hab : a ≠ b) :
    Equiv.Perm.sign (coordinatePerm (Equiv.swap a b)) = (-1) ^ (2 ^ k) :=
  (sign_coordinateSwap_congr hab (by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 1 % (2 + k) at hval
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega)).trans
    (sign_swapFirstTwoCoordinates k)

/-- On at least three coordinates, every bare coordinate permutation acts evenly on Boolean
words.  The hypothesis `0 < k` is exactly the condition `3 ≤ 2 + k`. -/
theorem sign_coordinatePerm_eq_one (k : ℕ) (hk : 0 < k)
    (e : Equiv.Perm (Fin (2 + k))) :
    Equiv.Perm.sign (coordinatePerm e) = 1 := by
  induction e using Equiv.Perm.swap_induction_on with
  | one =>
      rw [show coordinatePerm (1 : Equiv.Perm (Fin (2 + k))) = 1 by
        apply Equiv.ext
        intro x
        rfl]
      exact Equiv.Perm.sign_one
  | swap_mul f a b hab ih =>
      change Equiv.Perm.sign (coordinateHom (Equiv.swap a b * f)) = 1
      rw [coordinateHom.map_mul, Equiv.Perm.sign_mul]
      change Equiv.Perm.sign (coordinatePerm (Equiv.swap a b)) *
        Equiv.Perm.sign (coordinatePerm f) = 1
      rw [sign_coordinateSwap k hab, ih]
      have hpow : (-1 : ℤˣ) ^ (2 ^ k) = 1 :=
        (even_two.pow_of_ne_zero (Nat.ne_of_gt hk)).neg_one_pow
      simpa using hpow

end BoolPerm

end Toffoli
