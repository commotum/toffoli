import Toffoli.Bool.Defs

/-!
# Faces of Boolean cubes

A face is a partial Boolean assignment. `none` leaves a coordinate free; `some b` fixes it to
`b`. The definition is valid for infinite and empty index types, although later permutation
theorems generally use finite indices.
-/

namespace Toffoli

universe u v

/-- A partial assignment specifying a face of a Boolean cube. -/
abbrev Face (ι : Type u) := ι → Option Bool

namespace Face

variable {ι : Type u} {κ : Type v}

/-- A word belongs to a face when it agrees with every fixed coordinate. -/
def Mem (face : Face ι) (x : BoolWord ι) : Prop :=
  ∀ i b, face i = some b → x i = b

/-- The set of Boolean words belonging to a face. -/
def carrier (face : Face ι) : Set (BoolWord ι) :=
  {x | face.Mem x}

/-- The subtype of Boolean words belonging to a face. -/
abbrev Points (face : Face ι) := {x : BoolWord ι // x ∈ face.carrier}

@[simp]
theorem mem_carrier_iff (face : Face ι) (x : BoolWord ι) : x ∈ face.carrier ↔ face.Mem x :=
  Iff.rfl

/-- The unconstrained face. -/
def free : Face ι :=
  fun _ => none

@[simp]
theorem mem_free (x : BoolWord ι) : x ∈ (free : Face ι).carrier := by
  intro i b h
  simp [free] at h

/-- The zero-dimensional face containing exactly one specified word. -/
def point (x : BoolWord ι) : Face ι :=
  fun i => some (x i)

@[simp]
theorem mem_point_iff (x y : BoolWord ι) : y ∈ (point x).carrier ↔ y = x := by
  constructor
  · intro h
    funext i
    exact h i (x i) rfl
  · rintro rfl i b h
    simpa [point] using h

/-- The face of a disjoint component sum obtained by fixing every right coordinate to `c`. -/
def right (c : BoolWord κ) : Face (ι ⊕ κ) :=
  Sum.elim (fun _ => none) (fun k => some (c k))

@[simp]
theorem mem_right_iff (c : BoolWord κ) (x : BoolWord (ι ⊕ κ)) :
    x ∈ (right c).carrier ↔ ∀ k, x (Sum.inr k) = c k := by
  constructor
  · intro h k
    exact h (Sum.inr k) (c k) rfl
  · intro h i b hi
    cases i with
    | inl i => simp [right] at hi
    | inr k =>
        have hcb : c k = b := by simpa [right] using hi
        exact (h k).trans hcb

end Face

end Toffoli
