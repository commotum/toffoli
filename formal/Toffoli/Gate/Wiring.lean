import Mathlib.Data.Finset.Image
import Toffoli.Bool.Reindex
import Toffoli.Component.Tensor
import Toffoli.Gate.Toffoli

/-!
# Wiring generalized Toffoli gates

This leaf keeps gate transport and unused-coordinate extension above the cheap gate definition.
Transporting a gate specification along an equivalence is proved to agree with conjugating its
permutation. Mapping into a left summand is proved to agree with tensoring by an identity.
-/

namespace Toffoli

universe u v

namespace ToffoliGate

variable {ι : Type u} {κ : Type v}

/-- Map the target and controls of a gate along an embedding of coordinate types. -/
def map (f : ι ↪ κ) (g : ToffoliGate ι) : ToffoliGate κ where
  controls := g.controls.map f
  target := f g.target
  target_not_mem := by
    intro h
    obtain ⟨i, hi, hit⟩ := Finset.mem_map.1 h
    exact g.target_not_mem (f.injective hit ▸ hi)

@[simp]
theorem map_target (f : ι ↪ κ) (g : ToffoliGate ι) : (g.map f).target = f g.target :=
  rfl

@[simp]
theorem map_active_iff (f : ι ↪ κ) (g : ToffoliGate ι) (x : BoolWord κ) :
    (g.map f).Active x ↔ g.Active (fun i => x (f i)) := by
  constructor
  · intro h i hi
    exact h (f i) (Finset.mem_map.2 ⟨i, hi, rfl⟩)
  · intro h k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hk
    exact h i hi

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem map_equiv_active_reindex (e : ι ≃ κ) (g : ToffoliGate ι) (x : BoolWord ι) :
    (g.map e.toEmbedding).Active (BoolWord.reindex e x) ↔ g.Active x := by
  rw [map_active_iff]
  constructor <;> intro h i hi
  · simpa using h i hi
  · simpa using h i hi

theorem run_map_equiv_reindex (e : ι ≃ κ) (g : ToffoliGate ι) (x : BoolWord ι) :
    (g.map e.toEmbedding).run (BoolWord.reindex e x) = BoolWord.reindex e (g.run x) := by
  funext k
  by_cases hk : k = e g.target
  · subst k
    change
      (g.map e.toEmbedding).run (BoolWord.reindex e x) (g.map e.toEmbedding).target =
        BoolWord.reindex e (g.run x) (e g.target)
    rw [(g.map e.toEmbedding).run_target]
    simp
  · have hi : e.symm k ≠ g.target := by
      intro hi
      apply hk
      simpa using congrArg e hi
    have hmk : k ≠ (g.map e.toEmbedding).target := by simpa using hk
    rw [(g.map e.toEmbedding).run_of_ne_target _ hmk]
    simp only [BoolWord.reindex_apply]
    rw [g.run_of_ne_target _ hi]

/-- Mapping a gate along an index equivalence agrees with permutation conjugation. -/
theorem perm_map_equiv (e : ι ≃ κ) (g : ToffoliGate ι) :
    (g.map e.toEmbedding).perm = BoolPerm.reindex e g.perm := by
  apply Equiv.ext
  intro y
  funext k
  rw [perm_apply, BoolPerm.reindex_apply]
  have h := congrFun (g.run_map_equiv_reindex e ((BoolWord.reindex e).symm y)) k
  simpa [BoolWord.reindex] using h

/-- Place a gate into the left summand of a disjoint coordinate type. -/
def inl (g : ToffoliGate ι) : ToffoliGate (ι ⊕ κ) :=
  g.map Function.Embedding.inl

omit [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem inl_active_iff (g : ToffoliGate ι) (x : BoolWord (ι ⊕ κ)) :
    (g.inl (κ := κ)).Active x ↔ g.Active (fun i => x (Sum.inl i)) :=
  g.map_active_iff Function.Embedding.inl x

@[simp]
theorem inl_run_inl (g : ToffoliGate ι) (x : BoolWord (ι ⊕ κ)) (i : ι) :
    (g.inl (κ := κ)).run x (Sum.inl i) = g.run (fun j => x (Sum.inl j)) i := by
  by_cases hi : i = g.target
  · subst i
    change
      (g.inl (κ := κ)).run x (g.inl (κ := κ)).target =
        g.run (fun j => x (Sum.inl j)) g.target
    rw [(g.inl (κ := κ)).run_target]
    simp only [inl, map_target]
    rw [g.run_target]
    rw [if_congr (g.map_active_iff Function.Embedding.inl x) rfl rfl]
    rfl
  · have hmi : Sum.inl i ≠ (g.inl (κ := κ)).target := by
      intro hEq
      apply hi
      change Sum.inl i = Sum.inl g.target at hEq
      exact Sum.inl_injective hEq
    rw [(g.inl (κ := κ)).run_of_ne_target _ hmi]
    exact (g.run_of_ne_target (fun j : ι => x (Sum.inl j)) hi).symm

@[simp]
theorem inl_run_inr (g : ToffoliGate ι) (x : BoolWord (ι ⊕ κ)) (k : κ) :
    (g.inl (κ := κ)).run x (Sum.inr k) = x (Sum.inr k) :=
  (g.inl (κ := κ)).run_of_ne_target x Sum.inr_ne_inl

/-- Mapping into a left summand agrees with extending the permutation by unused coordinates. -/
theorem perm_inl (g : ToffoliGate ι) :
    (g.inl (κ := κ)).perm = BoolPerm.extendRight g.perm κ := by
  apply Equiv.ext
  intro x
  funext i
  cases i <;> simp

end ToffoliGate

end Toffoli
