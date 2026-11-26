module

public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace Staircase

/-- Slash-major vertex numbers. The slot order reverses on alternate slashes. -/
def Adj (n u v : Nat) : Prop :=
  u < 4*n ∧ v < 4*n ∧ (u/4+1 = v/4 ∨ v/4+1 = u/4) ∧
    (u%4 + v%4 = 3 ∨ u%4 + v%4 = 4)

instance (n u v : Nat) : Decidable (Adj n u v) := by unfold Adj; infer_instance

abbrev Stock := Multiset Nat

/-- An ordinary legal pebbling sequence, ending with a pebble at the chosen target. -/
inductive Reaches (edge : Nat → Nat → Prop) : Stock → Nat → Prop where
  | occupied {P t} : t ∈ P → Reaches edge P t
  | move {u v t rest} : edge u v → Reaches edge (v ::ₘ rest) t →
      Reaches edge (u ::ₘ u ::ₘ rest) t

def Solvable (n : Nat) (P : Stock) : Prop :=
  (∀ u ∈ P, u < 4*n) ∧ ∀ t < 4*n, Reaches (Adj n) P t

theorem Reaches.add {edge P t} (h : Reaches edge P t) (Q : Stock) :
    Reaches edge (P+Q) t := by
  induction h with
  | occupied ht => exact .occupied (Multiset.mem_add.mpr (.inl ht))
  | move ha _ ih =>
    simp only [Multiset.cons_add] at ih ⊢
    exact .move ha ih

theorem Reaches.mono {edge P Q t} (h : Reaches edge P t) (le : P ≤ Q) :
    Reaches edge Q t := by
  obtain ⟨extra,rfl⟩ := Multiset.le_iff_exists_add.mp le
  exact h.add extra

theorem Reaches.map {E D P t} (f : Nat → Nat) (hom : ∀ u v, E u v → D (f u) (f v))
    (h : Reaches E P t) : Reaches D (P.map f) (f t) := by
  induction h with
  | occupied ht => exact .occupied (Multiset.mem_map_of_mem f ht)
  | move ha _ ih =>
    simp only [Multiset.map_cons] at ih ⊢
    exact .move (hom _ _ ha) ih

theorem adj_embed {n N u v} (offset : Nat) (h : offset+n ≤ N) (a : Adj n u v) :
    Adj N (u+4*offset) (v+4*offset) := by
  unfold Adj at *
  omega

theorem reaches_embed {n N P t} (offset : Nat) (h : offset+n ≤ N)
    (a : Reaches (Adj n) P t) : Reaches (Adj N) (P.map (·+4*offset)) (t+4*offset) :=
  a.map _ (fun _ _ => adj_embed offset h)

theorem reaches_widen {n N P t} (h : n ≤ N) (a : Reaches (Adj n) P t) :
    Reaches (Adj N) P t := by
  simpa using reaches_embed 0 (N := N) (by omega) a

/-- The minimum number of pebbles in a distribution solving each target separately. -/
noncomputable def optimal (n : Nat) : Nat :=
  by
    classical
    exact if h : ∃ m, ∃ P : Stock, Solvable n P ∧ P.card = m then Nat.find h else 0

end Staircase
