module

public import Staircase.Graph

@[expose] public section
namespace Staircase

/-- Replay a proposed path against a concrete list of initial tokens. -/
def plays (n t : Nat) (P : List Nat) : List (Nat × Nat) → Bool
  | [] => decide (t ∈ P)
  | (u,v) :: steps =>
    decide (Adj n u v ∧ u ∈ P ∧ u ∈ P.erase u) &&
      plays n t (v :: (P.erase u).erase u) steps

theorem plays_sound {n t : Nat} (steps : List (Nat × Nat)) (P : List Nat)
    (h : plays n t P steps = true) : Reaches (Adj n) (↑P) t := by
  induction steps generalizing P with
  | nil => exact .occupied (of_decide_eq_true h)
  | cons move tail ih =>
    obtain ⟨u,v⟩ := move
    simp only [plays, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨adj,h₁,h₂⟩,rest⟩ := h
    have a := ih _ rest
    have eq₁ := Multiset.cons_erase (s := (↑P : Stock)) (a := u) h₁
    have eq₂ := Multiset.cons_erase (s := (↑(P.erase u) : Stock)) (a := u) h₂
    change Reaches _ (v ::ₘ (↑((P.erase u).erase u) : Stock)) _ at a
    have b := Reaches.move adj a
    change u ::ₘ (↑((P.erase u).erase u) : Stock) = _ at eq₂
    change u ::ₘ (↑(P.erase u) : Stock) = _ at eq₁
    rw [eq₂,eq₁] at b
    exact b

def covers (n k : Nat) (P : List Nat) (paths : List (List (Nat × Nat))) : Prop :=
  ∀ i : Fin k, plays n i P (paths[i.val]?.getD []) = true

instance (n k P paths) : Decidable (covers n k P paths) := by unfold covers; infer_instance

theorem covers_sound {n k P paths} (h : covers n k P paths) (t : Nat) (ht : t < k) :
    Reaches (Adj n) (↑P) t :=
  plays_sound _ P (h ⟨t, ht⟩)

end Staircase
