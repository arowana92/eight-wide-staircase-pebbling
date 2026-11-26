module

public import Staircase.Arithmetic
public import Staircase.UpperData

@[expose] public section
namespace Staircase

def anchor : Stock := ↑([2,2,2,2] : List Nat)
def newPiles : Stock := ↑([2,2,2,2,7] : List Nat)
def Anchored (n m : Nat) : Prop :=
  ∃ P : Stock, Solvable n P ∧ P.card = m ∧ anchor ≤ P

theorem extend_anchored {n m} (h : Anchored n m) (hn : 1 ≤ n) : Anchored (n+4) (m+5) := by
  obtain ⟨P, ⟨valid,sol⟩, mass, pile⟩ := h
  let Q := P.map (·+16)
  refine ⟨newPiles+Q, ⟨?_,?_⟩, ?_, ?_⟩
  · intro u hu
    rcases Multiset.mem_add.mp hu with h₁ | h₂
    · simp [newPiles] at h₁
      omega
    · obtain ⟨v,hv,rfl⟩ := Multiset.mem_map.mp h₂
      have := valid v hv
      omega
  · intro t ht
    by_cases small : t < 16
    · have h₁ := reaches_widen (N := n+4) (by omega : 5 ≤ n+4)
          (UpperData.extension_reaches t small)
      apply h₁.mono
      have h₂ : anchor.map (·+16) ≤ Q := Multiset.map_le_map pile
      exact Multiset.add_le_add_left (s := newPiles) h₂
    · have old := reaches_embed (N := n+4) 4 (by omega) (sol (t-16) (by omega))
      have eq : t-16+4*4=t := by omega
      rw [eq] at old
      exact old.mono (Multiset.le_add_left _ _)
  · simp [Q, newPiles, mass, Nat.add_comm]
  · exact le_trans (by decide : anchor ≤ newPiles) (Multiset.le_add_right _ _)

theorem upper_bases (n : Nat) (lo : 3 ≤ n) (hi : n ≤ 6) :
    ∃ m, Anchored n m ∧ m ≤ (5*n+3)/4+3 := by
  have cases : n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨7, ⟨↑UpperData.base3, ⟨by decide, UpperData.base3_reaches⟩, by decide, by decide⟩, by decide⟩
    | exact ⟨8, ⟨↑UpperData.base4, ⟨by decide, UpperData.base4_reaches⟩, by decide, by decide⟩, by decide⟩
    | exact ⟨10, ⟨↑UpperData.base5, ⟨by decide, UpperData.base5_reaches⟩, by decide, by decide⟩, by decide⟩
    | exact ⟨11, ⟨↑UpperData.base6, ⟨by decide, UpperData.base6_reaches⟩, by decide, by decide⟩, by decide⟩

theorem upper_placement {n : Nat} (pos : 0 < n) :
    ∃ P : Stock, Solvable n P ∧ P.card ≤ (5*n+3)/4+3 := by
  by_cases small : n ≤ 2
  · have cases : n=1 ∨ n=2 := by omega
    rcases cases with rfl | rfl
    · exact ⟨↑UpperData.base1, ⟨by decide, UpperData.base1_reaches⟩, by decide⟩
    · exact ⟨↑UpperData.base2, ⟨by decide, UpperData.base2_reaches⟩, by decide⟩
  · let pred := fun k m => 3 ≤ k ∧ Anchored k m
    have bases : ∀ k, 3 ≤ k → k ≤ 6 → ∃ m, pred k m ∧ m ≤ (5*k+3)/4+3 := by
      intro k lo hi
      obtain ⟨m, h, bd⟩ := upper_bases k lo hi
      exact ⟨m,⟨lo,h⟩,bd⟩
    have step : ∀ k m, pred k m → pred (k+4) (m+5) := by
      intro k m ⟨hk, hp⟩
      exact ⟨by omega, extend_anchored hp (by omega)⟩
    obtain ⟨m, ⟨_,P,hP,rfl,_⟩, bd⟩ := extend_upper bases step n (by omega)
    exact ⟨P,hP,bd⟩

theorem optimal_spec {n : Nat} (hn : 0 < n) :
    (∃ P : Stock, Solvable n P ∧ P.card = optimal n) ∧
    ∀ P : Stock, Solvable n P → optimal n ≤ P.card := by
  classical
  obtain ⟨P,sol,_⟩ := upper_placement hn
  have ex : ∃ m, ∃ Q : Stock, Solvable n Q ∧ Q.card = m := ⟨_,P,sol,rfl⟩
  simp only [optimal, dite_eq_left ex]
  exact ⟨Nat.find_spec ex, fun Q hQ => Nat.find_min' ex ⟨Q,hQ,rfl⟩⟩

theorem optimal_upper {n : Nat} (hn : 0 < n) : optimal n ≤ (5*n+3)/4+3 := by
  obtain ⟨P,h,b⟩ := upper_placement hn
  exact ((optimal_spec hn).2 P h).trans b

end Staircase
