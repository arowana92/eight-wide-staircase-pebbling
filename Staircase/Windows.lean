module

public import Staircase.Columns
public import Mathlib.Algebra.Order.Monoid.Multiset

@[expose] public section
namespace Staircase

def foldLeft (u : Nat) := if u=1 then 1 else if u<6 then 0 else u-4
def foldRight (k u : Nat) := if u<4*k+2 then u else 1

theorem trim_left {a b c cs} (hc : ∀ u ∈ c, u < 4) (h : Served a (c::cs) b) :
    Served (c.card+a/2) cs b := by
  intro t ht
  have gl := h (t+4) (by simp only [List.length_cons]; omega)
  simp only [List.length_cons] at gl
  have r := gl.pool 0 0 foldLeft
    (by intro u e; unfold WAdj Adj at e; unfold foldLeft; (repeat' split) <;> omega)
    (by intro v e; unfold WAdj Adj at e; unfold foldLeft; (repeat' split) <;> omega)
    (D := WAdj cs.length)
    (by
      intro u v hu hv e
      rcases e with ⟨pu,pv,adj⟩ | ⟨eq,_,_⟩ | ⟨eq,_,_⟩ | ⟨eq,_,_,_⟩ | ⟨eq,_,_,_⟩
      · unfold Adj at adj
        by_cases au : u<6
        · have av : 6≤v := by omega
          apply Or.inr ∘ Or.inl
          simp [foldLeft,show u≠1 by omega,show v≠1 by omega,au,show ¬v<6 by omega]
          omega
        · by_cases av : v<6
          · apply Or.inr ∘ Or.inr ∘ Or.inl
            simp [foldLeft,show u≠1 by omega,show v≠1 by omega,au,av]
            omega
          · apply Or.inl
            simp only [foldLeft,ite_eq_right (show u≠1 by omega),ite_eq_right (show v≠1 by omega),
              ite_eq_right au,ite_eq_right av,Adj]
            omega
      · contradiction
      · contradiction
      · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
        simp [foldLeft,eq,show v≠1 by omega,show ¬v<6 by omega]
        omega
      · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
        simp [foldLeft,eq,show u≠1 by omega,show ¬u<6 by omega]
        omega)
    (by omega)
  rw [show foldLeft (t+4+2) = t+2 by unfold foldLeft; (repeat' split) <;> omega] at r
  unfold layout at r ⊢
  rw [pool_separate] at r
  · simp only [flatten, Multiset.map_add, Multiset.map_replicate, Multiset.map_map] at r
    have h₁ : c.map (foldLeft ∘ (·+2)) = Multiset.replicate c.card 0 := by
      rw [← Multiset.map_const]
      apply Multiset.map_congr rfl
      intro u hu
      have := hc u hu
      dsimp [foldLeft]
      (repeat' split) <;> omega
    have h₂ : (flatten cs).map (foldLeft ∘ (·+2) ∘ (·+4)) = (flatten cs).map (·+2) := by
      apply Multiset.map_congr rfl
      intro u _
      dsimp [foldLeft]
      (repeat' split) <;> omega
    simpa only [Function.comp_assoc,h₁,h₂,show foldLeft 1=1 by decide, Multiset.replicate_add,
      Multiset.add_assoc,Multiset.add_comm,add_left_comm] using r
  · simp [Multiset.mem_replicate]

theorem trim_right {a b c cs} (good : ValidCols cs)
    (h : Served a (cs++[c]) b) : Served a cs (c.card+b/2) := by
  intro t ht
  have gl := h t (by simp; omega)
  simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at gl
  have r := gl.pool 1 1 (foldRight cs.length)
    (by intro u e; unfold WAdj Adj at e; unfold foldRight; split <;> omega)
    (by intro v e; unfold WAdj Adj at e; unfold foldRight; split <;> omega)
    (D := WAdj cs.length)
    (by
      intro u v hu hv e
      unfold WAdj Adj at *
      unfold foldRight
      (repeat' split) <;> omega)
    (by omega)
  rw [show foldRight cs.length (t+2) = t+2 by simp [foldRight,ht]] at r
  unfold layout at r ⊢
  rw [add_left_comm, pool_separate] at r
  · simp only [flatten_append, flatten, Multiset.map_zero, Multiset.add_zero, Multiset.map_add,
      Multiset.map_replicate, Multiset.map_map] at r
    have h₁ : c.map (foldRight cs.length ∘ (·+2) ∘ (·+4*cs.length)) = Multiset.replicate c.card 1 := by
      rw [← Multiset.map_const]
      apply Multiset.map_congr rfl
      intro u _
      dsimp [foldRight]
      split <;> omega
    have h₂ : (flatten cs).map (foldRight cs.length ∘ (·+2)) = (flatten cs).map (·+2) := by
      apply Multiset.map_congr rfl
      intro u hu
      have := flatten_bound good hu
      dsimp [foldRight]
      split <;> omega
    simpa only [Function.comp_assoc,h₁,h₂,show foldRight cs.length 0=0 by unfold foldRight; split <;> omega,
      Multiset.replicate_add,Multiset.add_assoc,Multiset.add_comm,add_left_comm] using r
  · simp [Multiset.mem_replicate]

end Staircase
