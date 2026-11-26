module

public import Staircase.Graph
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Algebra.Order.Monoid.Multiset

@[expose] public section
namespace Staircase

inductive Tree where
  | token (v : Nat)
  | merge (v : Nat) (a b : Tree)
deriving DecidableEq

def Tree.site : Tree → Nat
  | .token v | .merge v _ _ => v

def Tree.stock : Tree → Stock
  | .token v => {v}
  | .merge _ a b => a.stock+b.stock

def Tree.Legal (E : Nat → Nat → Prop) : Tree → Prop
  | .token _ => True
  | .merge v a b => a.Legal E ∧ b.Legal E ∧ a.site=b.site ∧ E a.site v

private theorem extractTree {F : Multiset Tree} {t : Nat} {P : Stock}
    (h : F.map Tree.site = t ::ₘ P) :
    ∃ A F', F=A ::ₘ F' ∧ A.site=t ∧ F'.map Tree.site=P := by
  obtain ⟨A,ha,root,rest⟩ := (Multiset.map_eq_cons ..).mpr h
  exact ⟨A,F.erase A,(Multiset.cons_erase ha).symm,root,rest⟩

theorem Reaches.tree_from {E P t} (h : Reaches E P t) (F : Multiset Tree)
    (roots : F.map Tree.site = P) (legal : ∀ a ∈ F, Tree.Legal E a) :
    ∃ T : Tree, T.site=t ∧ T.Legal E ∧ T.stock ≤ F.bind Tree.stock := by
  induction h generalizing F with
  | occupied ht =>
    rw [← roots] at ht
    obtain ⟨T,hT,e⟩ := Multiset.mem_map.mp ht
    exact ⟨T,e,legal _ hT,Multiset.le_bind _ hT⟩
  | @move u v t rest edge _ ih =>
    obtain ⟨A,F₁,rfl,ra,r₁⟩ := extractTree roots
    obtain ⟨B,F₂,rfl,rb,r₂⟩ := extractTree r₁
    let C := Tree.merge v A B
    have good : C.Legal E := ⟨legal _ (by simp),legal _ (by simp),ra.trans rb.symm,ra ▸ edge⟩
    obtain ⟨T,target,ok,cost⟩ := ih (C ::ₘ F₂) (by simp [C,Tree.site,r₂]) (by
      intro a ha
      rcases Multiset.mem_cons.mp ha with rfl | h₂
      · exact good
      · exact legal a (by simp [h₂]))
    exact ⟨T,target,ok,by simpa [C,Tree.stock,add_assoc] using cost⟩

theorem Reaches.tree {E P t} (h : Reaches E P t) :
    ∃ T : Tree, T.site=t ∧ T.Legal E ∧ T.stock ≤ P := by
  have singles : (P.bind fun x => ({x} : Stock)) = P := by
    clear h
    induction P using Multiset.induction_on with
    | empty => rfl
    | cons a s ih => simp [ih]
  simpa [Multiset.map_map,Function.comp_def,Tree.site,Tree.stock,Multiset.bind_map,singles] using
    h.tree_from (P.map Tree.token) (by simp [Multiset.map_map,Function.comp_def,Tree.site])
      (by intro a ha; obtain ⟨_,_,rfl⟩ := Multiset.mem_map.mp ha; trivial)

end Staircase
