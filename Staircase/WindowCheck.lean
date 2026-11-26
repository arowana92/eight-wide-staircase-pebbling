module

public import Staircase.Boxes

@[expose] public section
namespace Staircase

def binStock : Nat → List Nat → Stock
  | _, [] => 0
  | start, p::ps => Multiset.replicate p start + binStock (start+1) ps

private theorem bin_lower {u start ps} (h : u ∈ binStock start ps) : start ≤ u := by
  induction ps generalizing start with
  | nil => simp [binStock] at h
  | cons p ps ih =>
    rcases Multiset.mem_add.mp h with a|b
    · have := Multiset.eq_of_mem_replicate a; omega
    · have := ih b; omega

theorem bin_count (start : Nat) (ps : List Nat) (j : Nat) :
    (binStock start ps).count (start+j)=ps[j]?.getD 0 := by
  induction ps generalizing j start with
  | nil => simp [binStock]
  | cons p ps ih =>
    cases j with
    | zero =>
      have h : start ∉ binStock (start+1) ps := fun a => by have := bin_lower a; omega
      simp [binStock,Multiset.count_eq_zero.mpr h]
    | succ j =>
      simp [binStock,Multiset.count_replicate,show start+(j+1)=start+1+j by omega,
        show start ≠ start+1+j by omega, ih]

theorem bins_of_columns {cs : Columns} (good : ValidCols cs) (start : Nat) :
    (flatten cs).map (fun u => u/4+start) = binStock start (masses cs) := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    have val : (c.map fun u => u/4+start) = Multiset.replicate c.card start := by
      rw [← Multiset.map_const]
      apply Multiset.map_congr rfl
      intro u hu
      have := good c (.head _) u hu
      dsimp; omega
    simp only [flatten,Multiset.map_add,Multiset.map_map,masses,List.map_cons,binStock,val]
    have eq : (flatten cs).map ((fun u => u/4+start) ∘ (·+4)) =
        (flatten cs).map (fun u => u/4+(start+1)) := by
      apply Multiset.map_congr rfl
      intro u _
      dsimp; omega
    rw [eq,ih (fun k hk => good k (.tail _ hk))]; rfl

theorem bins_of_layout {cs} (good : ValidCols cs) (a b : Nat) :
    (layout a cs b).map OriginCert.groupOf = binStock 0 (a::b::masses cs) := by
  simp only [layout,Multiset.map_add,Multiset.map_replicate,Multiset.map_map,binStock]
  have eq : OriginCert.groupOf ∘ (·+2) = fun u => u/4+2 := by
    funext u; simp [OriginCert.groupOf]
  rw [eq,bins_of_columns good]
  rfl

theorem limits_lookup {xs ys : List Nat} (h : List.Forall₂ (· ≤ ·) xs ys) (j : Nat) :
    xs[j]?.getD 0 ≤ ys[j]?.getD 0 := by
  induction h generalizing j with
  | nil => rfl
  | cons hd _ ih => cases j with
    | zero => exact hd
    | succ j => exact ih j

def headerOK (C : OriginCert) (r : Rule) := decide (C.width=r.word.length ∧ 0<C.width) &&
  every C.bins (fun j => decide ((r.left::r.right::r.word)[j]?.getD 0 ≤ digit C.caps j))

def checkWindow (C : OriginCert) (box : BoxProof) (r : Rule) :=
  headerOK C r && every C.dim C.nodeOK &&
    C.boxOK (fun _ => 0) (fun u => digit C.caps (OriginCert.groupOf u)) box

theorem checkWindow_parts {C : OriginCert} {box : BoxProof} {r : Rule}
    (header : headerOK C r = true) (closed : C.Closed)
    (cover : C.boxOK (fun _ => 0) (fun u => digit C.caps (OriginCert.groupOf u)) box = true) :
    r.Valid := by
  intro cs a b good shape left right served
  simp only [headerOK,Bool.and_eq_true,decide_eq_true_eq,every_iff] at header
  have len : cs.length=C.width := by
    have := shape.length_eq
    simpa [masses,header.1.1] using this
  let P := layout a cs b
  have budget : C.Budget P := by
    intro j hj
    have h := limits_lookup (.cons left (.cons right shape)) j
    have bx := bin_count 0 (a::b::masses cs) j
    rw [Nat.zero_add] at bx
    change (Multiset.map OriginCert.groupOf (layout a cs b)).count j ≤ _
    rw [bins_of_layout good,bx]
    exact h.trans (header.2 j hj)
  have valid : ∀ u ∈ P, u<C.dim := by
    intro u hu
    rcases Multiset.mem_add.mp hu with l|r
    · have := Multiset.eq_of_mem_replicate l; unfold OriginCert.dim; omega
    · rcases Multiset.mem_add.mp r with l|r
      · have := Multiset.eq_of_mem_replicate l; unfold OriginCert.dim; omega
      · obtain ⟨v,hv,rfl⟩ := Multiset.mem_map.mp r
        have := flatten_bound good hv
        unfold OriginCert.dim; omega
  apply C.box_sound budget _ box _ _ (fun _ => Nat.zero_le _) _ cover
  · intro t lo hi
    have ht : t-2<4*cs.length := by unfold OriginCert.dim at hi; omega
    have reach := served (t-2) ht
    rw [len,show t-2+2=t by omega] at reach
    exact C.reachable_origin closed header.1.2 reach valid budget
  · intro u hu
    have := OriginCert.other_bound (fun _ => Nat.zero_le _) budget hu
    omega

theorem checkWindow_sound (C : OriginCert) (box : BoxProof) (r : Rule)
    (h : checkWindow C box r = true) : r.Valid := by
  simp only [checkWindow,Bool.and_eq_true,every_iff] at h
  exact checkWindow_parts h.1.1 h.1.2 h.2

end Staircase
