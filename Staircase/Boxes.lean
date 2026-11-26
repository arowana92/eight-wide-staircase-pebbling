module

public import Staircase.Origins

@[expose] public section
namespace Staircase

inductive BoxProof where
  | miss (target upper : Nat)
  | cut (site threshold : Nat) (below above : BoxProof)

namespace OriginCert

theorem count_four (P : Stock) (s : Nat) :
    countG P (s+2) = P.count (4*s+2)+P.count (4*s+3)+P.count (4*s+4)+P.count (4*s+5) := by
  induction P using Multiset.induction_on with
  | empty => simp [countG]
  | cons u P ih =>
    have eq : groupOf u=s+2 ↔ u=4*s+2 ∨ u=4*s+3 ∨ u=4*s+4 ∨ u=4*s+5 := by
      unfold groupOf; split <;> omega
    simp only [countG,Multiset.map_cons,Multiset.count_cons] at ih ⊢
    split_ifs <;> omega

theorem count_hub (P : Stock) {u : Nat} (h : u<2) : countG P u=P.count u := by
  induction P using Multiset.induction_on with
  | empty => simp [countG]
  | cons a P ih =>
    have eq : groupOf a=u ↔ a=u := by unfold groupOf; split <;> omega
    simp only [countG,Multiset.map_cons,Multiset.count_cons] at ih ⊢
    split_ifs <;> omega

def others (lo : Nat → Nat) (u : Nat) : Nat :=
  if u<2 then 0 else
    let start := 4*((u-2)/4)+2
    (if u=start then 0 else lo start) + (if u=start+1 then 0 else lo (start+1)) +
    (if u=start+2 then 0 else lo (start+2)) + (if u=start+3 then 0 else lo (start+3))

theorem other_bound {C : OriginCert} {P : Stock} {lo : Nat → Nat}
    (minima : ∀ i, lo i ≤ P.count i) (budget : C.Budget P) {u} (hu : u<C.dim) :
    P.count u + others lo u ≤ digit C.caps (groupOf u) := by
  have g : groupOf u<C.bins := by unfold groupOf dim bins at *; split <;> omega
  have bc := budget _ g
  by_cases small : u<2
  · simpa [others,small,groupOf,count_hub P small] using bc
  · let s := (u-2)/4
    have gu : groupOf u=s+2 := by simp [groupOf,small,s]
    rw [gu,count_four] at bc
    rw [gu]
    have mi₀ := minima (4*s+2)
    have mi₁ := minima (4*s+3)
    have mi₂ := minima (4*s+4)
    have mi₃ := minima (4*s+5)
    simp only [others,ite_eq_right small]
    change P.count u + ((if u=4*s+2 then 0 else lo (4*s+2)) +
      (if u=4*s+3 then 0 else lo (4*s+3)) + (if u=4*s+4 then 0 else lo (4*s+4)) +
      (if u=4*s+5 then 0 else lo (4*s+5))) ≤ _
    have ranges : u=4*s+2 ∨ u=4*s+3 ∨ u=4*s+4 ∨ u=4*s+5 := by dsimp [s]; omega
    rcases ranges with eq|eq|eq|eq <;> rw [eq] <;> simp [Nat.add_assoc] <;> omega

def allowance (C : OriginCert) (lo hi : Nat → Nat) (u : Nat) :=
  min (hi u) (digit C.caps (groupOf u) - others lo u)

def excludes (C : OriginCert) (target upper : Nat) :=
  every (C.node target).profiles.size fun i =>
    let pr := C.profile target i
    every pr.sites.size fun j => !(fastBounded C.dim (pr.sites.read j) upper 0)

def boxOK (C : OriginCert) (lo hi : Nat → Nat) : BoxProof → Bool
  | .miss t upper => decide (2≤t ∧ t<C.dim) &&
      every C.dim (fun u => decide (C.allowance lo hi u ≤ digit upper u)) && C.excludes t upper
  | .cut v k a b =>
      C.boxOK lo (fun u => if u=v then min (hi u) (k-1) else hi u) a &&
      C.boxOK (fun u => if u=v then max (lo u) k else lo u) hi b

theorem box_sound {C : OriginCert} {P : Stock} (budget : C.Budget P)
    (all : ∀ t, 2≤t → t<C.dim → ∃ z, C.Realizes P t z) (box : BoxProof)
    (lo hi : Nat → Nat) (low : ∀ u,lo u ≤ P.count u) (high : ∀ u<C.dim, P.count u ≤ hi u)
    (ok : C.boxOK lo hi box = true) : False := by
  induction box generalizing lo hi with
  | cut v k a b ia ib =>
    simp only [boxOK,Bool.and_eq_true] at ok
    by_cases h : P.count v<k
    · apply ia lo _ low _ ok.1
      intro u hu; by_cases eq : u=v
      · subst u; simp; exact ⟨high _ hu,by omega⟩
      · simpa [eq] using high _ hu
    · apply ib _ hi _ high ok.2
      intro u; by_cases eq : u=v
      · subst u; simp; exact ⟨low _,by omega⟩
      · simpa [eq] using low _
  | miss t upper =>
    simp only [boxOK,Bool.and_eq_true,decide_eq_true_eq,every_iff] at ok
    obtain ⟨z,reg,_,demand⟩ := all t ok.1.1.1 ok.1.1.2
    have ids := of_decide_eq_true reg
    have impossible := every_iff.mp (every_iff.mp ok.2 _ ids.1) _ ids.2
    have actual : boundedSum C.dim (C.site t z) upper 0 = true := by
      apply boundedSum_iff.mpr
      intro u hu
      have weight := other_bound low budget hu
      have bound := ok.1.2 u hu
      have part := high u hu
      have req := demand u hu
      unfold allowance at bound
      omega
    simp [site] at actual
    simp [fastBounded_eq,actual] at impossible

end OriginCert
end Staircase
