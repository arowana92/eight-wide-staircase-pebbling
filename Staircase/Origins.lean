module

public import Staircase.Ancestry
public import Staircase.PackedOrder

@[expose] public section
namespace Staircase

/-- Origin lower bounds. A profile shares one slash-count bound between several
    vectors of site-count bounds. -/
structure Profile where
  groups : Nat
  sites : Packed
deriving Inhabited

structure OriginNode where
  neighbors : Array Nat
  profiles : Array Profile
  offsets : Packed
  seed : Nat
deriving Inhabited

structure OriginCert where
  width : Nat
  caps : Nat
  nodes : Array OriginNode
  tips : Packed

namespace OriginCert

def dim (C : OriginCert) := 4*C.width+2
def bins (C : OriginCert) := C.width+2
def groupOf (v : Nat) := if v<2 then v else (v-2)/4+2
def node (C : OriginCert) (v : Nat) := C.nodes[v]?.getD default
def profile (C : OriginCert) (u i : Nat) := (C.node u).profiles[i]?.getD default
def gr (C : OriginCert) (v z : Nat) := (C.profile v (z/1024)).groups
def site (C : OriginCert) (v z : Nat) := (C.profile v (z/1024)).sites.read (z%1024)

def registered (C : OriginCert) (v z : Nat) : Bool :=
  decide (z/1024 < (C.node v).profiles.size ∧ z%1024 < (C.profile v (z/1024)).sites.size)

def countG (P : Stock) (i : Nat) := (P.map groupOf).count i
def Budget (C : OriginCert) (P : Stock) := ∀ j < C.bins, countG P j ≤ digit C.caps j

def Realizes (C : OriginCert) (P : Stock) (v z : Nat) : Prop :=
  C.registered v z = true ∧
  (∀ j < C.bins, digit (C.gr v z) j ≤ countG P j) ∧
  (∀ j < C.dim, digit (C.site v z) j ≤ P.count j)

def seedOK (C : OriginCert) (u : Nat) : Bool :=
  let z := (C.node u).seed
  digit C.caps (groupOf u) == 0 ||
    (C.registered u z &&
    every C.bins (fun j => decide (digit (C.gr u z) j ≤ if groupOf u = j then 1 else 0)) &&
    every C.dim (fun j => decide (digit (C.site u z) j ≤ if u = j then 1 else 0)))

def graphOK (C : OriginCert) (u : Nat) := every C.dim fun v =>
  !(decide (WAdj C.width u v)) || (C.node u).neighbors.contains v

def hint (C : OriginCert) (u i j a b k : Nat) : Nat :=
  let src := C.node u
  let offset := src.offsets.read (i*src.profiles.size+j)
  C.tips.read (offset+(a*(C.profile u j).sites.size+b)*src.neighbors.size+k)

def combineOK (C : OriginCert) (u i j a b k : Nat) : Bool :=
  let v := (C.node u).neighbors[k]?.getD 0
  let z := C.hint u i j a b k
  C.registered v z &&
    fastBounded C.bins (C.gr v z) (C.profile u i).groups (C.profile u j).groups &&
    fastBounded C.dim (C.site v z) ((C.profile u i).sites.read a) ((C.profile u j).sites.read b)

def profilePairOK (C : OriginCert) (u i j : Nat) : Bool :=
  let x := C.profile u i
  let y := C.profile u j
  !(fastWithin C.bins x.groups y.groups C.caps) ||
    every x.sites.size fun a => every y.sites.size fun b =>
      every (C.node u).neighbors.size fun k => C.combineOK u i j a b k

def nodeOK (C : OriginCert) (u : Nat) : Bool :=
  let n := (C.node u).profiles.size
  C.seedOK u && C.graphOK u && every n fun i => every n fun j => C.profilePairOK u i j

def Closed (C : OriginCert) := ∀ u < C.dim, C.nodeOK u = true

theorem realizes_mono {C : OriginCert} {P Q v z} (h : C.Realizes P v z) (le : P ≤ Q) :
    C.Realizes Q v z :=
  ⟨h.1, fun j hj => (h.2.1 j hj).trans (Multiset.count_le_of_le _ (Multiset.map_le_map le)),
   fun j hj => (h.2.2 j hj).trans (Multiset.count_le_of_le _ le)⟩

theorem seed_realizes {C : OriginCert} (closed : C.Closed) {u} (bound : u < C.dim)
    (budget : C.Budget {u}) : C.Realizes {u} u (C.node u).seed := by
  have ok := closed u bound
  simp only [nodeOK,Bool.and_eq_true] at ok
  have seed := ok.1.1
  simp only [seedOK,Bool.or_eq_true,beq_iff_eq,Bool.and_eq_true,every_iff,decide_eq_true_eq] at seed
  have hg : groupOf u < C.bins := by unfold groupOf bins dim at *; split <;> omega
  have bc := budget _ hg
  simp [countG] at bc
  rcases seed with zero|⟨⟨reg,g⟩,s⟩
  · omega
  · refine ⟨reg,?_,?_⟩
    · intro j hj; simpa [countG,Multiset.count_singleton,eq_comm] using g j hj
    · intro j hj; simpa [Multiset.count_singleton,eq_comm] using s j hj

theorem merge_realizes {C : OriginCert} (closed : C.Closed) {u v P Q x y}
    (hu : u < C.dim) (hv : v < C.dim) (e : WAdj C.width u v)
    (hx : C.Realizes P u x) (hy : C.Realizes Q u y) (bd : C.Budget (P+Q)) :
    ∃ z, C.Realizes (P+Q) v z := by
  have ok := closed u hu
  simp only [nodeOK,Bool.and_eq_true] at ok
  obtain ⟨⟨_,graph⟩,pairs⟩ := ok
  have link := every_iff.mp graph v hv
  simp only [e,decide_true,Bool.not_true,Bool.false_or,Array.contains_iff_mem] at link
  obtain ⟨k,hk,eq⟩ := Array.mem_iff_getElem.mp link
  have ix := of_decide_eq_true hx.1
  have iy := of_decide_eq_true hy.1
  have pair := every_iff.mp (every_iff.mp pairs _ ix.1) _ iy.1
  have admissible : sumWithin C.bins (C.gr u x) (C.gr u y) C.caps = true := by
    apply sumWithin_iff.mpr
    intro j hj
    have h := bd j hj
    simp only [countG, Multiset.map_add, Multiset.count_add] at h
    exact (Nat.add_le_add (hx.2.1 _ hj) (hy.2.1 _ hj)).trans h
  change sumWithin _ (C.profile u (x/1024)).groups (C.profile u (y/1024)).groups _ = true at admissible
  simp only [profilePairOK,fastWithin_eq,admissible,Bool.not_true,Bool.false_or] at pair
  have step := every_iff.mp (every_iff.mp (every_iff.mp pair _ ix.2) _ iy.2) k hk
  have src : (C.node u).neighbors[k]?.getD 0 = v := by simp [hk,eq]
  simp only [combineOK,fastBounded_eq,src,Bool.and_eq_true,boundedSum_iff] at step
  refine ⟨_,step.1.1,?_,?_⟩
  · intro j hj
    simpa only [countG,Multiset.map_add,Multiset.count_add] using
      (step.1.2 j hj).trans (Nat.add_le_add (hx.2.1 _ hj) (hy.2.1 _ hj))
  · intro j hj
    simpa only [Multiset.count_add] using
      (step.2 j hj).trans (Nat.add_le_add (hx.2.2 _ hj) (hy.2.2 _ hj))

theorem tree_realizes {C : OriginCert} (closed : C.Closed) (pos : 0<C.width)
    (T : Tree) (legal : T.Legal (WAdj C.width)) (valid : ∀ u ∈ T.stock, u < C.dim)
    (budget : C.Budget T.stock) : T.site < C.dim ∧ ∃ z, C.Realizes T.stock T.site z := by
  induction T with
  | token u => exact ⟨valid u (by simp [Tree.stock]),_,seed_realizes closed (valid u (by simp [Tree.stock])) budget⟩
  | merge v A B ia ib =>
    obtain ⟨ga,gb,same,edge⟩ := legal
    have sub (S : Stock) (le : S ≤ A.stock+B.stock) : C.Budget S := fun j hj =>
      (Multiset.count_le_of_le _ (Multiset.map_le_map le)).trans (budget j hj)
    obtain ⟨ha,x,hx⟩ := ia ga (fun u hu => valid u (by simp [Tree.stock,hu]))
      (sub _ (Multiset.le_add_right ..))
    obtain ⟨_,y,hy⟩ := ib gb (fun u hu => valid u (by simp [Tree.stock,hu]))
      (sub _ (Multiset.le_add_left ..))
    have hv : v<C.dim := by unfold WAdj Adj at edge; unfold dim; omega
    rw [← same] at hy
    exact ⟨hv,merge_realizes closed ha hv edge hx hy budget⟩

theorem reachable_origin {C : OriginCert} (closed : C.Closed) (pos : 0<C.width)
    {P t} (h : Reaches (WAdj C.width) P t) (valid : ∀ u ∈ P, u<C.dim)
    (budget : C.Budget P) : ∃ z, C.Realizes P t z := by
  obtain ⟨T,rfl,legal,le⟩ := h.tree
  obtain ⟨_,z,hz⟩ := C.tree_realizes closed pos T legal
    (fun _ hu => valid _ (Multiset.mem_of_le le hu))
    (fun j hj => (Multiset.count_le_of_le _ (Multiset.map_le_map le)).trans (budget j hj))
  exact ⟨z,realizes_mono hz le⟩

end OriginCert
end Staircase
