module

public import Staircase.Collapse
public import Staircase.Arithmetic

@[expose] public section
namespace Staircase

abbrev Columns := List Stock
def ValidCols (cs : Columns) := ∀ c ∈ cs, ∀ u ∈ c, u < 4
def flatten : Columns → Stock
  | [] => 0
  | c :: cs => c + (flatten cs).map (·+4)
def masses (cs : Columns) : List Nat := cs.map Multiset.card

theorem flatten_append (cs ds : Columns) :
    flatten (cs++ds) = flatten cs + (flatten ds).map (·+4*cs.length) := by
  induction cs with
  | nil => simp [flatten]
  | cons c cs ih =>
    simp [flatten, ih, Multiset.map_add, Multiset.map_map,
      Nat.mul_add, Nat.add_assoc, Multiset.add_assoc]

theorem flatten_bound {cs : Columns} (valid : ValidCols cs) {u : Nat} (hu : u ∈ flatten cs) :
    u < 4*cs.length := by
  induction cs generalizing u with
  | nil => simp [flatten] at hu
  | cons c cs ih =>
    rw [flatten] at hu
    rcases Multiset.mem_add.mp hu with left|right
    · have := valid c (.head _) u left
      simp only [List.length_cons]; omega
    · obtain ⟨v,hv,rfl⟩ := Multiset.mem_map.mp right
      have := ih (fun _ hc => valid _ (.tail _ hc)) hv
      simp only [List.length_cons]; omega

theorem flatten_mass (cs : Columns) : (flatten cs).card = (masses cs).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa [flatten, masses] using congrArg (c.card+·) ih

theorem stock_columns (n : Nat) (P : Stock) (valid : ∀ u ∈ P, u < 4*n) :
    ∃ cs : Columns, cs.length = n ∧ ValidCols cs ∧ flatten cs = P := by
  induction n generalizing P with
  | zero =>
    have h : P=0 := Multiset.eq_zero_of_forall_notMem (by intro u hu; have := valid _ hu; omega)
    exact ⟨[],rfl,by simp [ValidCols],h.symm⟩
  | succ n ih =>
    let c := P.filter (·<4)
    let rest := P.filter (fun u => ¬u<4)
    have parts : c+rest=P := Multiset.filter_add_not _ _
    obtain ⟨cs,len,good,flat⟩ := ih (rest.map (·-4)) (by
      intro u hu
      obtain ⟨v,hv,rfl⟩ := Multiset.mem_map.mp hu
      obtain ⟨inP,large⟩ := Multiset.mem_filter.mp hv
      have := valid v inP
      omega)
    refine ⟨c::cs,by simp [len],?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|h
      · exact fun _ hu => (Multiset.mem_filter.mp hu).2
      · exact good a h
    · rw [flatten,flat,Multiset.map_map]
      have eq : rest.map ((·+4) ∘ (·-4)) = rest := by
        conv_rhs => rw [← Multiset.map_id rest]
        apply Multiset.map_congr rfl
        intro u hu
        have := (Multiset.mem_filter.mp hu).2
        dsimp
        omega
      rwa [eq]

/-- Physical vertices start at 2. Vertex 0 is the left hub, vertex 1 the right. -/
def WAdj (n u v : Nat) : Prop :=
  (2 ≤ u ∧ 2 ≤ v ∧ Adj n (u-2) (v-2)) ∨
  (u=0 ∧ 2≤v ∧ v<6) ∨ (v=0 ∧ 2≤u ∧ u<6) ∨
  (u=1 ∧ 2≤v ∧ 4*n≤v+2 ∧ v<4*n+2) ∨
  (v=1 ∧ 2≤u ∧ 4*n≤u+2 ∧ u<4*n+2)

instance (n u v) : Decidable (WAdj n u v) := by unfold WAdj; infer_instance

def layout (a : Nat) (cs : Columns) (b : Nat) : Stock :=
  Multiset.replicate a 0 + (Multiset.replicate b 1 + (flatten cs).map (·+2))
def Served (a : Nat) (cs : Columns) (b : Nat) : Prop :=
  ∀ t < 4*cs.length, Reaches (WAdj cs.length) (layout a cs b) (t+2)

theorem full_served {n P} (h : Solvable n P) {cs} (len : cs.length=n) (flat : flatten cs=P) :
    Served 0 cs 0 := by
  intro t ht
  rw [len] at ht ⊢
  have reach := (h.2 t ht).map (·+2) (D := WAdj n) (by
    intro u v edge
    exact Or.inl ⟨by omega,by omega,by simpa using edge⟩)
  simpa [layout,flat] using reach

end Staircase
