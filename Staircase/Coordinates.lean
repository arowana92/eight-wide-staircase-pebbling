module

public import Staircase.Graph

@[expose] public section
namespace Staircase

/-- Physical row and slash in the paper's one-based diagonal coordinates. -/
def row (u : Nat) : Nat := if (u/4)%2 = 0 then 1+2*(u%4) else 8-2*(u%4)
def slash (u : Nat) := u/4+1

def index (s r : Nat) : Nat :=
  4*(s-1) + (if (s-1)%2 = 0 then (r-1)/2 else (8-r)/2)

theorem index_valid {n s r : Nat} (hs : 1 ≤ s ∧ s ≤ n) (hr : 1 ≤ r ∧ r ≤ 8)
    (par : s%2 = r%2) :
    index s r < 4*n ∧ slash (index s r) = s ∧ row (index s r) = r := by
  unfold index slash row
  split <;> split <;> omega

theorem row_valid {n u : Nat} (h : u < 4*n) :
    (1 ≤ slash u ∧ slash u ≤ n) ∧ (1 ≤ row u ∧ row u ≤ 8) ∧
    slash u % 2 = row u % 2 ∧ index (slash u) (row u) = u := by
  unfold slash row index
  split <;> split <;> omega

def consecutive (a b : Nat) : Prop := a+1=b ∨ b+1=a

theorem adj_iff_diagonals {n u v : Nat} :
    Adj n u v ↔ u < 4*n ∧ v < 4*n ∧ consecutive (slash u) (slash v) ∧
      consecutive (row u) (row v) := by
  unfold Adj consecutive row slash
  split <;> split <;> omega

/-- Original integer-grid coordinates from the two diagonal numbers. -/
def gridXY (u : Nat) : Int × Int :=
  (((slash u : Int)+(row u : Int))/2, ((row u : Int)-(slash u : Int))/2)

theorem gridXY_diagonals (u : Nat) :
    (gridXY u).1 - (gridXY u).2 = (slash u : Int) ∧
    (gridXY u).1 + (gridXY u).2 = (row u : Int) := by
  have h := (row_valid (n := u+1) (by omega : u < 4*(u+1))).2.2.1
  unfold gridXY
  dsimp
  omega

theorem gridXY_onto {n : Nat} (x y : Int)
    (h : 1 ≤ x-y ∧ x-y ≤ n ∧ 1 ≤ x+y ∧ x+y ≤ 8) :
    ∃ u < 4*n, gridXY u = (x,y) := by
  let s := (x-y).toNat
  let r := (x+y).toNat
  have hv := index_valid (n := n) (s := s) (r := r)
    (by dsimp [s]; omega) (by dsimp [r]; omega) (by dsimp [s,r]; omega)
  refine ⟨_,hv.1,?_⟩
  simp only [gridXY,hv.2.1,hv.2.2,Prod.mk.injEq]
  dsimp [s,r]
  omega

theorem gridXY_injective {n u v : Nat} (hu : u < 4*n) (hv : v < 4*n)
    (h : gridXY u = gridXY v) : u=v := by
  have a := gridXY_diagonals u
  rw [h] at a
  have b := gridXY_diagonals v
  have hs : slash u=slash v := by omega
  have hr : row u=row v := by omega
  rw [← (row_valid hu).2.2.2, hs,hr,(row_valid hv).2.2.2]

def gridNeighbors (a b : Int × Int) : Prop :=
  (a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨
  (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1))

theorem adj_iff_grid {n u v : Nat} :
    Adj n u v ↔ u < 4*n ∧ v < 4*n ∧ gridNeighbors (gridXY u) (gridXY v) := by
  rw [adj_iff_diagonals]
  have a := gridXY_diagonals u
  have b := gridXY_diagonals v
  unfold consecutive gridNeighbors
  omega

end Staircase
