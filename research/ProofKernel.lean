import Std

/- Integer part of the all-length proof. The finite certificate and the strip
   embeddings are checked separately as described in proof.md. -/
namespace Staircase

/-- Exterior slash totals in order from nearest to farthest. -/
def supply : List Nat → Nat
  | [] => 0
  | p :: rest => p + supply rest / 2

theorem prefix_mono (front u v : List Nat) (h : supply u ≤ supply v) :
    supply (front ++ u) ≤ supply (front ++ v) := by
  induction front with
  | nil => exact h
  | cons p rest ih =>
    simp only [List.cons_append, supply]
    omega

theorem inward (front rest : List Nat) (a b : Nat) :
    supply (front ++ (a+1) :: b :: rest) ≤
    supply (front ++ a :: (b+2) :: rest) := by
  apply prefix_mono
  simp only [supply]
  omega

theorem outward (front rest : List Nat) (a b : Nat) :
    supply (front ++ a :: (b+1) :: rest) ≤
    supply (front ++ (a+2) :: b :: rest) := by
  apply prefix_mono
  simp only [supply]
  omega

theorem boundary_change (a k : Nat) (rest : List Nat) :
    supply ((a+k) :: rest) = supply (a :: rest) + k := by
  simp only [supply]
  omega

structure Cut where
  left : Int
  right : Int
  d : Int
  left_nonneg : 0 ≤ left
  right_nonneg : 0 ≤ right
  d_lower : -56 ≤ d
  d_upper : d ≤ 0

def F (x : Cut) : Int := x.d + 4*(x.left-x.right)
def low (x : Cut) : Prop := x.left ≤ 36 ∧ x.right ≤ 36

/-- The bounded computation is needed only when both cut states are low. -/
structure Transfer (x y : Cut) (p : Int) : Prop where
  mass_nonneg : 0 ≤ p
  left_step : y.left = p + x.left / 2
  right_step : x.right = p + y.right / 2
  local_bound : low x → low y →
    y.d - x.d ≤ 4*(2*p + (x.left+1)/2 + (y.right+1)/2) - 20

theorem step_bound {x y : Cut} {p : Int} (step : Transfer x y p) :
    F y - F x ≤ 16*p - 20 := by
  obtain ⟨hp, hl, hr, cert⟩ := step
  have hL := x.left_nonneg
  have hR := y.right_nonneg
  have hx := x.d_lower
  have hy := y.d_upper
  unfold F
  by_cases h : low x ∧ low y
  · have := cert h.1 h.2
    omega
  · simp only [low] at h
    omega

inductive Walk : Cut → Cut → Int → Int → Prop
  | nil (x : Cut) : Walk x x 0 0
  | snoc {x y z : Cut} {n m p : Int} (w : Walk x y n m)
      (e : Transfer y z p) : Walk x z (n+1) (m+p)

theorem telescope {x y : Cut} {n m : Int} (w : Walk x y n m) :
    F y - F x ≤ 16*m - 20*n := by
  induction w with
  | nil => omega
  | snoc w e ih =>
    have := step_bound e
    omega

theorem endpoint_bound {x y : Cut} {n m : Int} (w : Walk x y n m)
    (left_end : x.left = 0) (right_end : y.right = 0) :
    -56 ≤ 16*m - 20*n := by
  have h := telescope w
  have := y.d_lower
  have := x.d_upper
  have := x.right_nonneg
  have := y.left_nonneg
  unfold F at h
  omega

/-- Apply the strip estimate to fifteen disjoint copies of the same placement. -/
theorem pointwise {m n : Int} {x y : Cut} (w : Walk x y (15*n) (15*m))
    (left_end : x.left = 0) (right_end : y.right = 0) : 5*n ≤ 4*m := by
  have := endpoint_bound w left_end right_end
  omega

end Staircase
