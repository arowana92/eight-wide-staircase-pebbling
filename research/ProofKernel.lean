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

/-- The exterior effect of one original grid move, including its change to
    the auxiliary stock. A move elsewhere leaves this exterior unchanged. -/
inductive Effect : List Nat → List Nat → Int → Prop where
  | other (u) : Effect u u 0
  | toward (front rest a b) :
      Effect (front ++ a :: (b+2) :: rest) (front ++ (a+1) :: b :: rest) 0
  | away (front rest a b) :
      Effect (front ++ (a+2) :: b :: rest) (front ++ a :: (b+1) :: rest) 0
  | receive (a rest) : Effect (a :: rest) ((a+1) :: rest) 1
  | send (a rest) : Effect ((a+2) :: rest) (a :: rest) (-2)

theorem bank_step {u v delta} (e : Effect u v delta) {bank : Int}
    (h : (supply u : Int) ≤ bank) : (supply v : Int) ≤ bank+delta := by
  cases e with
  | other => omega
  | toward f t a b => have := inward f t a b; omega
  | away f t a b => have := outward f t a b; omega
  | receive a t => have := boundary_change a 1 t; omega
  | send a t => have := boundary_change a 2 t; omega

inductive Trace : List Nat → List Nat → List Int → Prop where
  | nil (u) : Trace u u []
  | cons {u v w d ds} : Effect u v d → Trace v w ds → Trace u w (d :: ds)

/-- The simulated stock stays nonnegative at every prefix of the replay. -/
inductive Payable : Int → List Int → Prop where
  | nil (b : Int) : Payable b []
  | cons {b d ds} : 0 ≤ b+d → Payable (b+d) ds → Payable b (d :: ds)

theorem bank_simulation {u v ds} (t : Trace u v ds) (bank : Int)
    (h : (supply u : Int) ≤ bank) : Payable bank ds := by
  induction t generalizing bank with
  | nil => exact .nil _
  | cons e _ ih =>
    have hs := bank_step e h
    exact .cons (by omega) (ih _ hs)

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

/-- All lengths at least three follow from four checked bases and the physical
    construction which preserves the distinguished four-pebble pile. -/
theorem extend_upper {P : Nat → Nat → Prop}
    (bases : ∀ n, 3 ≤ n → n ≤ 6 → ∃ m, P n m ∧ m ≤ (5*n+3)/4+3)
    (extend : ∀ n m, P n m → P (n+4) (m+5)) (n : Nat) (hn : 3 ≤ n) :
    ∃ m, P n m ∧ m ≤ (5*n+3)/4+3 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n ≤ 6
    · exact bases n hn small
    · obtain ⟨m, hm, bound⟩ := ih (n-4) (by omega) (by omega)
      have hlen : n-4+4 = n := by omega
      exact ⟨m+5, hlen ▸ extend (n-4) m hm, by omega⟩

end Staircase
