module

public import Staircase.Windows
public import Mathlib.Data.List.Induction

@[expose] public section
namespace Staircase

/-- A residual window test consists of its remaining slash bounds and its right stock. -/
structure Pattern where
  word : List Nat
  right : Nat
deriving DecidableEq, Repr

structure Rule extends Pattern where
  left : Nat
deriving DecidableEq, Repr

def Rule.Valid (r : Rule) : Prop :=
  ∀ (cs : Columns) (a b : Nat), ValidCols cs → List.Forall₂ (· ≤ ·) (masses cs) r.word →
    a ≤ r.left → b ≤ r.right → ¬ Served a cs b

/-- Complete a residual pattern at the first slashes of the input with exterior supply b. -/
def patternFits : List Nat → Nat → List Nat → Nat → Prop
  | [], cap, ps, b => (ps.foldr (fun p v => p+v/2) b) ≤ cap
  | _::_, _, [], _ => False
  | u::us, cap, p::ps, b => p ≤ u ∧ patternFits us cap ps b

def rightSupply (cs : Columns) (b : Nat) := (masses cs).foldr (fun p v => p+v/2) b

theorem trim_suffix (cs tail : Columns) (a b : Nat)
    (h : Served a (cs++tail) b) (good : ValidCols (cs++tail)) :
    Served a cs (rightSupply tail b) := by
  induction tail using List.reverseRecOn generalizing b with
  | nil => simpa [rightSupply,masses] using h
  | append_singleton xs c ih =>
    rw [← List.append_assoc] at h good
    have gx : ValidCols (cs++xs) := fun k hk => good k (List.mem_append_left _ hk)
    have short := trim_right gx h
    simpa [rightSupply,masses,List.foldr_append] using ih (c.card+b/2) short gx

theorem matches_split {word : List Nat} {cap cs b}
    (h : patternFits word cap (masses cs) b) :
    ∃ front tail : Columns, cs=front++tail ∧ List.Forall₂ (· ≤ ·) (masses front) word ∧
      rightSupply tail b ≤ cap := by
  induction word generalizing cs with
  | nil => exact ⟨[],cs,rfl,.nil,h⟩
  | cons u us ih =>
    cases cs with
    | nil => contradiction
    | cons c cs =>
      obtain ⟨front, tail, eq, test, bank⟩ := ih h.2
      exact ⟨c::front,tail,by simp [eq],.cons h.1 test,bank⟩

theorem rejects_rule {r : Rule} (valid : r.Valid) {cs a b}
    (h : Served a cs b) (good : ValidCols cs) (left : a ≤ r.left) :
    ¬ patternFits r.word r.right (masses cs) b := by
  intro matched
  obtain ⟨front,tail,rfl,limits,right⟩ := matches_split matched
  apply valid front a _ (fun k hk => good k (List.mem_append_left _ hk)) limits left right
  exact trim_suffix front tail a b h good

end Staircase
