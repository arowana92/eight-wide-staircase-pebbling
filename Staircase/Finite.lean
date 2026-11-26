module

public import Staircase.Local

@[expose] public section
namespace Staircase

/-- Universal iteration on the indices strictly below n. -/
def every : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n+1, f => f n && every n f

theorem every_iff {n f} : every n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [every]
  | succ n ih =>
    rw [every,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨last,prev⟩ i hi
      by_cases eq : i=n
      · simpa [eq] using last
      · exact prev _ (by omega)
    · intro h
      exact ⟨h _ (by omega), fun i hi => h i (by omega)⟩

/-- Unsigned base-64 coordinates, least significant coordinate first. -/
def digit (a : Nat) : Nat → Nat
  | 0 => a%64
  | i+1 => digit (a/64) i

def boundedSum : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | k+1, need, a, b =>
    need == 0 || (decide (need%64 ≤ a%64+b%64) && boundedSum k (need/64) (a/64) (b/64))

theorem boundedSum_iff {k need a b} : boundedSum k need a b = true ↔
    ∀ j < k, digit need j ≤ digit a j + digit b j := by
  have zero (j : Nat) : digit 0 j = 0 := by induction j <;> simp_all [digit]
  induction k generalizing need a b with
  | zero => simp [boundedSum]
  | succ k ih =>
    by_cases h : need=0
    · simp [boundedSum,h,zero]
    · simp only [boundedSum,beq_iff_eq,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,h,
        false_or,ih]
      constructor
      · rintro ⟨hd,tl⟩ (j|j) hj
        · exact hd
        · exact tl j (by omega)
      · intro all
        exact ⟨all 0 (by omega),fun j hj => all (j+1) (by omega)⟩

def sumWithin : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | k+1, a,b,cap => decide (a%64+b%64 ≤ cap%64) && sumWithin k (a/64) (b/64) (cap/64)

theorem sumWithin_iff {k a b cap} : sumWithin k a b cap = true ↔
    ∀ j < k, digit a j + digit b j ≤ digit cap j := by
  induction k generalizing a b cap with
  | zero => simp [sumWithin]
  | succ k ih =>
    simp only [sumWithin,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨hd,tl⟩ (j|j) hj
      · exact hd
      · exact tl j (by omega)
    · intro h
      exact ⟨h 0 (by omega),fun j hj => h (j+1) (by omega)⟩

/-- Packed tables only provide candidate witnesses. Their mathematical properties
    are checked subsequently. Each limb holds 32 entries. -/
inductive LimbTree where
  | leaf (word : Nat)
  | fork (even odd : LimbTree)
deriving Inhabited

def LimbTree.read : LimbTree → Nat → Nat
  | .leaf x, _ => x
  | .fork a b, i => if i%2=0 then a.read (i/2) else b.read (i/2)

structure Packed where
  size : Nat
  width : Nat
  limbs : LimbTree
deriving Inhabited

def Packed.read (p : Packed) (i : Nat) : Nat :=
  ((p.limbs.read (i/32)) >>> ((i%32)*p.width)) % (2^p.width)

end Staircase
