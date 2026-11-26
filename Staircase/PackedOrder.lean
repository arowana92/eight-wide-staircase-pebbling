module

public import Staircase.Finite

@[expose] public section
namespace Staircase

/-- Repeated six-bit lanes. Bit five is the borrow guard. -/
def laneMask (v : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => 64*laneMask v n+v

def Narrow (limit : Nat) : Nat → Nat → Prop
  | 0,x => x=0
  | k+1,x => x%64 < limit ∧ Narrow limit k (x/64)

private theorem and_div64 (a b : Nat) : (a &&& b)/64 = a/64 &&& b/64 := by
  simpa [Nat.shiftRight_eq_div_pow] using (Nat.shiftRight_and_distrib (a := a) (b := b) (i := 6))

private theorem and_mod64 (a b : Nat) : (a &&& b)%64 = a%64 &&& b%64 := by
  exact Nat.and_mod_two_pow (a := a) (b := b) (n := 6)

private theorem highNibble : ∀ i : Fin 64, (i.val &&& 48 = 0 ↔ i.val < 16) := by decide
private theorem highBit : ∀ i : Fin 64, (i.val &&& 32 = 32 ↔ 32 ≤ i.val) := by decide

def narrowCheck (k x : Nat) := decide (x < 64^k ∧ x &&& laneMask 48 k = 0)

theorem narrowCheck_sound {k x} (h : narrowCheck k x = true) : Narrow 16 k x := by
  induction k generalizing x with
  | zero => have := (of_decide_eq_true h).1; change x=0; simpa using this
  | succ k ih =>
    obtain ⟨size,mask⟩ := of_decide_eq_true h
    have m : (64*laneMask 48 k+48)%64=48 := by omega
    have d : (64*laneMask 48 k+48)/64=laneMask 48 k := by omega
    refine ⟨(highNibble ⟨x%64,by omega⟩).mp ?_,ih ?_⟩
    · have a := congrArg (fun v : Nat => v%64) mask
      change (x &&& laneMask 48 (k+1))%64=0 at a
      rwa [and_mod64,laneMask,m] at a
    · apply decide_eq_true
      rw [Nat.pow_succ] at size
      refine ⟨by omega, ?_⟩
      have a := congrArg (fun v : Nat => v/64) mask
      change (x &&& laneMask 48 (k+1))/64=0 at a
      rwa [and_div64,laneMask,d] at a

private theorem narrow_weaken {k a} (h : Narrow 16 k a) : Narrow 32 k a := by
  induction k generalizing a with
  | zero => exact h
  | succ k ih => exact ⟨by have := h.1; omega, ih h.2⟩

private theorem narrow_add {k a b} (ha : Narrow 16 k a) (hb : Narrow 16 k b) :
    Narrow 32 k (a+b) ∧ ∀ j<k, digit (a+b) j = digit a j + digit b j := by
  induction k generalizing a b with
  | zero =>
    change a=0 at ha; change b=0 at hb
    subst a; subst b; exact ⟨rfl,by omega⟩
  | succ k ih =>
    obtain ⟨rec,eq⟩ := ih ha.2 hb.2
    have la := ha.1
    have lb := hb.1
    have d : (a+b)/64 = a/64+b/64 := by omega
    refine ⟨⟨by omega,by rwa [d]⟩,?_⟩
    rintro (j|j) hj
    · simp only [digit]; omega
    · simp only [digit,d]; exact eq _ (by omega)

private theorem guard_ge {k x} (h : Narrow 32 k x) : x ≤ laneMask 32 k := by
  induction k generalizing x with
  | zero => exact Nat.le_of_eq h
  | succ k ih =>
    have head := h.1
    have tail := ih h.2
    simp only [laneMask]
    omega

def laneLE (k x y : Nat) :=
  let guard := laneMask 32 k
  decide ((guard+y-x) &&& guard = guard)

private theorem laneLE_iff {k x y} (hx : Narrow 32 k x) (hy : Narrow 32 k y) :
    laneLE k x y = true ↔ ∀ i<k, digit x i ≤ digit y i := by
  induction k generalizing x y with
  | zero => simp [laneLE,laneMask]
  | succ k ih =>
    have gx := guard_ge hx.2
    have lx := hx.1
    have ly := hy.1
    let g := laneMask 32 k
    let v := 64*g+32+y-x
    have divg : (64*g+32)/64=g := by omega
    have modg : (64*g+32)%64=32 := by omega
    have divv : v/64=g+y/64-x/64 := by dsimp [v,g] at *; omega
    have lowv : 32≤v%64 ↔ x%64≤y%64 := by dsimp [v,g] at *; omega
    have part₀ : (v &&& (64*g+32))%64=32 ↔ x%64≤y%64 := by
      rw [and_mod64,modg]
      exact (highBit ⟨v%64,by omega⟩).trans lowv
    have part₁ : (v &&& (64*g+32))/64=g ↔ ∀ i<k, digit (x/64) i ≤ digit (y/64) i := by
      rw [and_div64,divg,divv]
      simpa only [laneLE,decide_eq_true_eq,g] using ih hx.2 hy.2
    change decide (v &&& (64*g+32) = 64*g+32) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · intro eq
      rintro (j|j) hj
      · exact part₀.mp (by rw [eq]; exact modg)
      · exact part₁.mp (by rw [eq]; exact divg) _ (by omega)
    · intro all
      have a := part₀.mpr (all 0 (by omega))
      have b := part₁.mpr (fun j hj => all (j+1) (by omega))
      omega

def fastBounded (k need a b : Nat) :=
  if narrowCheck k need && narrowCheck k a && narrowCheck k b then laneLE k need (a+b)
  else boundedSum k need a b

def fastWithin (k a b cap : Nat) :=
  if narrowCheck k a && narrowCheck k b && narrowCheck k cap then laneLE k (a+b) cap
  else sumWithin k a b cap

theorem fastBounded_eq (k need a b : Nat) : fastBounded k need a b = boundedSum k need a b := by
  unfold fastBounded
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨add,digits⟩ := narrow_add (narrowCheck_sound h.1.2) (narrowCheck_sound h.2)
    apply Bool.eq_iff_iff.mpr
    rw [laneLE_iff (narrow_weaken (narrowCheck_sound h.1.1)) add,boundedSum_iff]
    exact forall_congr' fun i => forall_congr' fun hi => by rw [digits i hi]
  · rfl

theorem fastWithin_eq (k a b cap : Nat) : fastWithin k a b cap = sumWithin k a b cap := by
  unfold fastWithin
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨add,digits⟩ := narrow_add (narrowCheck_sound h.1.1) (narrowCheck_sound h.1.2)
    apply Bool.eq_iff_iff.mpr
    rw [laneLE_iff add (narrow_weaken (narrowCheck_sound h.2)),sumWithin_iff]
    exact forall_congr' fun i => forall_congr' fun hi => by rw [digits i hi]
  · rfl

end Staircase
