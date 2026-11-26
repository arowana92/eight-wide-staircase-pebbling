module

public import Staircase.Finite

@[expose] public section
namespace Staircase

structure Position where
  pat : Pattern
  startId : Nat
deriving Repr

def flagMask {α : Type} (f : α → Bool) : List α → Nat
  | [] => 0
  | x::xs => 2*flagMask f xs + (f x).toNat

theorem flagMask_bit {α} (f : α → Bool) (xs : List α) (i : Nat) :
    (flagMask f xs).testBit i = (xs[i]?.map f).getD false := by
  induction xs generalizing i with
  | nil => simp [flagMask]
  | cons x xs ih =>
    cases i with
    | zero => cases h : f x <;> simp [flagMask,h,Nat.testBit_zero]
    | succ i =>
      rw [flagMask,Nat.testBit_succ]
      have eq : (2*flagMask f xs+(f x).toNat)/2=flagMask f xs := by
        cases h : f x <;> simp; omega
      simpa only [eq,List.getElem?_cons_succ] using ih i

theorem flagMask_witness {α} {f : α → Bool} {xs i} (h : (flagMask f xs).testBit i = true) :
    ∃ x, xs[i]?=some x ∧ f x=true := by
  rw [flagMask_bit] at h
  cases e : xs[i]? with
  | none => simp [e] at h
  | some x => exact ⟨x,rfl,by simpa [e] using h⟩

theorem overlap {a b : Nat} (nonzero : a &&& b ≠ 0) :
    ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  by_contra! none
  apply nonzero
  apply Nat.eq_of_testBit_eq
  intro i
  cases h : a.testBit i <;> simp_all

structure Machine where
  positions : List Position
  starts : Array Nat
  letters : Array Nat
  ends : Array Nat
  cont : Nat

namespace Machine

def startFlag (rs : List Rule) (a : Nat) (e : Position) : Bool :=
  match rs[e.startId]? with
  | some r => decide (a≤r.left ∧ e.pat=r.toPattern)
  | none => false

def letterFlag (p : Nat) (e : Position) : Bool :=
  match e.pat.word with
  | u::_ => decide (p≤u)
  | [] => false

def endFlag (r : Nat) (e : Position) : Bool :=
  match e.pat.word with
  | [_] => decide (r≤e.pat.right)
  | _ => false

def contFlag (e : Position) : Bool := decide (2≤e.pat.word.length)

def linkOK (M : Machine) (i : Nat) := match M.positions[i]? with
  | none => true
  | some e => !contFlag e || match M.positions[i+1]? with
    | none => false
    | some f => decide (f.pat.word=e.pat.word.tail ∧ f.pat.right=e.pat.right)

def Header (M : Machine) (rs : List Rule) : Prop :=
  (∀ a<37, M.starts[a]?.getD 0=flagMask (startFlag rs a) M.positions) ∧
  (∀ p<37, M.letters[p]?.getD 0=flagMask (letterFlag p) M.positions) ∧
  (∀ r<37, M.ends[r]?.getD 0=flagMask (endFlag r) M.positions) ∧
  M.cont=flagMask contFlag M.positions ∧ ∀ i<M.positions.length, M.linkOK i=true

def Safe (M : Machine) (mem : Nat) (ps : List Nat) (b : Nat) : Prop :=
  ∀ i e, M.positions[i]?=some e → mem.testBit i=true → ¬ patternFits e.pat.word e.pat.right ps b

theorem safe_zero (M : Machine) (ps b) : M.Safe 0 ps b := by
  intro i e h bit; simp at bit

def active (M : Machine) (a p mem : Nat) := (mem ||| M.starts[a]?.getD 0) &&& M.letters[p]?.getD 0
def following (M : Machine) (active : Nat) := (active &&& M.cont)*2

theorem valid_step {M rs} (header : Machine.Header M rs) (rules : ∀ r ∈ rs, Rule.Valid r)
    {a c cs b mem} (served : Served a (c::cs) b) (good : ValidCols (c::cs))
    (old : M.Safe mem (masses (c::cs)) b) (ha : a<37) (hp : c.card<37)
    (hr : rightSupply cs b<37) :
    let A := M.active a c.card mem
    A &&& M.ends[rightSupply cs b]?.getD 0 = 0 ∧ M.Safe (M.following A) (masses cs) b := by
  let A := M.active a c.card mem
  have activeAt (i : Nat) (hit : A.testBit i=true) :
      ∃ e, M.positions[i]?=some e ∧ letterFlag c.card e=true ∧
        ¬ patternFits e.pat.word e.pat.right (masses (c::cs)) b := by
    change ((mem ||| _) &&& _).testBit i = true at hit
    rw [Nat.testBit_and,Nat.testBit_or,header.2.1 _ hp] at hit
    simp only [Bool.and_eq_true,Bool.or_eq_true] at hit
    obtain ⟨e,he,mass⟩ := flagMask_witness hit.2
    refine ⟨e,he,mass,?_⟩
    rcases hit.1 with carry|start
    · exact old _ _ he carry
    · rw [header.1 _ ha,flagMask_bit,he] at start
      change startFlag rs a e = true at start
      unfold startFlag at start
      split at start
      next r h =>
        obtain ⟨le,pat⟩ := of_decide_eq_true start
        rw [pat]
        exact rejects_rule (rules r (List.mem_of_getElem? h)) served good le
      next => contradiction
  constructor
  · by_contra nz
    obtain ⟨i,hit,last⟩ := overlap nz
    obtain ⟨e,he,mass,impossible⟩ := activeAt i hit
    rw [header.2.2.1 _ hr,flagMask_bit,he] at last
    change endFlag (rightSupply cs b) e=true at last
    unfold endFlag at last
    split at last
    next u word =>
      apply impossible
      simp only [letterFlag,word] at mass
      rw [word]
      exact ⟨of_decide_eq_true mass, (show rightSupply cs b ≤ e.pat.right from of_decide_eq_true last)⟩
    next => contradiction
  · intro j child childAt nextBit
    change ((A &&& M.cont)*2).testBit j=true at nextBit
    cases j with
    | zero => simp [Nat.testBit_zero] at nextBit
    | succ i =>
      rw [Nat.testBit_succ, Nat.mul_div_cancel _ (by decide : 0<2), Nat.testBit_and] at nextBit
      simp only [Bool.and_eq_true] at nextBit
      obtain ⟨parent,atParent,mass,impossible⟩ := activeAt i nextBit.1
      have cont := nextBit.2
      rw [header.2.2.2.1,flagMask_bit,atParent] at cont
      change contFlag parent=true at cont
      have lk := header.2.2.2.2 i (List.getElem?_eq_some_iff.mp atParent).choose
      simp only [linkOK,atParent,cont,Bool.not_true,Bool.false_or,childAt,decide_eq_true_eq] at lk
      intro bad
      apply impossible
      cases word : parent.pat.word with
      | nil => simp [letterFlag,word] at mass
      | cons u us =>
        simp [letterFlag,word] at mass
        rw [word] at lk
        rw [← lk.2]
        exact ⟨mass,by simpa [lk.1,masses] using bad⟩

theorem safe_weaken {M : Machine} {strong weak ps b} (h : M.Safe strong ps b)
    (sub : weak &&& strong=weak) : M.Safe weak ps b := by
  intro i e atI bit
  have keep := congrArg (fun n : Nat => n.testBit i) sub
  simp only [Nat.testBit_and,bit,Bool.true_and] at keep
  exact h i e atI keep

end Machine
end Staircase
