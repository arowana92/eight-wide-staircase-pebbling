module

public import Staircase.Matcher
public import Staircase.Copies

@[expose] public section
namespace Staircase

structure Label where
  left : Nat
  right : Nat
  debt : Nat
  mem : Nat
deriving DecidableEq

structure Dual where
  lefts : Packed
  rights : Packed
  debts : Packed
  memories : Packed
  hints : Packed

namespace Dual

def size (T : Dual) := 1369+T.debts.size

def label (T : Dual) (i : Nat) : Label :=
  if i<1369 then ⟨i/37,i%37,0,0⟩ else
    let j := i-1369
    ⟨T.lefts.read j,T.rights.read j,T.debts.read j,T.memories.read j⟩

def gain (a p r : Nat) := 2*p+(a+1)/2+(r+1)/2

def edgeOK (T : Dual) (M : Machine) (i p r : Nat) : Bool :=
  let x := T.label i
  let A := M.active x.left p x.mem
  decide (x.debt+5 ≤ gain x.left p r) || (A &&& M.ends[r]?.getD 0 != 0) ||
    let j := T.hints.read (74*i+2*p+r%2)
    let y := T.label j
    decide (j<T.size ∧ y.left=p+x.left/2 ∧ y.right=r ∧ x.debt+5≤gain x.left p r+y.debt ∧
      y.mem &&& M.following A=y.mem)

def rowOK (T : Dual) (M : Machine) (i : Nat) : Bool :=
  let x := T.label i
  decide (x.left≤36 ∧ x.right≤36 ∧ x.debt≤14) && every (x.right+1) fun p =>
    T.edgeOK M i p (2*(x.right-p)) && T.edgeOK M i p (2*(x.right-p)+1)

def live (T : Dual) (x : Label) : Prop :=
  (x.debt=0 ∧ x.mem=0) ∨ ∃ i<T.size, T.label i=x

theorem init_label (T : Dual) {a R : Nat} (ha : a<37) (hR : R<37) :
    T.label (37*a+R)=⟨a,R,0,0⟩ := by
  have bound : 37*a+R<1369 := by omega
  simp [label,bound,show (37*a+R)/37=a by omega,show (37*a+R)%37=R by omega]

theorem load_live {T : Dual} {x} (live : T.live x) (la : x.left<37) (ra : x.right<37) :
    ∃ i<T.size,T.label i=x := by
  rcases live with ⟨d,m⟩|found
  · refine ⟨_,?_,(T.init_label la ra).trans ?_⟩
    · unfold size; omega
    · cases x; simp_all
  · exact found

theorem pick {T : Dual} {M rs} (hdr : Machine.Header M rs) (valid : ∀ r∈rs, Rule.Valid r)
    (rows : ∀ i<T.size,T.rowOK M i=true)
    {a c cs b d mem} (served : Served a (c::cs) b) (good : ValidCols (c::cs))
    (live : T.live ⟨a,rightSupply (c::cs) b,d,mem⟩) (limit : d≤14)
    (safe : M.Safe mem (masses (c::cs)) b) :
    ∃ d' mem', T.live ⟨c.card+a/2,rightSupply cs b,d',mem'⟩ ∧ d'≤14 ∧
      M.Safe mem' (masses cs) b ∧ d+5 ≤ gain a c.card (rightSupply cs b) + d' := by
  let p := c.card
  let r := rightSupply cs b
  let R := p+r/2
  change T.live ⟨a,R,d,mem⟩ at live
  by_cases easy : d+5 ≤ gain a p r
  · exact ⟨0,0,Or.inl ⟨rfl,rfl⟩,by decide,M.safe_zero _ _,by simpa [p,r] using easy⟩
  · have ha : a<37 := by unfold gain at easy; omega
    have hp : p<37 := by unfold gain at easy; omega
    have hr : r<37 := by unfold gain at easy; omega
    have hR : R<37 := by dsimp [R]; unfold gain at easy; omega
    obtain ⟨i,hi,hx⟩ := load_live live ha hR
    have row := rows i hi
    simp only [rowOK,hx,Bool.and_eq_true,every_iff] at row
    have pm : p < R+1 := by dsimp [R]; omega
    have opt := row.2 p pm
    have next : T.edgeOK M i p r = true := by
      by_cases even : r=2*(R-p)
      · simpa only [← even] using opt.1
      · have odd : r=2*(R-p)+1 := by dsimp [R] at *; omega
        simpa only [← odd] using opt.2
    have sound := M.valid_step hdr valid served good safe ha hp hr
    change (M.active a p mem &&& M.ends[r]?.getD 0=0) ∧ _ at sound
    simp only [edgeOK,hx,Bool.or_eq_true,decide_eq_true_eq,easy,sound.1, show (0 != (0:Nat))=false by decide,
      Bool.false_eq_true,false_or] at next
    let j := T.hints.read (74*i+2*p+r%2)
    let y := T.label j
    change j<T.size ∧ y.left=p+a/2 ∧ y.right=r ∧ d+5≤gain a p r+y.debt ∧ _ at next
    obtain ⟨hj,yl,yr,cost,inc⟩ := next
    have desc : T.label j=⟨p+a/2,r,y.debt,y.mem⟩ := by
      change y=_; rw [← yl,← yr]
    have ybd := rows j hj
    simp only [rowOK,Bool.and_eq_true,decide_eq_true_eq] at ybd
    exact ⟨y.debt,y.mem,Or.inr ⟨j,hj,desc⟩,ybd.1.2.2,M.safe_weaken sound.2 inc,cost⟩

def potential (a r d : Nat) : Int := -4*(d:Int)+4*((a:Int)-(r:Int))

theorem strip_bound {T : Dual} {M rs} (hdr : Machine.Header M rs)
    (valid : ∀ r∈rs, Rule.Valid r) (rows : ∀ i<T.size,T.rowOK M i=true)
    (cs : Columns) (a b d mem : Nat) (served : Served a cs b) (good : ValidCols cs)
    (live : T.live ⟨a,rightSupply cs b,d,mem⟩) (limit : d≤14) (safe : M.Safe mem (masses cs) b) :
    -56-4*(b:Int)-potential a (rightSupply cs b) d ≤
      16*((masses cs).sum:Int)-20*(cs.length:Int) := by
  induction cs generalizing a d mem with
  | nil =>
    simp only [rightSupply,masses,List.map_nil,List.foldr_nil,List.sum_nil,List.length_nil,
      Int.ofNat_zero,potential]
    omega
  | cons c cs ih =>
    obtain ⟨e,s,live',lim',safe',cost⟩ := pick hdr valid rows served good live limit safe
    have tail := ih _ _ _ (trim_left (fun u hu => good c (.head _) u hu) served)
      (fun k hk => good k (.tail _ hk)) live' lim' safe'
    have stepR : rightSupply (c::cs) b=c.card+rightSupply cs b/2 := rfl
    rw [stepR]
    change _ ≤ 16*((c.card+(masses cs).sum : Nat):Int)-20*((cs.length+1 : Nat):Int)
    unfold potential at *
    unfold gain at cost
    omega

theorem optimal_lower {T : Dual} {M rs} (hdr : Machine.Header M rs)
    (valid : ∀ r∈rs, Rule.Valid r) (rows : ∀ i<T.size,T.rowOK M i=true)
    {n : Nat} (hn : 0<n) : (5*n+3)/4 ≤ optimal n := by
  obtain ⟨X,sol,hX⟩ := (optimal_spec hn).1
  rw [← hX]
  apply amplify_lower _ sol
  intro k P hp
  obtain ⟨cs,len,good,flat⟩ := stock_columns k P hp.1
  have h := strip_bound hdr valid rows cs 0 0 0 0 (full_served hp len flat) good
    (Or.inl ⟨rfl,rfl⟩) (by decide) (M.safe_zero _ _)
  rw [← flatten_mass,flat,len] at h
  unfold potential at h
  omega

end Dual
end Staircase
