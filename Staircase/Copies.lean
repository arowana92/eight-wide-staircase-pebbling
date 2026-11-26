module

public import Staircase.Upper

@[expose] public section
namespace Staircase

theorem solvable_append {m n P Q} (hp : Solvable m P) (hq : Solvable n Q) :
    Solvable (m+n) (P+Q.map (·+4*m)) := by
  constructor
  · intro u hu
    rcases Multiset.mem_add.mp hu with h|h
    · have := hp.1 u h; omega
    · obtain ⟨v,hv,rfl⟩ := Multiset.mem_map.mp h
      have := hq.1 v hv; omega
  · intro t ht
    by_cases left : t<4*m
    · exact (reaches_widen (by omega) (hp.2 t left)).add _
    · have reach := reaches_embed (N := m+n) m (by omega) (hq.2 (t-4*m) (by omega))
      rw [show t-4*m+4*m=t by omega] at reach
      exact reach.mono (Multiset.le_add_left ..)

theorem solvable_copies {n P} (h : Solvable n P) (k : Nat) :
    ∃ Q : Stock, Solvable (k*n) Q ∧ Q.card=k*P.card := by
  induction k with
  | zero => exact ⟨0,⟨by simp, by simp⟩,by simp⟩
  | succ k ih =>
    obtain ⟨Q,hQ,mass⟩ := ih
    refine ⟨_,by simpa [Nat.succ_mul] using solvable_append hQ h,?_⟩
    simp [mass,Nat.succ_mul]

theorem amplify_lower
    (bound : ∀ n (P : Stock), Solvable n P → (-56 : Int) ≤ 16*(P.card : Int)-20*n)
    {n P} (h : Solvable n P) : (5*n+3)/4 ≤ P.card := by
  obtain ⟨Q,hQ,mass⟩ := solvable_copies h 15
  have result := bound _ _ hQ
  rw [mass] at result
  omega

end Staircase
