module

public import Staircase.Graph
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Multiset.Replicate

@[expose] public section
namespace Staircase

/-- Replace the exterior hub h by half its stock at b; send other tokens through f. -/
def pool (h b : Nat) (f : Nat → Nat) (P : Stock) : Stock :=
  Multiset.replicate (P.count h/2) b + (P.filter (· ≠ h)).map f

theorem pool_other {h b f P u} (hu : u ≠ h) :
    pool h b f (u ::ₘ P) = f u ::ₘ pool h b f P := by
  simp [pool, Multiset.count_cons_of_ne (Ne.symm hu), Multiset.filter_cons_of_pos (p := (· ≠ h)) _ hu]

theorem pool_two (h b f P) : pool h b f (h ::ₘ h ::ₘ P) = b ::ₘ pool h b f P := by
  simp only [pool, Multiset.count_cons_self, Multiset.filter_cons_of_neg (p := (· ≠ h)) _ (not_not_intro rfl)]
  rw [show (P.count h+1+1)/2 = P.count h/2+1 by omega, Multiset.replicate_succ,
      Multiset.cons_add]

theorem pool_one (h b f P) : pool h b f (h ::ₘ P) ≤ b ::ₘ pool h b f P := by
  simp only [pool, Multiset.count_cons_self, Multiset.filter_cons_of_neg (p := (· ≠ h)) _ (not_not_intro rfl)]
  rw [← Multiset.cons_add, ← Multiset.replicate_succ]
  exact Multiset.add_le_add_right ((Multiset.replicate_le_replicate b).2 (show (P.count h+1)/2 ≤ P.count h/2+1 by omega))

theorem Reaches.pool {E D P t} (h b : Nat) (f : Nat → Nat)
    (incoming : ∀ u, E u h → f u = b) (outgoing : ∀ v, E h v → f v = b)
    (internal : ∀ u v, u ≠ h → v ≠ h → E u v → D (f u) (f v))
    (p : Reaches E P t) (keep : t ≠ h) : Reaches D (pool h b f P) (f t) := by
  induction p with
  | occupied ht =>
    apply Reaches.occupied
    exact Multiset.mem_add.mpr (.inr (Multiset.mem_map_of_mem _ (Multiset.mem_filter.mpr ⟨ht,keep⟩)))
  | @move u v t rest edge _ ih =>
    have after := ih keep
    by_cases hu : u = h
    · subst u
      rw [pool_two]
      by_cases hv : v = h
      · subst v; exact after.mono (pool_one ..)
      · rwa [pool_other hv, outgoing _ edge] at after
    · rw [pool_other hu, pool_other hu]
      by_cases hv : v = h
      · subst v
        rw [incoming _ edge]
        exact after.mono ((pool_one ..).trans (Multiset.le_cons_self ..))
      · rw [pool_other hv] at after
        exact .move (internal _ _ hu hv edge) after

theorem pool_separate (h b f a) (Q : Stock) (free : h ∉ Q) :
    pool h b f (Multiset.replicate a h + Q) = Multiset.replicate (a/2) b + Q.map f := by
  have hf : Q.filter (· ≠ h) = Q := Multiset.filter_eq_self.mpr (by
    intro u hu eq; exact free (eq ▸ hu))
  have hempty : (Multiset.replicate a h).filter (· ≠ h) = 0 :=
    Multiset.filter_eq_nil.mpr (by intro u hu; simpa using Multiset.eq_of_mem_replicate hu)
  simp [pool, Multiset.count_eq_zero.mpr free, Multiset.filter_add, hf, hempty]

end Staircase
