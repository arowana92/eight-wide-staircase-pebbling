module

public import Staircase.Finite

@[expose] public section
namespace Staircase

def Batch (f : Nat → Bool) (start len : Nat) := ∀ i<len, f (start+i)=true

theorem batch_checked {f start len} (h : every len (fun i => f (start+i))=true) :
    Batch f start len := every_iff.mp h

theorem batch_join {f start a b} (left : Batch f start a) (right : Batch f (start+a) b) :
    Batch f start (a+b) := by
  intro i hi
  by_cases cut : i<a
  · exact left i cut
  · have h := right (i-a) (by omega)
    rwa [show start+a+(i-a)=start+i by omega] at h

end Staircase
