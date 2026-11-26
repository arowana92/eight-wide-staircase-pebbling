module

public import Staircase.Header
public import Staircase.DualPart0
public import Staircase.DualPart1
public import Staircase.DualPart2
public import Staircase.DualPart3
public import Staircase.AllWindows
public import Staircase.Upper

@[expose] public section
namespace Staircase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Certificate

theorem rows : ∀ i<dual.size, dual.rowOK machine i=true := by
  have allRows : Batch stateTest 0 6516 :=
    batch_join (batch_join states0 states1) (batch_join states2 states3)
  have size : dual.size=6516 := by decide +kernel
  intro i hi
  rw [size] at hi
  simpa only [Nat.zero_add,stateTest] using allRows i hi

theorem rules_valid (r : Rule) (h : r ∈ listedRules) : r.Valid := by
  have eq : listedRules=windowRules := by decide +kernel
  exact windowRules_valid r (eq ▸ h)

end Certificate

/-- Uniform upper and lower bounds on the optimum for every positive strip length. -/
theorem optimal_bounds (n : Nat) (hn : 0<n) :
    (5*n+3)/4 ≤ optimal n ∧ optimal n ≤ (5*n+3)/4+3 :=
  ⟨Dual.optimal_lower Certificate.header Certificate.rules_valid Certificate.rows hn,
   optimal_upper hn⟩

/-- Every solvable distribution obeys the lower bound, with unrestricted pile sizes. -/
theorem solvable_lower {n : Nat} (hn : 0<n) {P : Stock} (sol : Solvable n P) :
    (5*n+3)/4 ≤ P.card :=
  (optimal_bounds n hn).1.trans ((optimal_spec hn).2 P sol)

end Staircase
