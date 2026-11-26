import Staircase
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if (`Staircase).isPrefixOf env.header.moduleNames[idx]! then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a => !(permitted.contains a)
      unless extra.isEmpty do
        throwError "{name} depends on unapproved axioms {extra}"
      checked := checked + 1
  if checked == 0 then throwError "no Staircase declarations found"
  logInfo m!"Audited {checked} project declarations."

open Staircase Filter Asymptotics

example : ∀ n : Nat, 0 < n →
    (5*n+3)/4 ≤ optimal n ∧ optimal n ≤ (5*n+3)/4+3 := optimal_bounds

example : ∀ {n : Nat}, 0 < n → ∀ {P : Stock}, Solvable n P → (5*n+3)/4 ≤ P.card :=
  @solvable_lower

example : (fun n : Nat => (optimal n : ℝ)-5*(n:ℝ)/4) =O[atTop] (fun _ : Nat => (1:ℝ)) :=
  conjecture32

#print axioms Staircase.conjecture32
#print axioms Staircase.optimal_bounds
#print axioms Staircase.solvable_lower
#print axioms Staircase.windowRules_valid
#print axioms Staircase.Certificate.rows
#print axioms Staircase.adj_iff_grid
