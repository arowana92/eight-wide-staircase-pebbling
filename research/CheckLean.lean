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

example : ∀ n : Nat, 0 < n → Staircase.optimal n ≤ (5*n+3)/4+3 :=
  fun _ h => Staircase.optimal_upper h

#print axioms Staircase.optimal_upper
#print axioms Staircase.adj_iff_grid
