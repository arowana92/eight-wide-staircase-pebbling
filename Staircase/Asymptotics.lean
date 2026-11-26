module

public import Staircase.Resolution
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section
namespace Staircase

open Filter Asymptotics

/-- Conjecture 3.2 of Győri, Katona, Papp and Tompkins. -/
def Conjecture32 : Prop :=
  (fun n : Nat => (optimal n : ℝ) - 5*(n : ℝ)/4) =O[atTop] (fun _ : Nat => (1 : ℝ))

theorem conjecture32 : Conjecture32 := by
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  obtain ⟨lower, upper⟩ := optimal_bounds n (by omega)
  have lo : 5*n ≤ 4*optimal n := by omega
  have hi : 4*optimal n ≤ 5*n+15 := by omega
  have lo' : 5*(n:ℝ) ≤ 4*(optimal n:ℝ) := by exact_mod_cast lo
  have hi' : 4*(optimal n:ℝ) ≤ 5*(n:ℝ)+15 := by exact_mod_cast hi
  have nonneg : 0 ≤ (optimal n:ℝ)-5*(n:ℝ)/4 := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one, abs_of_nonneg nonneg]
  linarith

end Staircase
