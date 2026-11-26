module

public import Staircase.WindowData.R228
public import Staircase.WindowData.R229
public import Staircase.WindowData.R230
public import Staircase.WindowData.R227

@[expose] public section
namespace Staircase

def windowRules : List Rule := WindowData.R228.rules ++ WindowData.R229.rules ++
  WindowData.R230.rules ++ WindowData.R227.rules

theorem windowRules_valid (r : Rule) (h : r ∈ windowRules) : r.Valid := by
  simp only [windowRules,List.mem_append] at h
  rcases h with ((a|b)|c)|d
  · exact WindowData.R228.all_valid r a
  · exact WindowData.R229.all_valid r b
  · exact WindowData.R230.all_valid r c
  · exact WindowData.R227.all_valid r d

end Staircase
