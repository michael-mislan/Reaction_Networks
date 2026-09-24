import proofs.RAF.Frankl.ProjectionCriterion

namespace RAF.Frankl.ExtensionExample

open RAF RAFQueryCompilation

/-- Food 0; the third reaction consumes the core product 3 and feeds catalyst
2 back to the first reaction. This is the guide's genuine-feedback example. -/
def source : CRS (Fin 5) (Fin 3) where
  food := {0}
  inputs := fun r => if r = 2 then {3} else {0}
  outputs := fun r => if r = 0 then {1} else if r = 1 then {2,3} else {2,4}

def catalysts (x : Fin 5) (r : Fin 3) : Prop :=
  if r = 0 then x = 2 else if r = 1 then x = 1 else x = 0

instance (x : Fin 5) (r : Fin 3) : Decidable (catalysts x r) := by
  unfold catalysts
  infer_instance

def core : Finset (Fin 3) := {0,1}

theorem core_food_ready : ∀ r ∈ core, SeedReaction source r := by
  unfold SeedReaction
  decide

theorem isolated_core : evaluate source catalysts core = core := by decide

theorem genuine_feedback : 2 ∉ core ∧ 2 ∈ source.outputs 2 ∧
    catalysts 2 0 ∧ 0 ∈ core ∧ ¬ SeedReaction source 2 := by
  unfold SeedReaction
  decide

/-- The literal example consumes the general theorem; no abundance fact is
assumed as an interface input or taken from numerical enumeration. -/
theorem abundant_core_reaction :
    ∃ r ∈ core, (fixedFamily source catalysts).card ≤
      2 * ((fixedFamily source catalysts).filter (fun W => r ∈ W)).card := by
  have hn : (evaluate source catalysts core).Nonempty := by
    rw [isolated_core]
    decide
  simpa only [isolated_core] using
    elementary_maxRAF_exists_abundant source catalysts core core_food_ready hn

end RAF.Frankl.ExtensionExample
