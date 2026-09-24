import proofs.IrrRAFEnumeration.ProductComposition
import Mathlib.Combinatorics.SetFamily.Shatter

namespace IrrRAFEnumeration

/-- One fixed universal vertex in every outer-product stage. -/
def stagedUniversalSample {r b : Nat} (block : Fin b) :
    Finset (StagedProductVertex r b) :=
  Finset.univ.image fun stage : Fin r =>
    (stage, (block, Sum.inr (0 : Fin 3)))

theorem stagedUniversalSample_card {r b : Nat} (block : Fin b) :
    (stagedUniversalSample block : Finset (StagedProductVertex r b)).card = r := by
  classical
  rw [stagedUniversalSample, Finset.card_image_iff.mpr]
  · simp
  · intro left _ right _ h
    exact congrArg Prod.fst h

/-- The blocker product independently realizes either trace value at every
sampled stage.  Thus its VC dimension grows at least linearly with the number
of independent stages; the bounded-VC trace algorithm cannot bypass this
counterfamily. -/
theorem stagedProduct_blocker_vcDim_ge {r b : Nat} (block : Fin b) :
    r ≤ (blocker (stagedProductFamily r b)).vcDim := by
  classical
  have hshatters : (blocker (stagedProductFamily r b)).Shatters
      (stagedUniversalSample block) := by
    intro trace htrace
    let parts : Fin r → Finset (ProductVertex b) := fun stage =>
      if (stage, (block, Sum.inr (0 : Fin 3))) ∈ trace then
        {(block, Sum.inr (0 : Fin 3))}
      else
        {(block, Sum.inr (1 : Fin 3))}
    refine ⟨assembleStages parts, ?_, ?_⟩
    · rw [mem_blocker_stagedProductFamily_iff]
      intro stage
      rw [stageSection_assembleStages]
      dsimp [parts]
      split_ifs <;> simp [switchProductDual, universalBlockers]
    · ext vertex
      rcases vertex with ⟨stage, vertex⟩
      constructor
      · intro hvertex
        have hsample := (Finset.mem_inter.mp hvertex).1
        have hassembled := (Finset.mem_inter.mp hvertex).2
        obtain ⟨sampleStage, _, heq⟩ := Finset.mem_image.mp hsample
        have hstage : sampleStage = stage := congrArg Prod.fst heq
        subst sampleStage
        have hvertexValue : vertex = (block, Sum.inr (0 : Fin 3)) :=
          (congrArg Prod.snd heq).symm
        subst vertex
        have : (stage, (block, Sum.inr (0 : Fin 3))) ∈ trace := by
          by_contra hnot
          simp [assembleStages, parts, hnot, stageLift] at hassembled
        exact this
      · intro hvertex
        have hsampleVertex := htrace hvertex
        obtain ⟨sampleStage, _, heq⟩ := Finset.mem_image.mp hsampleVertex
        have hstage : sampleStage = stage := congrArg Prod.fst heq
        subst sampleStage
        have hvertexValue : vertex = (block, Sum.inr (0 : Fin 3)) :=
          (congrArg Prod.snd heq).symm
        subst vertex
        have hsample : (stage, (block, Sum.inr (0 : Fin 3))) ∈
            stagedUniversalSample block := by
          exact Finset.mem_image.mpr ⟨stage, Finset.mem_univ _, rfl⟩
        have hassembled : (stage, (block, Sum.inr (0 : Fin 3))) ∈
            assembleStages parts := by
          simp [assembleStages, parts, stageLift, hvertex]
        exact Finset.mem_inter.mpr ⟨hsample, hassembled⟩
  calc
    r = (stagedUniversalSample block :
        Finset (StagedProductVertex r b)).card :=
      (stagedUniversalSample_card block).symm
    _ ≤ (blocker (stagedProductFamily r b)).vcDim :=
      hshatters.card_le_vcDim

end IrrRAFEnumeration
