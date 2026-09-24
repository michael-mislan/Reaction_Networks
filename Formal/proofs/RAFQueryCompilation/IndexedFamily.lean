import proofs.RAFQueryCompilation.FamilyCost
import proofs.RAFQueryCompilation.BudgetQueryComplete
import proofs.RAFQueryCompilation.HybridQuery

namespace RAFQueryCompilation.ModuleFamily
open RAF

def reactionCode (n : ℕ) : Reaction n ≃ Fin (n*2+1) :=
  (Equiv.optionCongr ((Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans
    finProdFinEquiv)).trans (finSuccEquiv (n*2)).symm

def moleculeCode (n : ℕ) : Molecule n ≃ Fin (n*2+1+1) :=
  (Equiv.optionCongr (reactionCode n)).trans (finSuccEquiv (n*2+1)).symm

/-- Literal source relabeling by computable bijections, with no reaction identification. -/
def indexedSource (n : ℕ) : CRS (Fin (n*2+1+1)) (Fin (n*2+1)) where
  inputs r := ((source n).inputs ((reactionCode n).symm r)).map (moleculeCode n).toEmbedding
  outputs r := ((source n).outputs ((reactionCode n).symm r)).map (moleculeCode n).toEmbedding
  food := ((source n).food).map (moleculeCode n).toEmbedding

def indexedCats (n : ℕ) (r : Fin (n*2+1)) : Finset (Fin (n*2+1+1)) :=
  (familyCats ((reactionCode n).symm r)).map (moleculeCode n).toEmbedding

def indexedRegion {n : ℕ} (i : Fin n) : Finset (Fin (n*2+1)) :=
  (region i).map (reactionCode n).toEmbedding

def indexedCertificate {n : ℕ} (i : Fin n) : List (List (Fin (n*2+1))) :=
  (pairCertificate i).map (List.map (reactionCode n))

@[simp] theorem indexed_region_card {n : ℕ} (i : Fin n) : (indexedRegion i).card = 2 := by
  simp [indexedRegion, region_card]

@[simp] theorem indexed_input_card {n : ℕ} (r : Fin (n*2+1)) :
    ((indexedSource n).inputs r).card = 1 := by simp [indexedSource, source]

@[simp] theorem indexed_output_card {n : ℕ} (r : Fin (n*2+1)) :
    ((indexedSource n).outputs r).card = 1 := by simp [indexedSource, source]

@[simp] theorem indexed_catalyst_card {n : ℕ} (r : Fin (n*2+1)) :
    (indexedCats n r).card = 1 := by simp [indexedCats, familyCats]

@[simp] theorem indexed_food_card (n : ℕ) : (indexedSource n).food.card = 1 := by
  simp [indexedSource, source]

theorem indexed_needs {n : ℕ} (i : Fin n) (b : Bool) :
    sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)
      (reactionCode n (some (i,b))) =
      {moleculeCode n (some none),moleculeCode n (some (some (i,!b)))} := by
  ext x
  simp [sourceNeeds, indexedSource, indexedCats, source, familyCats]

theorem indexed_successors {n : ℕ} (i : Fin n) (b : Bool) :
    sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r)
      (reactionCode n (some (i,b))) = {reactionCode n (some (i,!b))} := by
  ext r
  obtain ⟨s,rfl⟩ := (reactionCode n).surjective r
  cases s with
  | none => simp [sourceSuccessors, indexedSource, indexedCats, source, familyCats]
  | some p =>
    rcases p with ⟨j,c⟩
    cases b <;> cases c <;>
      simp [sourceSuccessors, indexedSource, indexedCats, source, familyCats, eq_comm]

theorem indexed_envelope {n : ℕ} (i : Fin n) :
    sourceEnvelope (indexedSource n)
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) (indexedRegion i) =
      ({none,some none,some (some (i,false)),some (some (i,true))} : Finset (Molecule n)).map
        (moleculeCode n).toEmbedding := by
  ext x
  simp [sourceEnvelope, indexedRegion, region, indexedSource, source, sourceNeeds, indexedCats, familyCats]
  tauto

theorem indexed_envelope_card {n : ℕ} (i : Fin n) :
    (sourceEnvelope (indexedSource n)
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) (indexedRegion i)).card = 4 := by
  rw [indexed_envelope, Finset.card_map]
  simp

end RAFQueryCompilation.ModuleFamily
