import proofs.ProductiveMemory.ExtractionPopulationSource
import proofs.HeritableCompositions.PartitionDaughters
import proofs.SerialTransferSelection.DiscardAccounting

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
noncomputable section
set_option Elab.async false

def chemicalInventory (cs : List TaggedCell) (j : Fin 4) : ℝ :=
  (cs.map (fun c => (c.compartment.1 j:ℝ))).sum

theorem resident_inventory_change (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell)
    (b : List TaggedCell) (r : Fin 13) (hr : reactants c.compartment.1 r) (j : Fin 4) :
    chemicalInventory (residentAt Q D a c b r).live j =
      chemicalInventory (sourceAt Q D a c b).live j+jump r j := by
  simp only [chemicalInventory,residentAt,sourceAt,List.map_append,List.map_cons,List.sum_append,List.sum_cons,nextCompartment]
  rw [nextCounts_cast _ r hr j]
  ring

theorem growth_inventory_change (N Q D : ℕ) (a : List TaggedCell) (c : TaggedCell)
    (b : List TaggedCell) (d : Counts)
    (hd : d ∈ daughterDraws (nextCompartment c.compartment (.inr ())).1)
    (hz : 1 ≤ c.compartment.1 2) (j : Fin 4) :
    chemicalInventory (growthAt N Q D a c b d).live j =
      chemicalInventory (sourceAt Q D a c b).live j-membraneDirection j := by
  have hcast := membrane_count_update c.compartment hz j
  have hdraw := daughter_draw_le _ d hd j
  dsimp only [growthAt]
  split_ifs
  · simp only [chemicalInventory,sourceAt,List.map_append,List.map_cons,List.sum_append,List.sum_cons,
      Nat.cast_sub hdraw]
    linarith only [hcast]
  · simp only [chemicalInventory,sourceAt,List.map_append,List.map_cons,List.sum_append,List.sum_cons]
    linarith only [hcast]

theorem extraction_inventory_change (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell)
    (b : List TaggedCell) (hz : 1 ≤ c.compartment.1 2) (j : Fin 4) :
    chemicalInventory (extractionAt Q D a c b).live j =
      chemicalInventory (sourceAt Q D a c b).live j+channelJump (.inr ()) j := by
  simp only [chemicalInventory,extractionAt,sourceAt,List.map_append,List.map_cons,List.sum_append,List.sum_cons]
  rw [channel_next_cast _ (.inr ()) hz j]
  ring

def productiveInternalProduction (s : ProductiveState) : ProductiveEvent s → ℝ
  | .inl ⟨_,.inl r⟩ => jump r 2
  | _ => 0

def productiveGrowthMark (s : ProductiveState) : ProductiveEvent s → ℕ
  | .inl ⟨_,.inr _⟩ => 1
  | _ => 0

def ProductiveEnabled (s : ProductiveState) : ProductiveEvent s → Prop
  | .inl ⟨i,.inl r⟩ => reactants (selectedCell s.population i).compartment.1 r
  | .inl ⟨i,.inr _⟩ => 1 ≤ (selectedCell s.population i).compartment.1 2
  | .inr i => 1 ≤ (selectedCell s.population i).compartment.1 2

theorem productive_z_account_step (N : ℕ) (s : ProductiveState) (e : ProductiveEvent s)
    (he : ProductiveEnabled s e) :
    chemicalInventory (productiveOutcome N s e).population.live 2+
      ((productiveOutcome N s e).collected:ℝ)+(productiveGrowthMark s e:ℝ) =
      chemicalInventory s.population.live 2+(s.collected:ℝ)+productiveInternalProduction s e := by
  rcases e with ⟨i,r | d⟩ | i
  · have h := resident_inventory_change s.population.resource s.population.divisions
      (s.population.live.take i.val) (selectedCell s.population i) (s.population.live.drop (i.val+1)) r he 2
    rw [sourceAt_selected] at h
    simp only [productiveOutcome,productiveGrowthMark,productiveInternalProduction,Nat.cast_zero]
    linarith only [h]
  · have h := growth_inventory_change N s.population.resource s.population.divisions
      (s.population.live.take i.val) (selectedCell s.population i) (s.population.live.drop (i.val+1)) d.val d.property he 2
    rw [sourceAt_selected] at h
    norm_num [membraneDirection,Matrix.cons_val_two] at h
    simp only [productiveOutcome,productiveGrowthMark,productiveInternalProduction,Nat.cast_one]
    linarith only [h]
  · have h := extraction_inventory_change s.population.resource s.population.divisions
      (s.population.live.take i.val) (selectedCell s.population i) (s.population.live.drop (i.val+1)) he 2
    rw [sourceAt_selected] at h
    norm_num [channelJump,Matrix.cons_val_two] at h
    simp only [productiveOutcome,productiveGrowthMark,productiveInternalProduction,Nat.cast_zero]
    push_cast
    linarith only [h]

end
end ProductiveMemory
