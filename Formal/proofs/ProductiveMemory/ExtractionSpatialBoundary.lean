import proofs.ProductiveMemory.ExtractionSpatialPopulation
import proofs.ResourceLimitedCompetition.SpatialPopulationBoundary

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition
noncomputable section
set_option Elab.async false

theorem productive_replacement_frame (F : TaggedCell → ℝ) (s : PopulationState)
    (i : Fin s.live.length) (c : TaggedCell) :
    potentialSum F s-F (selectedCell s i)+F c =
      ((s.live.take i.val).map F).sum+F c+((s.live.drop (i.val+1)).map F).sum := by
  have h := congrArg (fun cs : List TaggedCell => (cs.map F).sum) (selected_decomposition s i)
  simp only [List.map_append,List.map_cons,List.sum_append,List.sum_cons] at h
  unfold potentialSum
  linarith only [h]

theorem productive_raw_nonneg (F : TaggedCell → ℝ) (hF : ∀ c, 0 ≤ F c)
    (s : ProductiveState) (e : ProductiveEvent s) : 0 ≤ productiveRawPotential F s e := by
  cases e with
  | inl e => exact raw_potential_nonneg F hF s.population e
  | inr i =>
    dsimp [productiveRawPotential]
    rw [productive_replacement_frame]
    exact add_nonneg (add_nonneg (sum_map_nonneg F hF _) (hF _)) (sum_map_nonneg F hF _)

theorem productive_active_births (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (s : ProductiveActive D) (i : Fin s.val.population.live.length)
    (d : {d : Counts // d ∈ daughterDraws (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1})
    (h : productiveReason N W0 J rho zL zH ⟨s,.inl ⟨i,.inr d⟩⟩=.active)
    (hm : (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N) :
    extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,(d.val,N)⟩ < 4*readyLevel ∧
      extractionCellEnergy rho zL zH ⟨(selectedCell s.val.population i).high,
        ((fun j => (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1 j-d.val j),N)⟩ < 4*readyLevel := by
  classical
  simp only [productiveReason] at h
  split_ifs at h
  simp_all

def productiveSpatialObservable (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) :
    ProductiveStopped D → ℝ := by
  classical
  exact fun x => match x with
  | .inl s => potentialSum (extractionCellSpatial N rho zL zH) s.val.population
  | .inr e => if productiveReason N W0 J rho zL zH e=.divisionEnergy
      then Real.exp (2*(N:ℝ)*localAlpha*readyLevel) else 0

theorem productive_spatial_nonneg (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (x : ProductiveStopped D) : 0 ≤ productiveSpatialObservable N W0 J rho zL zH D x := by
  classical
  cases x with
  | inl s => exact sum_map_nonneg _ (extraction_spatial_nonneg N rho zL zH) _
  | inr e => simp only [productiveSpatialObservable]; split_ifs <;> positivity

theorem productive_active_spatial_outcome (N W0 J : ℕ)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH : ℝ)
    (D : Finset ProductiveState) (s : ProductiveActive D) (e : ProductiveEvent s.val)
    (ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active) :
    potentialSum (extractionCellSpatial N rho zL zH) (productiveOutcome N s.val e).population ≤
      productiveRawPotential (extractionCellSpatial N rho zL zH) s.val e := by
  classical
  cases e with
  | inl e =>
    rcases e with ⟨i,r | d⟩
    · simp only [productiveRawPotential,rawEventPotential]
      rw [raw_selected_frame]
      simp [productiveOutcome,residentAt,potentialSum,List.sum_append,add_assoc]
    · simp only [productiveRawPotential,rawEventPotential]
      rw [raw_selected_frame]
      by_cases hm : (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N
      · have hg := productive_active_births N W0 J rho zL zH D s i d ha hm
        have hr := extraction_spatial_pair_reset N hlarge rho zL zH (selectedCell s.val.population i).high
          (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1 d.val hg
        have hp : ((nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1,2*N)=
            nextCompartment (selectedCell s.val.population i).compartment (.inr ()) := by rw [← hm]
        rw [hp] at hr
        simp only [productiveOutcome,growthAt,hm,if_true,potentialSum,List.map_append,List.map_cons,List.sum_append,List.sum_cons]
        linarith only [hr]
      · simp [productiveOutcome,growthAt,hm,potentialSum,List.sum_append,add_assoc]
  | inr i =>
    dsimp [productiveRawPotential]
    rw [productive_replacement_frame]
    simp [productiveOutcome,extractionAt,potentialSum,List.sum_append,add_assoc]

theorem productive_division_raw_barrier (N W0 J : ℕ) (rho zL zH : ℝ)
    (D : Finset ProductiveState) (s : ProductiveActive D) (e : ProductiveEvent s.val)
    (hd : productiveReason N W0 J rho zL zH ⟨s,e⟩=.divisionEnergy) :
    Real.exp (2*(N:ℝ)*localAlpha*readyLevel) ≤
      productiveRawPotential (extractionCellSpatial N rho zL zH) s.val e := by
  classical
  cases e with
  | inr i => simp only [productiveReason] at hd; split_ifs at hd
  | inl e =>
    rcases e with ⟨i,r | d⟩
    · simp only [productiveReason] at hd; split_ifs at hd
    · have hb : (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).2=2*N ∧
          2*readyLevel < extractionCellEnergy rho zL zH
            ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩ := by
        simp only [productiveReason] at hd
        split_ifs at hd
        simp_all
      have hp := extraction_spatial_division_barrier N rho zL zH
        ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩ hb.1 hb.2.le
      simp only [productiveRawPotential,rawEventPotential]
      rw [raw_selected_frame]
      have hl := sum_map_nonneg _ (extraction_spatial_nonneg N rho zL zH) (s.val.population.live.take i.val)
      have hr := sum_map_nonneg _ (extraction_spatial_nonneg N rho zL zH) (s.val.population.live.drop (i.val+1))
      linarith only [hp,hl,hr]

theorem productive_spatial_next_le_raw (N W0 J : ℕ)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH : ℝ)
    (D : Finset ProductiveState) (s : ProductiveActive D) (e : ProductiveEvent s.val) :
    productiveSpatialObservable N W0 J rho zL zH D
      (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩) ≤
      productiveRawPotential (extractionCellSpatial N rho zL zH) s.val e := by
  classical
  have hn := productive_raw_nonneg _ (extraction_spatial_nonneg N rho zL zH) s.val e
  simp only [productiveStoppedNext,if_true]
  by_cases ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active
  · simp only [ha,if_true]
    split_ifs
    · exact productive_active_spatial_outcome N W0 J hlarge rho zL zH D s e ha
    · simpa [productiveSpatialObservable,ha] using hn
  · simp only [ha,if_false,productiveSpatialObservable]
    split_ifs with hd
    · exact productive_division_raw_barrier N W0 J rho zL zH D s e hd
    · exact hn

end
end ProductiveMemory
