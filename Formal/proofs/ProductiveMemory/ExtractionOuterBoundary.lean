import proofs.ProductiveMemory.ExtractionOuter

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition
noncomputable section
set_option Elab.async false

def productiveOuterObservable (N M W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) :
    ProductiveStopped D → ℝ := by
  classical
  exact fun x => match x with
  | .inl s => potentialSum (extractionCellOuter N rho zL zH) s.val.population+
      productiveOuterReserve N M s.val.population.divisions
  | .inr e => if productiveReason N W0 J rho zL zH e=.outer
      then Real.exp ((N:ℝ)*localAlpha*(8*readyLevel)) else 0

theorem productive_active_outer_outcome (N M W0 J : ℕ) (rho zL zH : ℝ)
    (D : Finset ProductiveState) (s : ProductiveActive D) (e : ProductiveEvent s.val)
    (ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active) :
    potentialSum (extractionCellOuter N rho zL zH) (productiveOutcome N s.val e).population+
      productiveOuterReserve N M (productiveOutcome N s.val e).population.divisions ≤
      productiveRawPotential (extractionCellOuter N rho zL zH) s.val e+
        productiveOuterReserve N M s.val.population.divisions := by
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
        have hd1 := extraction_outer_birth N rho zL zH _ hg.1
        have hd2 := extraction_outer_birth N rho zL zH _ hg.2
        have hp := extraction_outer_nonneg N rho zL zH
          ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩
        simp only [productiveOutcome,growthAt,hm,if_true,potentialSum,List.map_append,List.map_cons,List.sum_append,List.sum_cons,
          productiveOuterReserve,Nat.cast_add,Nat.cast_one]
        linarith only [hd1,hd2,hp]
      · simp [productiveOutcome,growthAt,hm,potentialSum,List.sum_append,add_assoc]
  | inr i =>
    dsimp [productiveRawPotential]
    rw [productive_replacement_frame]
    simp [productiveOutcome,extractionAt,potentialSum,List.sum_append,add_assoc]

theorem productive_outer_raw_barrier (N W0 J : ℕ) (rho zL zH : ℝ)
    (D : Finset ProductiveState) (s : ProductiveActive D) (e : ProductiveEvent s.val)
    (ho : productiveReason N W0 J rho zL zH ⟨s,e⟩=.outer) :
    Real.exp ((N:ℝ)*localAlpha*(8*readyLevel)) ≤
      productiveRawPotential (extractionCellOuter N rho zL zH) s.val e := by
  classical
  cases e with
  | inl e =>
    rcases e with ⟨i,r | d⟩
    · have he : 8*readyLevel ≤ extractionCellEnergy rho zL zH
          ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inl r)⟩ := by
        simp only [productiveReason] at ho
        split_ifs at ho with he
        exact he
      have hp := extraction_outer_barrier N rho zL zH _ he
      simp only [productiveRawPotential,rawEventPotential]
      rw [raw_selected_frame]
      have hl := sum_map_nonneg _ (extraction_outer_nonneg N rho zL zH) (s.val.population.live.take i.val)
      have hr := sum_map_nonneg _ (extraction_outer_nonneg N rho zL zH) (s.val.population.live.drop (i.val+1))
      linarith only [hp,hl,hr]
    · have he : 8*readyLevel ≤ extractionCellEnergy rho zL zH
          ⟨(selectedCell s.val.population i).high,nextCompartment (selectedCell s.val.population i).compartment (.inr ())⟩ := by
        simp only [productiveReason] at ho
        split_ifs at ho
        simp_all
      have hp := extraction_outer_barrier N rho zL zH _ he
      simp only [productiveRawPotential,rawEventPotential]
      rw [raw_selected_frame]
      have hl := sum_map_nonneg _ (extraction_outer_nonneg N rho zL zH) (s.val.population.live.take i.val)
      have hr := sum_map_nonneg _ (extraction_outer_nonneg N rho zL zH) (s.val.population.live.drop (i.val+1))
      linarith only [hp,hl,hr]
  | inr i =>
    have he : 8*readyLevel ≤ extractionCellEnergy rho zL zH
        ⟨(selectedCell s.val.population i).high,
          (channelNext (selectedCell s.val.population i).compartment.1 (.inr ()),(selectedCell s.val.population i).compartment.2)⟩ := by
      simp only [productiveReason] at ho
      split_ifs at ho
      simp_all
    have hp := extraction_outer_barrier N rho zL zH _ he
    dsimp [productiveRawPotential]
    rw [productive_replacement_frame]
    have hl := sum_map_nonneg _ (extraction_outer_nonneg N rho zL zH) (s.val.population.live.take i.val)
    have hr := sum_map_nonneg _ (extraction_outer_nonneg N rho zL zH) (s.val.population.live.drop (i.val+1))
    linarith only [hp,hl,hr]

theorem productive_outer_next_le_raw (N M W0 J : ℕ) (rho zL zH : ℝ)
    (D : Finset ProductiveState) (s : ProductiveActive D) (hD : s.val.population.divisions ≤ 7*M)
    (e : ProductiveEvent s.val) :
    productiveOuterObservable N M W0 J rho zL zH D
      (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩) ≤
      productiveRawPotential (extractionCellOuter N rho zL zH) s.val e+
        productiveOuterReserve N M s.val.population.divisions := by
  classical
  have hr := productive_outer_reserve_nonneg N M s.val.population.divisions hD
  have hn := add_nonneg (productive_raw_nonneg _ (extraction_outer_nonneg N rho zL zH) s.val e) hr
  simp only [productiveStoppedNext,if_true]
  by_cases ha : productiveReason N W0 J rho zL zH ⟨s,e⟩=.active
  · simp only [ha,if_true]
    split_ifs
    · exact productive_active_outer_outcome N M W0 J rho zL zH D s e ha
    · simpa [productiveOuterObservable,ha] using hn
  · simp only [ha,if_false,productiveOuterObservable]
    split_ifs with ho
    · exact (productive_outer_raw_barrier N W0 J rho zL zH D s e ho).trans (le_add_of_nonneg_right hr)
    · exact hn

end
end ProductiveMemory
