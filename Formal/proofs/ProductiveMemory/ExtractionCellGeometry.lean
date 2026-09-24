import proofs.ProductiveMemory.ExtractionSelected

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
noncomputable section
set_option Elab.async false

theorem extraction_energy_lower (b : Bool) (y : Point) :
    (1/200:ℝ)*normSq y ≤ extractionEnergy b y := by
  cases b
  · exact lowExtractionEnergy_lower y
  · exact highExtractionEnergy_lower y

theorem extraction_center_upper (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (b : Bool) (i : Fin 4) : extractionCenter rho zL zH b i ≤ 34 := by
  cases b
  · exact low_extraction_root_upper rho zL hr hzL i
  · exact high_extraction_root_upper rho zH hr hzH i

theorem extraction_cell_in_box (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (N : ℕ) (hN : 1 ≤ N) (c : TaggedCell)
    (hm : N ≤ c.compartment.2) (hmax : c.compartment.2 ≤ 2*N)
    (he : extractionCellEnergy rho zL zH c < outerLevel) : c ∈ cellBox N := by
  have hbox := small_energy_in_countBox c.compartment.2 (hN.trans hm) c.compartment.1
    (extractionCenter rho zL zH c.high) (extraction_center_upper rho zL zH hr hzL hzH c.high)
    (extractionEnergy c.high) (extraction_energy_lower c.high) he
  have hn := (mem_countBox _ _).mp hbox
  apply (mem_cellBox N c).mpr
  refine ⟨hmax,?_⟩
  intro i
  have hi := hn i
  omega

theorem extraction_ancestral_rates (N : ℕ) (hN : 0 < N) (rho zL zH : ℝ)
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : PopulationState) (hv : ValidVolumes N s)
    (he : ∀ c ∈ s.live, extractionCellEnergy rho zL zH c < outerLevel) :
    ((288/100:ℝ)*(ancestralMembrane true s.live:ℝ) ≤ ancestralZ true s.live ∧
      ancestralZ true s.live ≤ 3*(ancestralMembrane true s.live:ℝ)) ∧
    ((97/100:ℝ)*(ancestralMembrane false s.live:ℝ) ≤ ancestralZ false s.live ∧
      ancestralZ false s.live ≤ (ancestralMembrane false s.live:ℝ)) := by
  constructor
  · apply ancestral_rate_envelope
    intro c hc ht
    have hm : 0 < (c.compartment.2:ℝ) := by exact_mod_cast hN.trans_le (hv c hc).1
    have henergy : concentration c.compartment.2 c.compartment.1 ∈
        energyRegion highExtractionEnergy (lift rho zH) outerLevel := by
      simpa [extractionCellEnergy,extractionEnergy,extractionCenter,ht,energyRegion] using (he c hc).le
    have hg := high_outer_readout rho zH hzH _ henergy
    exact ⟨(le_div_iff₀ hm).mp hg.1,(div_le_iff₀ hm).mp hg.2⟩
  · have h := ancestral_rate_envelope false s.live (97/100) 1 ?_
    · simpa only [one_mul] using h
    intro c hc ht
    have hm : 0 < (c.compartment.2:ℝ) := by exact_mod_cast hN.trans_le (hv c hc).1
    have henergy : concentration c.compartment.2 c.compartment.1 ∈
        energyRegion lowExtractionEnergy (lift rho zL) outerLevel := by
      simpa [extractionCellEnergy,extractionEnergy,extractionCenter,ht,energyRegion] using (he c hc).le
    have hg := low_outer_readout rho zL hzL _ henergy
    exact ⟨(le_div_iff₀ hm).mp hg.1,(div_le_iff₀ hm).mp hg.2⟩

end
end ProductiveMemory
