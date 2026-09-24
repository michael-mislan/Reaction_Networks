import proofs.ProductiveMemory.ExtractionAttraction

namespace ProductiveMemory
open FiniteCopy Set Filter Topology
noncomputable section
set_option Elab.async false

def ExtractionAttracts (rho : ℝ) (c : Point) (E : Point → ℝ) : Prop :=
  ∀ x₀, E (fun i => x₀ i-c i) ≤ outerLevel →
    ∃ x : ℝ → Point, x 0=x₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt x (extractDrift rho 0 (x t)) t ∧
        E (fun i => x t i-c i) ≤ outerLevel ∧
        E (fun i => x t i-c i) ≤ E (fun i => x₀ i-c i)*Real.exp (-(1/1000:ℝ)*t)) ∧
      Tendsto x atTop (𝓝 c)

theorem low_extraction_attracts (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z)=0) :
    ExtractionAttracts rho (lift rho z) lowExtractionEnergy := by
  intro x₀ h₀
  apply extraction_energy_attraction rho (lift rho z) lowExtractionEnergy lowExtractionPair
    ?_ lowExtractionEnergy_lower lowExtractionEnergy_upper ?_ ?_ x₀ h₀
  · intro i
    rw [abs_of_nonneg ((reconstructed_positive rho z (by linarith [hr.1]) (by linarith [hz.1]) i).le)]
    exact low_extraction_root_upper rho z hr hz i
  · intro x v t hd
    exact low_extraction_energy_derivative x v (lift rho z) t hd
  · exact low_extraction_dissipation rho z hr hz he

theorem high_extraction_attracts (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z)=0) :
    ExtractionAttracts rho (lift rho z) highExtractionEnergy := by
  intro x₀ h₀
  apply extraction_energy_attraction rho (lift rho z) highExtractionEnergy highExtractionPair
    ?_ highExtractionEnergy_lower highExtractionEnergy_upper ?_ ?_ x₀ h₀
  · intro i
    rw [abs_of_nonneg ((reconstructed_positive rho z (by linarith [hr.1]) (by linarith [hz.1]) i).le)]
    exact high_extraction_root_upper rho z hr hz i
  · intro x v t hd
    exact high_extraction_energy_derivative x v (lift rho z) t hd
  · exact high_extraction_dissipation rho z hr hz he

theorem two_extraction_attractors (rho : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) :
    ∃ zL zH, zL ∈ Icc (98172/100000:ℝ) (98174/100000) ∧
      zH ∈ Icc (289014/100000:ℝ) (289017/100000) ∧
      ExtractionAttracts rho (lift rho zL) lowExtractionEnergy ∧
      ExtractionAttracts rho (lift rho zH) highExtractionEnergy ∧
      Disjoint (energyRegion lowExtractionEnergy (lift rho zL) outerLevel)
        (energyRegion highExtractionEnergy (lift rho zH) outerLevel) := by
  obtain ⟨⟨zL,hzL,hsL,_⟩,⟨zH,hzH,hsH,_⟩⟩ := two_positive_stationary_states rho hr
  exact ⟨zL,zH,hzL,hzH,low_extraction_attracts rho zL hr hzL hsL,
    high_extraction_attracts rho zH hr hzH hsH,separated_outer_regions rho zL zH hzL hzH⟩

end
end ProductiveMemory
