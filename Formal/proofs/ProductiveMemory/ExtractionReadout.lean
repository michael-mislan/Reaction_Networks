import proofs.ProductiveMemory.ExtractionConstructive

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

theorem productive_ready_readout (N M : ℕ) (rho zL zH : ℝ)
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveReady N M rho zL zH) (c : TaggedCell) (hc : c ∈ s.val.population.live) :
    (if c.high then (288/100:ℝ) ≤ concentration c.compartment.2 c.compartment.1 2 ∧
        concentration c.compartment.2 c.compartment.1 2 ≤ 3
      else (97/100:ℝ) ≤ concentration c.compartment.2 c.compartment.1 2 ∧
        concentration c.compartment.2 c.compartment.1 2 ≤ 1) := by
  have he := (productiveReady_ready N M rho zL zH s).2.2.2.2.1 c hc
  have hb : readyLevel ≤ outerLevel := by norm_num [readyLevel,outerLevel]
  cases h : c.high
  · simp only [Bool.false_eq_true,ite_false]
    apply low_outer_readout rho zL hzL
    change lowExtractionEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-lift rho zL i) ≤ outerLevel
    simpa only [extractionCellEnergy,extractionEnergy,extractionCenter,h] using he.trans hb
  · simp only [ite_true]
    apply high_outer_readout rho zH hzH
    change highExtractionEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-lift rho zH i) ≤ outerLevel
    simpa only [extractionCellEnergy,extractionEnergy,extractionCenter,h] using he.trans hb

theorem productive_readout_exact (N M : ℕ) (rho zL zH : ℝ)
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveReady N M rho zL zH) (c : TaggedCell) (hc : c ∈ s.val.population.live) :
    c.high=true ↔ 2 ≤ concentration c.compartment.2 c.compartment.1 2 := by
  have h := productive_ready_readout N M rho zL zH hzL hzH s c hc
  cases hb : c.high <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] at h ⊢
  · constructor
    · exact False.elim
    · intro hg
      linarith only [h.2,hg]
  · constructor
    · intro _; linarith only [h.1]
    · intro _; trivial

end
end ProductiveMemory
