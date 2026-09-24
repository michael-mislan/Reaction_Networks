import proofs.SerialTransferSelection.ReadyPopulation
import proofs.SerialTransferSelection.ReadyRegions

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- A physical concentration readout; it does not inspect the ancestry tag. -/
noncomputable def chemicalReadout (c : TaggedCell) : Bool := by
  classical
  exact decide (2 < concentration c.compartment.2 c.compartment.1 2)

theorem chemical_readout_matches_ancestry (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (c : TaggedCell) (he : cellEnergy zL zH c ≤ outerEnergy) :
    chemicalReadout c=c.high := by
  cases ht : c.high
  · have he' : lowEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
        pointOfState (lift sourceRates zL) i) ≤ 1/32000000 := by
      simpa [cellEnergy,ht,outerEnergy] using he
    have hg := (low_safe_geometry zL hzL _ he').1.2
    have hn : ¬2 < concentration c.compartment.2 c.compartment.1 2 := by linarith
    simp [chemicalReadout,hn]
  · have he' : highEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
        pointOfState (lift sourceRates zH) i) ≤ 1/32000000 := by
      simpa [cellEnergy,ht,outerEnergy] using he
    have hg := (high_safe_geometry zH hzH _ he').1.1
    have hp : 2 < concentration c.compartment.2 c.compartment.1 2 := by linarith
    simp [chemicalReadout,hp]

theorem ready_population_readout (N M : ℕ) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : ReadyPopulation N M zL zH) (c : TaggedCell) (hc : c ∈ s.val.live) :
    chemicalReadout c=c.high := by
  apply chemical_readout_matches_ancestry zL zH hzL hzH c
  exact ((readyPopulation_ready N M zL zH s).2.2.2.2 c hc).trans
    (by norm_num [innerEnergy,outerEnergy])

end SerialTransferSelection
