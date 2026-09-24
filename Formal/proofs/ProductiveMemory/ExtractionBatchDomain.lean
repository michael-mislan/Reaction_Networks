import proofs.ProductiveMemory.ExtractionStoppedPopulation
import proofs.ProductiveMemory.ExtractionCellGeometry
import proofs.SerialTransferSelection.BatchDomain

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
noncomputable section
set_option Elab.async false

def ProductiveActiveCondition (N M W0 J : ℕ) (rho zL zH : ℝ) (s : ProductiveState) : Prop :=
  W0 < s.population.resource ∧ s.population.resource ≤ 4*W0 ∧
    s.population.resource+membrane s.population.live=5*W0 ∧
    s.population.live.length=M+s.population.divisions ∧
    ValidVolumes N s.population ∧
    (∀ c ∈ s.population.live, extractionCellEnergy rho zL zH c < 8*readyLevel) ∧
    s.collected < J

def productiveBox (N M W0 J : ℕ) : Finset ProductiveState := by
  classical
  exact ((SerialTransferSelection.phasePopulationBox N M W0).product (Finset.range J)).image
    (fun p => ⟨p.1,p.2⟩)

theorem mem_productiveBox (N M W0 J : ℕ) (s : ProductiveState) :
    s ∈ productiveBox N M W0 J ↔
      s.population ∈ SerialTransferSelection.phasePopulationBox N M W0 ∧ s.collected < J := by
  classical
  constructor
  · intro h
    obtain ⟨⟨p,E⟩,hp,rfl⟩ := Finset.mem_image.mp h
    exact ⟨(Finset.mem_product.mp hp).1,Finset.mem_range.mp (Finset.mem_product.mp hp).2⟩
  · rintro ⟨hp,hE⟩
    apply Finset.mem_image.mpr
    exact ⟨(s.population,s.collected),Finset.mem_product.mpr ⟨hp,Finset.mem_range.mpr hE⟩,by cases s; rfl⟩

def productiveActiveDomain (N M W0 J : ℕ) (rho zL zH : ℝ) : Finset ProductiveState := by
  classical
  exact (productiveBox N M W0 J).filter (ProductiveActiveCondition N M W0 J rho zL zH)

theorem productive_active_safe (N M W0 J : ℕ) (rho zL zH : ℝ) (s : ProductiveState)
    (h : s ∈ productiveActiveDomain N M W0 J rho zL zH) :
    ProductiveActiveCondition N M W0 J rho zL zH s := by
  classical
  exact (Finset.mem_filter.mp h).2

theorem productive_active_mem (N M W0 J : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M)
    (rho zL zH : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveState) (h : ProductiveActiveCondition N M W0 J rho zL zH s) :
    s ∈ productiveActiveDomain N M W0 J rho zL zH := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_,h⟩
  obtain ⟨hlo,hhi,hres,hlen,hvol,he,hE⟩ := h
  apply (mem_productiveBox N M W0 J s).mpr
  refine ⟨?_,hE⟩
  have hb := SerialTransferSelection.phase_batch_population_budget N M W0 (by omega) hW s.population hvol hres hlo.le hlen
  apply (SerialTransferSelection.mem_phasePopulationBox N M W0 s.population).mpr
  refine ⟨hhi,⟨hb.1,?_⟩,hb.2⟩
  intro c hc
  apply extraction_cell_in_box rho zL zH hr hzL hzH N hN c (hvol c hc).1 (hvol c hc).2.le
  exact (he c hc).trans (by norm_num [readyLevel,outerLevel])

theorem productive_active_cell_count (N M W0 J : ℕ) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    s.val.population.live.length ≤ 8*M := by
  classical
  have hb := (mem_productiveBox N M W0 J s.val).mp (Finset.mem_filter.mp s.property).1
  exact ((SerialTransferSelection.mem_phasePopulationBox N M W0 s.val.population).mp hb.1).2.1.1

theorem productive_active_energy (N M W0 J : ℕ) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH))
    (c : TaggedCell) (hc : c ∈ s.val.population.live) : extractionCellEnergy rho zL zH c < outerLevel := by
  have h := productive_active_safe N M W0 J rho zL zH s.val s.property
  exact (h.2.2.2.2.2.1 c hc).trans (by norm_num [readyLevel,outerLevel])

end
end ProductiveMemory
