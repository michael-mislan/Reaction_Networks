import proofs.SerialTransferSelection.BatchConservation
import proofs.ResourceLimitedCompetition.FinitePopulation

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC

/-- Actual ready populations keep all division phases and use the measured total size. -/
def PhaseReadyPopulation (N M : ℕ) (zL zH : ℝ) (s : PopulationState) : Prop :=
  s.live.length=M ∧ s.divisions=0 ∧ s.resource=4*membrane s.live ∧
    ValidVolumes N s ∧ ∀ c ∈ s.live, cellEnergy zL zH c ≤ innerEnergy

def PhaseActivePopulation (N M W0 : ℕ) (zL zH : ℝ) (s : PopulationState) : Prop :=
  W0 < s.resource ∧ s.resource ≤ 4*W0 ∧
    s.resource+membrane s.live=5*W0 ∧ s.live.length=M+s.divisions ∧
    ValidVolumes N s ∧ ∀ c ∈ s.live, cellEnergy zL zH c < 8*innerEnergy

noncomputable def phasePopulationBox (N M W0 : ℕ) : Finset PopulationState := by
  classical
  exact ((Finset.range (4*W0+1)).product
    ((boundedLists (cellBox N) (8*M)).product (Finset.range (7*M+1)))).image
    (fun p => ⟨p.1,p.2.1,p.2.2⟩)

theorem mem_phasePopulationBox (N M W0 : ℕ) (s : PopulationState) :
    s ∈ phasePopulationBox N M W0 ↔ s.resource ≤ 4*W0 ∧
      (s.live.length ≤ 8*M ∧ ∀ c ∈ s.live, c ∈ cellBox N) ∧ s.divisions ≤ 7*M := by
  classical
  constructor
  · intro h
    obtain ⟨⟨Q,cs,D⟩,hp,rfl⟩ := Finset.mem_image.mp h
    have hQ := (Finset.mem_product.mp hp).1
    have hcs := (Finset.mem_product.mp (Finset.mem_product.mp hp).2).1
    have hD := (Finset.mem_product.mp (Finset.mem_product.mp hp).2).2
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hQ),
      (mem_boundedLists _ _ _).mp hcs,Nat.le_of_lt_succ (Finset.mem_range.mp hD)⟩
  · rintro ⟨hQ,hcs,hD⟩
    apply Finset.mem_image.mpr
    refine ⟨(s.resource,s.live,s.divisions),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_product.mpr ⟨(mem_boundedLists _ _ _).mpr hcs,
          Finset.mem_range.mpr (by change s.divisions < 7*M+1; omega)⟩⟩
    · cases s
      rfl

noncomputable def phaseActiveDomain (N M W0 : ℕ) (zL zH : ℝ) : Finset PopulationState := by
  classical
  exact (phasePopulationBox N M W0).filter (PhaseActivePopulation N M W0 zL zH)

theorem phaseActiveDomain_safe (N M W0 : ℕ) (zL zH : ℝ) (s : PopulationState)
    (h : s ∈ phaseActiveDomain N M W0 zL zH) : PhaseActivePopulation N M W0 zL zH s := by
  classical
  exact (Finset.mem_filter.mp h).2

theorem phase_active_mem_domain (N M W0 : ℕ) (hN : 1 ≤ N) (hW : W0 ≤ 2*N*M)
    (zL zH : ℝ)
    (hzL : zL ∈ Set.Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Set.Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : PopulationState) (h : PhaseActivePopulation N M W0 zL zH s) :
    s ∈ phaseActiveDomain N M W0 zL zH := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_,h⟩
  obtain ⟨hlo,hhi,hres,hlen,hvol,he⟩ := h
  have hb := phase_batch_population_budget N M W0 (by omega) hW s hvol hres hlo.le hlen
  apply (mem_phasePopulationBox N M W0 s).mpr
  refine ⟨hhi,⟨hb.1,?_⟩,hb.2⟩
  intro c hc
  apply safe_cell_in_box N hN zL zH hzL hzH c (hvol c hc).1 (hvol c hc).2.le
  exact (he c hc).trans (by norm_num [innerEnergy,outerEnergy])

theorem phase_ready_mem_domain (N M : ℕ) (hN : 1 ≤ N) (hM : 0 < M)
    (zL zH : ℝ)
    (hzL : zL ∈ Set.Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Set.Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : PopulationState) (h : PhaseReadyPopulation N M zL zH s) :
    s ∈ phaseActiveDomain N M (membrane s.live) zL zH := by
  obtain ⟨hlen,hD,hQ,hv,he⟩ := h
  have hW := membrane_upper N s.live (fun c hc => (hv c hc).2.le)
  have hlo := membrane_lower N s.live (fun c hc => (hv c hc).1)
  rw [hlen] at hW hlo
  have hpos : 0 < membrane s.live := (Nat.mul_pos (by omega) hM).trans_le hlo
  apply phase_active_mem_domain N M (membrane s.live) hN hW zL zH hzL hzH s
  refine ⟨?_,?_,?_,?_,hv,?_⟩
  · rw [hQ]; omega
  · rw [hQ]
  · rw [hQ]; omega
  · omega
  · intro c hc
    exact (he c hc).trans_lt (by norm_num [innerEnergy,outerEnergy])

end SerialTransferSelection
