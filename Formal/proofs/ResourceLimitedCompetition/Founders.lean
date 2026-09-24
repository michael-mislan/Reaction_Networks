import proofs.ResourceLimitedCompetition.AncestralRates
import proofs.FiniteCopy.InitialLattice

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

def founderPopulation (N h l : ℕ) (nH nL : Counts) : PopulationState :=
  ⟨4*(N*(h+l)),List.replicate h ⟨true,(nH,N)⟩++List.replicate l ⟨false,(nL,N)⟩,0⟩

def SourceBirths (N : ℕ) (zL zH : ℝ) (nH nL : Counts) : Prop :=
  cellEnergy zL zH ⟨true,(nH,N)⟩ ≤ 4*innerEnergy ∧
    cellEnergy zL zH ⟨false,(nL,N)⟩ ≤ 4*innerEnergy

theorem founder_volumes (N h l : ℕ) (nH nL : Counts) :
    ∀ c ∈ (founderPopulation N h l nH nL).live, c.compartment.2=N := by
  intro c hc
  simp only [founderPopulation,List.mem_append,List.mem_replicate] at hc
  rcases hc with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl

theorem founder_birth_energy (N h l : ℕ) (zL zH : ℝ) (nH nL : Counts)
    (hb : SourceBirths N zL zH nH nL) :
    ∀ c ∈ (founderPopulation N h l nH nL).live, cellEnergy zL zH c ≤ 4*innerEnergy := by
  intro c hc
  simp only [founderPopulation,List.mem_append,List.mem_replicate] at hc
  rcases hc with ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact hb.1
  · exact hb.2

theorem founder_ancestral_membrane (N h l : ℕ) (nH nL : Counts) :
    ancestralMembrane true (founderPopulation N h l nH nL).live=N*h ∧
      ancestralMembrane false (founderPopulation N h l nH nL).live=N*l := by
  simp [founderPopulation,ancestralMembrane,List.map_replicate,List.sum_replicate,mul_comm]

theorem founder_membrane (N h l : ℕ) (nH nL : Counts) :
    membrane (founderPopulation N h l nH nL).live=N*(h+l) := by
  have hb := founder_ancestral_membrane N h l nH nL
  rw [← ancestral_membrane_total,hb.1,hb.2]
  ring

theorem founder_mem_activeDomain (N h l : ℕ) (hN : 1 ≤ N) (hh : 0 < h) (hl : 0 < l)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (nH nL : Counts) (hb : SourceBirths N zL zH nH nL) :
    founderPopulation N h l nH nL ∈ activeDomain N (h+l) zL zH := by
  apply active_mem_domain N (h+l) hN zL zH hzL hzH
  have hNM : 0 < N*(h+l) := Nat.mul_pos (by omega) (by omega)
  refine ⟨?_,le_rfl,?_,?_,?_,?_⟩
  · change N*(h+l) < 4*(N*(h+l))
    omega
  · rw [founder_membrane]
    change 4*(N*(h+l))+N*(h+l)=5*(N*(h+l))
    ring
  · simp [founderPopulation]
  · intro c hc
    rw [founder_volumes N h l nH nL c hc]
    exact ⟨le_rfl,by omega⟩
  · intro c hc
    have he := founder_birth_energy N h l zL zH nH nL hb c hc
    have hg : 4*innerEnergy < outerEnergy := by norm_num [innerEnergy,outerEnergy]
    exact he.trans_lt hg

theorem source_births_nonempty (N : ℕ) (hN : 1000000000000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)) :
    ∃ nH nL, SourceBirths N zL zH nH nL := by
  obtain ⟨nH,_,hH⟩ := high_initial_lattice_nonempty zH hzH N hN
  obtain ⟨nL,_,hL⟩ := low_initial_lattice_nonempty zL hzL N hN
  refine ⟨nH,nL,?_,?_⟩
  · change highEnergy (fun i => concentration N nH i-pointOfState (lift sourceRates zH) i) ≤ 4*innerEnergy
    norm_num [innerEnergy,outerEnergy]
    linarith only [hH]
  · change lowEnergy (fun i => concentration N nL i-pointOfState (lift sourceRates zL) i) ≤ 4*innerEnergy
    norm_num [innerEnergy,outerEnergy]
    linarith only [hL]

end ResourceLimitedCompetition
