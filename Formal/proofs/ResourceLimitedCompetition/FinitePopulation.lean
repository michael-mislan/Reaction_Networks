import proofs.ResourceLimitedCompetition.PopulationGenerator
import proofs.ResourceLimitedCompetition.SafeGeometry

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC

noncomputable def boundedLists {α : Type*} [DecidableEq α] (C : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | k+1 => insert [] (C.biUnion (fun c => (boundedLists C k).image (List.cons c)))

theorem mem_boundedLists {α : Type*} [DecidableEq α] (C : Finset α) (k : ℕ) (xs : List α) :
    xs ∈ boundedLists C k ↔ xs.length ≤ k ∧ ∀ x ∈ xs, x ∈ C := by
  induction k generalizing xs with
  | zero => cases xs <;> simp [boundedLists]
  | succ k ih =>
    cases xs with
    | nil => simp [boundedLists]
    | cons c cs => simp [boundedLists, ih, and_assoc, and_left_comm]

noncomputable def cellBox (N : ℕ) : Finset TaggedCell := by
  classical
  exact ((Finset.univ : Finset Bool).product
    ((Finset.range (2*N+1)).product (countBox (2*N)))).image
    (fun p => ⟨p.1,(p.2.2,p.2.1)⟩)

theorem mem_cellBox (N : ℕ) (c : TaggedCell) :
    c ∈ cellBox N ↔ c.compartment.2 ≤ 2*N ∧ ∀ i, c.compartment.1 i ≤ 70*N := by
  classical
  constructor
  · intro h
    obtain ⟨⟨tag,m,n⟩,hp,rfl⟩ := Finset.mem_image.mp h
    have hm := (Finset.mem_product.mp (Finset.mem_product.mp hp).2).1
    have hn := (mem_countBox (2*N) n).mp (Finset.mem_product.mp (Finset.mem_product.mp hp).2).2
    simp only [Finset.mem_range] at hm
    constructor
    · exact Nat.le_of_lt_succ hm
    · intro i
      have h := hn i
      dsimp
      omega
  · rintro ⟨hm,hn⟩
    apply Finset.mem_image.mpr
    refine ⟨(c.high,c.compartment.2,c.compartment.1),?_,?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,?_⟩⟩
      · change c.compartment.2 < 2*N+1
        omega
      apply (mem_countBox (2*N) _).mpr
      intro i
      change c.compartment.1 i ≤ 35*(2*N)
      have h := hn i
      omega
    · cases c
      rfl

noncomputable def populationBox (N M : ℕ) : Finset PopulationState := by
  classical
  exact ((Finset.range (4*(N*M)+1)).product
    ((boundedLists (cellBox N) (4*M)).product (Finset.range (3*M+1)))).image
    (fun p => ⟨p.1,p.2.1,p.2.2⟩)

theorem mem_populationBox (N M : ℕ) (s : PopulationState) :
    s ∈ populationBox N M ↔ s.resource ≤ 4*(N*M) ∧
      (s.live.length ≤ 4*M ∧ ∀ c ∈ s.live, c ∈ cellBox N) ∧ s.divisions ≤ 3*M := by
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
          Finset.mem_range.mpr (by change s.divisions < 3*M+1; omega)⟩⟩
    · cases s
      rfl

noncomputable def cellEnergy (zL zH : ℝ) (c : TaggedCell) : ℝ :=
  if c.high then highEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
    pointOfState (lift sourceRates zH) i)
  else lowEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
    pointOfState (lift sourceRates zL) i)

def ActivePopulation (N M : ℕ) (zL zH : ℝ) (s : PopulationState) : Prop :=
  N*M < s.resource ∧ s.resource ≤ 4*(N*M) ∧
  s.resource+membrane s.live=5*(N*M) ∧
  s.live.length=M+s.divisions ∧ ValidVolumes N s ∧
  ∀ c ∈ s.live, cellEnergy zL zH c < outerEnergy

noncomputable def activeDomain (N M : ℕ) (zL zH : ℝ) : Finset PopulationState := by
  classical
  exact (populationBox N M).filter (ActivePopulation N M zL zH)

theorem activeDomain_safe (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (h : s ∈ activeDomain N M zL zH) : ActivePopulation N M zL zH s := by
  classical
  exact (Finset.mem_filter.mp h).2

theorem safe_cell_in_box (N : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Set.Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Set.Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (c : TaggedCell) (hm : N ≤ c.compartment.2) (hmmax : c.compartment.2 ≤ 2*N)
    (he : cellEnergy zL zH c < outerEnergy) : c ∈ cellBox N := by
  have hn : ∀ i, c.compartment.1 i ≤ 35*c.compartment.2 := by
    cases hb : c.high with
    | false =>
      have he' : lowEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
          pointOfState (lift sourceRates zL) i) < 1/32000000 := by
        simpa [cellEnergy,hb,outerEnergy] using he
      exact (mem_countBox _ _).mp (small_energy_in_countBox _ (hN.trans hm) _ _
        (lowroot_upper zL hzL) lowEnergy lowEnergy_lower he')
    | true =>
      have he' : highEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
          pointOfState (lift sourceRates zH) i) < 1/32000000 := by
        simpa [cellEnergy,hb,outerEnergy] using he
      exact (mem_countBox _ _).mp (small_energy_in_countBox _ (hN.trans hm) _ _
        (highroot_upper zH hzH) highEnergy highEnergy_lower he')
  apply (mem_cellBox N c).mpr
  refine ⟨hmmax,?_⟩
  intro i
  have h := hn i
  omega

theorem active_mem_domain (N M : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Set.Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Set.Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : PopulationState) (h : ActivePopulation N M zL zH s) : s ∈ activeDomain N M zL zH := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_,h⟩
  obtain ⟨hlo,hhi,hres,hlen,hvol,he⟩ := h
  have hb := resource_population_budget N M (by omega) s hvol hres hlo.le hlen
  apply (mem_populationBox N M s).mpr
  refine ⟨hhi,⟨hb.1,?_⟩,hb.2.1⟩
  intro c hc
  exact safe_cell_in_box N hN zL zH hzL hzH c (hvol c hc).1
    (hvol c hc).2.le (he c hc)

end ResourceLimitedCompetition
