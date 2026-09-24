import proofs.HeritableCompositions.StoppedGrowth
import proofs.FiniteCopy.WellDomains

namespace HeritableCompositions
open FiniteCopy

noncomputable def growthDomain (N : ℕ) (s : Point) (E : Point → ℝ) (b : ℝ) :
    Finset Compartment := by
  classical
  exact ((countBox (2*N)).product (Finset.Icc N (2*N))).filter
    (fun c => E (fun i => concentration c.2 c.1 i-s i) < b)

theorem mem_growthDomain (N : ℕ) (hN : 1 ≤ N) (c : Compartment)
    (s : Point) (hs : ∀ i, s i ≤ 34) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y) (b : ℝ) (hb : b ≤ 1/32000000) :
    c ∈ growthDomain N s E b ↔ N ≤ c.2 ∧ c.2 ≤ 2*N ∧
      E (fun i => concentration c.2 c.1 i-s i) < b := by
  classical
  change (c.1,c.2) ∈ growthDomain N s E b ↔ _
  simp only [growthDomain,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hlo,hhi⟩,he⟩
    exact ⟨hlo,hhi,he⟩
  · rintro ⟨hlo,hhi,he⟩
    have hm : 1 ≤ c.2 := hN.trans hlo
    have hc := (mem_countBox c.2 c.1).mp
      (small_energy_in_countBox c.2 hm c.1 s hs E hE (he.trans_le hb))
    have hc' : c.1 ∈ countBox (2*N) := by
      apply (mem_countBox (2*N) c.1).mpr
      intro i
      exact (hc i).trans (Nat.mul_le_mul_left 35 hhi)
    exact ⟨⟨hc',hlo,hhi⟩,he⟩

theorem next_membrane_range (N : ℕ) (c : Compartment)
    (hlo : N ≤ c.2) (hhi : c.2 < 2*N) (r : Channel) :
    N ≤ (nextCompartment c r).2 ∧ (nextCompartment c r).2 ≤ 2*N := by
  cases r with
  | inl r => simpa only [nextCompartment] using And.intro hlo hhi.le
  | inr r => simp only [nextCompartment]; omega

theorem growth_domain_departure_energy (N : ℕ) (hN : 1 ≤ N)
    (s : Point) (hs : ∀ i, s i ≤ 34) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y) (b : ℝ) (hb : b ≤ 1/32000000)
    (c : Compartment) (hc : c ∈ growthDomain N s E b) (hm : c.2 < 2*N)
    (r : Channel) (hout : nextCompartment c r ∉ growthDomain N s E b) :
    b ≤ E (fun i => concentration (nextCompartment c r).2 (nextCompartment c r).1 i-s i) := by
  have hmem := mem_growthDomain N hN c s hs E hE b hb
  have hr := next_membrane_range N c (hmem.mp hc).1 hm r
  apply le_of_not_gt
  intro he
  exact hout ((mem_growthDomain N hN (nextCompartment c r) s hs E hE b hb).mpr
    ⟨hr.1,hr.2,he⟩)

end HeritableCompositions
