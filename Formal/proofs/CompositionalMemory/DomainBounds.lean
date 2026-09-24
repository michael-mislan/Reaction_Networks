import proofs.CompositionalMemory.ProductDomain

namespace CompositionalMemory
open FiniteCopy

/-- Domain membership supplies all local geometric bounds needed by J2. -/
theorem product_domain_point_bounds {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ j a, center j a ≤ 34)
    (hcz : ∀ j, center j 2 ≤ 3) (E : Fin k → Point → ℝ)
    (hE : ∀ j y, (1/200)*normSq y ≤ E j y) (b : ℝ) (hb : b ≤ 1/32000000)
    (s : ModularCountState k) (hs : s ∈ productDomain N center E b) (i : Fin k) :
    (∀ a, |modularConcentration s i a-center i a| ≤ 1/400) ∧
    normSq (fun a => modularConcentration s i a-center i a) ≤ 1/160000 ∧
    (∀ a, |modularConcentration s i a| ≤ 35) ∧
    (∀ j, 0 ≤ modularConcentration s j 2 ∧ modularConcentration s j 2 ≤ 4) := by
  have hmem := (mem_productDomain hk N hN center hc E hE b hb s).mp hs
  have he (j) := (hmem.2.2 j).trans_le hb
  have hcoord (j a) := small_energy_coordinates (E j) (hE j) _ (he j) a
  have hnonneg (j a) : 0 ≤ modularConcentration s j a := by
    unfold modularConcentration effectiveConcentration
    positivity
  refine ⟨hcoord i,?_,?_,?_⟩
  · have h := hE i (fun a => modularConcentration s i a-center i a)
    have hh := he i
    nlinarith only [h,hh]
  · intro a
    rw [abs_of_nonneg (hnonneg i a)]
    have h := (abs_le.mp (hcoord i a)).2
    linarith [hc i a]
  · intro j
    refine ⟨hnonneg j 2,?_⟩
    have h := (abs_le.mp (hcoord j 2)).2
    linarith [hcz j]

end CompositionalMemory
