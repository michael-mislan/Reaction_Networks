import proofs.CompositionalMemory.SourceCountGenerator
import proofs.CompositionalMemory.DomainBounds

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

noncomputable def wordCenter {k : ℕ} (z₀ z₁ : ℝ) (σ : Fin k → Bool) (i : Fin k) : Point :=
  pointOfState (lift sourceRates (if σ i then z₁ else z₀))

noncomputable def wordEnergy {k : ℕ} (σ : Fin k → Bool) (i : Fin k) : Point → ℝ :=
  if σ i then highEnergy else lowEnergy

theorem word_energy_lower {k : ℕ} (σ : Fin k → Bool) (i : Fin k) (y : Point) :
    (1/200)*normSq y ≤ wordEnergy σ i y := by
  unfold wordEnergy
  split
  · exact highEnergy_lower y
  · exact lowEnergy_lower y

theorem word_energy_upper {k : ℕ} (σ : Fin k → Bool) (i : Fin k) (y : Point) :
    wordEnergy σ i y ≤ 42*normSq y := by
  unfold wordEnergy
  split
  · simpa using highEnergy_upper y
  · have h := lowEnergy_upper y
    have hn := normSq_nonneg y
    linarith only [h,hn]

theorem word_center_bounds {k : ℕ} (z₀ z₁ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)) :
    (∀ i a, wordCenter z₀ z₁ σ i a ≤ 34) ∧ (∀ i, wordCenter z₀ z₁ σ i 2 ≤ 3) := by
  have hb₀ := low_source_box z₀ h₀
  have hb₁ := high_source_box z₁ h₁
  constructor
  · intro i a
    fin_cases a <;> cases h : σ i <;>
      norm_num [wordCenter,h,pointOfState,lift] <;>
      linarith [hb₀.1.2,hb₀.2.1.2,hb₀.2.2.2,hb₁.1.2,hb₁.2.1.2,hb₁.2.2.2,h₀.2,h₁.2]
  · intro i
    change (if σ i then z₁ else z₀) ≤ 3
    split <;> linarith [h₀.2,h₁.2]

end CompositionalMemory
