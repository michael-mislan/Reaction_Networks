import proofs.CompositionalMemory.WordGeometry
import proofs.CompositionalMemory.UniformEnvelope

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

theorem word_generator_bound {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (b : ℝ) (hb : b ≤ 1/32000000) (s : ModularCountState k)
    (hs : s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b) (i : Fin k) :
    modularGenerator γ w (fun t => Real.exp (localAlpha*(N : ℝ)*
      wordEnergy σ i (fun a => modularConcentration t i a-wordCenter z₀ z₁ σ i a))) s ≤
    localAlpha*Real.exp (localAlpha*(N : ℝ)*
      wordEnergy σ i (fun a => modularConcentration s i a-wordCenter z₀ z₁ σ i a))*
      (-(N : ℝ)*normSq (fun a => modularConcentration s i a-wordCenter z₀ z₁ σ i a)/4+
        200000000+1200000000*(N : ℝ)*(γ+κ)^2) := by
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  have hmem := (mem_productDomain hk N hN _ hc.1 _ (word_energy_lower σ) b hb s).mp hs
  have hbounds := product_domain_point_bounds hk N hN _ hc.1 hc.2 _ (word_energy_lower σ) b hb s hs i
  have hmpos : 0 < s.2 := lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hmem.1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmr : (k : ℝ)*(N : ℝ) ≤ (s.2 : ℝ) := by exact_mod_cast hmem.1
  cases hσ : σ i
  · have h := low_count_generator_bound hk z₀ γ κ N s.2 hmpos w hdiag hsym i s.1
      h₀ hst₀ hNr hmr hγ hγmax hκ hκmax hbounds.2.2.2 (hw i) (hrow i)
      (by simpa only [wordCenter,hσ,Bool.false_eq_true,ite_false] using hbounds.1)
      (by simpa only [wordCenter,hσ,Bool.false_eq_true,ite_false] using hbounds.2.1)
      hbounds.2.2.1
    simpa only [wordEnergy,wordCenter,hσ,Bool.false_eq_true,ite_false,localAlpha] using h
  · have h := high_count_generator_bound hk z₁ γ κ N s.2 hmpos w hdiag hsym i s.1
      h₁ hst₁ hNr hmr hγ hγmax hκ hκmax hbounds.2.2.2 (hw i) (hrow i)
      (by simpa only [wordCenter,hσ,ite_true] using hbounds.1)
      (by simpa only [wordCenter,hσ,ite_true] using hbounds.2.1)
      hbounds.2.2.1
    simpa only [wordEnergy,wordCenter,hσ,ite_true,localAlpha] using h

end CompositionalMemory
