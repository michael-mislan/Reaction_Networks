import proofs.CompositionalMemory.WordGenerator

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

theorem word_generator_envelope {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
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
      wordEnergy σ i (fun a => modularConcentration t i a-wordCenter z₀ z₁ σ i a))) s ≤ growingCeiling N (1/100000000000) := by
  have h := word_generator_bound hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁
    w hdiag hsym hw hrow hγ hγmax hκ hκmax b hb s hs i
  exact uniform_envelope N γ κ _ _ _ (Nat.cast_nonneg N) (normSq_nonneg _) (word_energy_upper σ i _)
    hγ hγmax hκ hκmax
    (by simpa only [localAlpha,mul_comm (N : ℝ) (1/1000000000000 : ℝ)] using h)

theorem word_generator_affine {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (hNlarge : 140000000000000000000 ≤ N)
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
      -((N : ℝ)*localAlpha*innerEnergy/672)*Real.exp ((N : ℝ)*localAlpha*
        wordEnergy σ i (fun a => modularConcentration s i a-wordCenter z₀ z₁ σ i a))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  have h := word_generator_bound hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁
    w hdiag hsym hw hrow hγ hγmax hκ hκmax b hb s hs i
  exact uniform_affine_recovery N γ κ _ _ _ (by exact_mod_cast hNlarge) (normSq_nonneg _) (word_energy_upper σ i _)
    hγ hγmax hκ hκmax
    (by simpa only [localAlpha,mul_comm (N : ℝ) (1/1000000000000 : ℝ)] using h)

end CompositionalMemory
