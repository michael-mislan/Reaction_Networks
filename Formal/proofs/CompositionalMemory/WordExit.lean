import proofs.CompositionalMemory.WordEnvelope
import proofs.CompositionalMemory.ProductExit

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

theorem word_exit_bound {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (b : ℝ) (hb : b ≤ 1/32000000) (a : ℝ) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (retainedModularModel γ w hγ hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).total s ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b})
    (hstart : ∀ i, wordEnergy σ i (fun j => modularConcentration s.val i j-wordCenter z₀ z₁ σ i j) ≤ a) :
    Real.exp (localAlpha*(N : ℝ)*b)*
      ((retainedModularModel γ w hγ hw N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some s) ≤
      (k : ℝ)*(Real.exp (localAlpha*(N : ℝ)*a)+(t : ℝ)*growingCeiling N (1/100000000000)) := by
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  exact product_exit_bound hk N hN γ w hγ hw _ hc.1 _ (word_energy_lower σ) b hb
    localAlpha a (growingCeiling N (1/100000000000)) (by norm_num [localAlpha])
    (growingCeiling_nonneg N _ (Nat.cast_nonneg N))
    (fun x hx _ i => word_generator_envelope hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁
      w hdiag hsym hw hrow hγ hγmax hκ hκmax b hb x hx i)
    q t hq hclock s hstart

end CompositionalMemory
