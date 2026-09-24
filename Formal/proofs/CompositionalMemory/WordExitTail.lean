import proofs.CompositionalMemory.WordExit
import proofs.HeritableCompositions.ExitTail

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

theorem scaled_exit_tail (k : ℕ) (hk : 1 ≤ k) (N b a t p : ℝ)
    (hN : 0 ≤ N) (ht : 0 ≤ t) (hb : 2*innerEnergy ≤ b) (ha : a ≤ b-innerEnergy/2)
    (h : Real.exp (N*localAlpha*b)*p ≤ (k : ℝ)*(Real.exp (N*localAlpha*a)+t*growingCeiling N (1/100000000000))) :
    p ≤ (k : ℝ)*(1+t)*Real.exp (-N*localAlpha*innerEnergy/2) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hh : Real.exp (N*localAlpha*b)*(p/k) ≤ Real.exp (N*localAlpha*a)+t*growingCeiling N (1/100000000000) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith only [h]
  have he := growth_exit_tail N (1/100000000000) b a t (p/k) hN ht
    (by norm_num) (by norm_num) hb ha hh
  have hf := (div_le_iff₀ hkpos).mp he
  simpa only [neg_mul,mul_assoc,mul_comm (k : ℝ)] using hf

theorem word_exit_tail {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (b : ℝ) (hb : b ≤ 1/32000000) (a : ℝ) (hgap : a ≤ b-innerEnergy/2) (hbmin : 2*innerEnergy ≤ b) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (retainedModularModel γ w hγ hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).total s ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b})
    (hstart : ∀ i, wordEnergy σ i (fun j => modularConcentration s.val i j-wordCenter z₀ z₁ σ i j) ≤ a) :
    ((retainedModularModel γ w hγ hw N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some s) ≤
      (k : ℝ)*(1+(t : ℝ))*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  have h := word_exit_bound hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁ w hdiag hsym hw hrow
    hγ hγmax hκ hκmax b hb a q t hq hclock s hstart
  exact scaled_exit_tail k hk N b a t _ (Nat.cast_nonneg N) t.property hbmin hgap
    (by simpa only [mul_comm (N : ℝ) localAlpha] using h)

end CompositionalMemory
