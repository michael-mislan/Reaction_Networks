import proofs.CompositionalMemory.WordEnvelope
import proofs.CompositionalMemory.ModularStopped
import proofs.CompositionalMemory.SumObservables

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

noncomputable def wordPredivisionDomain {k : ℕ} (N : ℕ) (z₀ z₁ : ℝ)
    (σ : Fin k → Bool) (b : ℝ) : Finset (ModularCountState k) := by
  classical
  exact (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b).filter
    (fun s => s.2 < 2*(k*N))

theorem word_recovery_bound {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (hNlarge : 140000000000000000000 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (b : ℝ) (hb : b ≤ 1/32000000) (a r : ℝ) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (killedModularModel γ w hγ hw (wordPredivisionDomain N z₀ z₁ σ b)).total s ≤ q)
    (hdecay : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (s : {s : ModularCountState k // s ∈ wordPredivisionDomain N z₀ z₁ σ b})
    (hstart : ∀ i, wordEnergy σ i (fun j => modularConcentration s.val i j-wordCenter z₀ z₁ σ i j) ≤ a) :
    Real.exp (localAlpha*(N : ℝ)*r)*
      ((killedModularModel γ w hγ hw (wordPredivisionDomain N z₀ z₁ σ b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {x | ∃ i, Real.exp (localAlpha*(N : ℝ)*r) ≤
          stoppedModularObservable (wordPredivisionDomain N z₀ z₁ σ b)
            (fun u => Real.exp (localAlpha*(N : ℝ)*wordEnergy σ i
              (fun j => modularConcentration u i j-wordCenter z₀ z₁ σ i j))) 0 x}) (some s) ≤
      (k : ℝ)*(Real.exp (-((N : ℝ)*localAlpha*innerEnergy/672)*(t : ℝ))*
        Real.exp (localAlpha*(N : ℝ)*a)+2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  classical
  let D := wordPredivisionDomain N z₀ z₁ σ b
  let F : Fin k → ModularCountState k → ℝ := fun i u => Real.exp (localAlpha*(N : ℝ)*
    wordEnergy σ i (fun j => modularConcentration u i j-wordCenter z₀ z₁ σ i j))
  have hd : 0 ≤ (N : ℝ)*localAlpha*innerEnergy/672 := by
    unfold localAlpha innerEnergy outerEnergy; positivity
  have hC : 0 ≤ 2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2) := by positivity
  apply product_recovery_bound (killedModularModel γ w hγ hw D)
    (fun i => stoppedModularObservable D (F i) 0) q t hq hclock
    (Real.exp (localAlpha*(N : ℝ)*r)) ((N : ℝ)*localAlpha*innerEnergy/672)
    (2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) (Real.exp (localAlpha*(N : ℝ)*a))
  · intro i x
    cases x with
    | none => exact le_rfl
    | some x => exact (Real.exp_pos _).le
  · exact hdecay
  · exact hC
  · intro i x
    apply killed_modular_affine γ w hγ hw D (F i) _ _ (fun u => (Real.exp_pos _).le) hd hC
    intro u hu
    have hu' : u ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b :=
      (Finset.mem_filter.mp hu).1
    have h := word_generator_affine hk N hN hNlarge z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁
      w hdiag hsym hw hrow hγ hγmax hκ hκmax b hb u hu' i
    simpa only [F,mul_comm (N : ℝ) localAlpha] using h
  · intro i
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hstart i)
      (mul_nonneg (by norm_num [localAlpha]) (Nat.cast_nonneg N)))

end CompositionalMemory
