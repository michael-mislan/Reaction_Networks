import proofs.CompositionalMemory.WordSecondPhase

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

theorem word_after_recovery_failure {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (retainedModularModel γ w hγ.le hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) (2*innerEnergy))).total x ≤ q)
    (hdecay : 19*(γ/2)*((k*N : ℕ) : ℝ)/400 ≤ q)
    (x : StoppedModularState (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)) :
    (wordAfterRecovery hk γ w hw hγ.le N hN (wordCenter z₀ z₁ σ)
      (word_center_bounds z₀ z₁ σ h₀ h₁).1 σ q (modularDeadline γ hγ) hq hclock x).mass none ≤
      FiniteKernel.eventIndicator (wordFirstBad N (wordCenter z₀ z₁ σ) σ) x+
      (k : ℝ)*(10+(modularDeadline γ hγ : ℝ))*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  classical
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  have hb : (1 : ℝ) ≤ 1+(k : ℝ)*(10+(modularDeadline γ hγ : ℝ))*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) :=
    le_add_of_nonneg_right (by positivity)
  cases x with
  | none => simpa [wordAfterRecovery,FiniteLaw.pure,FiniteKernel.eventIndicator,wordFirstBad] using hb
  | some s =>
    by_cases hs : s.val.2 < 2*(k*N) ∧ ∀ i,
        wordEnergy σ i (fun a => modularConcentration s.val i a-wordCenter z₀ z₁ σ i a) ≤ innerEnergy
    · have h := word_second_phase_failure hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁ w hdiag hsym hw hrow
        hγ hγmax hκ hκmax q hq hclock hdecay (wordEnterInner hk N hN _ hc.1 σ s hs.2) hs.1 hs.2
      simpa only [wordAfterRecovery, dif_pos hs, FiniteKernel.eventIndicator,
        wordFirstBad, Set.mem_setOf_eq, if_neg (show ¬¬(s.val.2 < 2*(k*N) ∧ ∀ i,
          wordEnergy σ i (fun a => modularConcentration s.val i a-wordCenter z₀ z₁ σ i a) ≤ innerEnergy) from not_not.mpr hs), zero_add] using h
    · simpa only [wordAfterRecovery, dif_neg hs, FiniteLaw.pure,
        FiniteKernel.eventIndicator, wordFirstBad, Set.mem_setOf_eq, if_pos hs, if_true] using hb

theorem word_generation_failure {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (hNlarge : 140000000000000000000 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x, (retainedModularModel γ w hγ.le hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x, (retainedModularModel γ w hγ.le hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) (2*innerEnergy))).total x ≤ q₁)
    (hd₀ : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q₀)
    (hd₁ : 19*(γ/2)*((k*N : ℕ) : ℝ)/400 ≤ q₁)
    (n : WordBirthCount N (wordCenter z₀ z₁ σ) σ) :
    (wordGenerationLaw hk γ hγ w hw N hN (wordCenter z₀ z₁ σ)
      (word_center_bounds z₀ z₁ σ h₀ h₁).1 σ q₀ q₁ hq₀ hq₁ hc₀ hc₁ n).mass none ≤
      (k : ℝ)*(2703+11/(5*γ))*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  let s := wordBirthAsOuter hk N hN (wordCenter z₀ z₁ σ) hc.1 σ n
  have hbirth (i) : wordEnergy σ i (fun a => modularConcentration s.val i a-wordCenter z₀ z₁ σ i a) ≤ 4*innerEnergy := by
    change wordEnergy σ i (fun a => modularConcentration (n.val,k*N) i a-wordCenter z₀ z₁ σ i a) ≤ _
    rw [module_lattice_concentration hk N n.val i]
    exact ((mem_wordBirthCounts N hN _ hc.1 σ n.val).mp n.property) i
  have hfirst := word_first_phase_failure hk N hN hNlarge z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁
    w hdiag hsym hw hrow hγ.le hγmax hκ hκmax q₀ hq₀ hc₀ hd₀ s rfl hbirth
  change (poissonLaw _ _ _).expect (fun x =>
    (wordAfterRecovery hk γ w hw hγ.le N hN (wordCenter z₀ z₁ σ) hc.1 σ q₁ (modularDeadline γ hγ) hq₁ hc₁ x).mass none) ≤ _
  rw [poissonLaw_expect]
  have h := poisson_mono ((retainedModularModel γ w hγ.le hw N
    (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)).uniformize q₀ hq₀ hc₀)
    (q₀*2688) (fun x => (wordAfterRecovery hk γ w hw hγ.le N hN (wordCenter z₀ z₁ σ) hc.1 σ q₁ (modularDeadline γ hγ) hq₁ hc₁ x).mass none)
    (fun x => FiniteKernel.eventIndicator (wordFirstBad N (wordCenter z₀ z₁ σ) σ) x+
      (k : ℝ)*(10+(modularDeadline γ hγ : ℝ))*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2))
    (word_after_recovery_failure hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁ w hdiag hsym hw hrow
      hγ hγmax hκ hκmax q₁ hq₁ hc₁ hd₁) (some s)
  rw [poisson_additive,poisson_constant] at h
  change _ ≤ (k : ℝ)*(2703+(modularDeadline γ hγ : ℝ))*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2)
  nlinarith only [h,hfirst]

end CompositionalMemory
