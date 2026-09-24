import proofs.CompositionalMemory.RetainedWordRecovery
import proofs.CompositionalMemory.RetainedWordClock
import proofs.CompositionalMemory.WordExitTail
import proofs.HeritableCompositions.KernelComposition

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

noncomputable def wordFirstBad {k : ℕ} (N : ℕ) (center : Fin k → Point) (σ : Fin k → Bool) :
    Set (StoppedModularState (productDomain N center (wordEnergy σ) outerEnergy)) :=
  {x | match x with | none => True | some s => ¬(s.val.2 < 2*(k*N) ∧
    ∀ i, wordEnergy σ i (fun a => modularConcentration s.val i a-center i a) ≤ innerEnergy)}

theorem word_first_bad_covered {k : ℕ} (N : ℕ) (center : Fin k → Point) (σ : Fin k → Bool)
    (x : StoppedModularState (productDomain N center (wordEnergy σ) outerEnergy)) :
    FiniteKernel.eventIndicator (wordFirstBad N center σ) x ≤
      FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (modularDivisionRecorded N (productDomain N center (wordEnergy σ) outerEnergy)) x+
       FiniteKernel.eventIndicator (wordRetainedUnrecovered N center σ (productDomain N center (wordEnergy σ) outerEnergy)) x) := by
  classical
  cases x with
  | none => simp [FiniteKernel.eventIndicator,wordFirstBad,modularDivisionRecorded,wordRetainedUnrecovered]
  | some s =>
    by_cases ha : s.val.2 < 2*(k*N)
    · have hdiv : ¬2*(k*N) ≤ s.val.2 := not_le.mpr ha
      by_cases he : ∀ i, wordEnergy σ i (fun a => modularConcentration s.val i a-center i a) ≤ innerEnergy
      · have hn : ¬∃ i, innerEnergy < wordEnergy σ i (fun a => modularConcentration s.val i a-center i a) := by
          simp only [not_exists]
          intro i
          exact not_lt.mpr (he i)
        simp [FiniteKernel.eventIndicator,wordFirstBad,modularDivisionRecorded,wordRetainedUnrecovered,ha,hdiv,hn]
      · have hn := he
        push Not at hn
        simp [FiniteKernel.eventIndicator,wordFirstBad,modularDivisionRecorded,wordRetainedUnrecovered,ha,hdiv,hn]
    · have hdiv : 2*(k*N) ≤ s.val.2 := Nat.le_of_not_gt ha
      simp [FiniteKernel.eventIndicator,wordFirstBad,modularDivisionRecorded,wordRetainedUnrecovered,ha,hdiv]

theorem word_early_error_weaken (k N : ℕ) (hk : 1 ≤ k) :
    Real.exp (-((k*N : ℕ) : ℝ)/125) ≤ (k : ℝ)*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  have hkn : (N : ℝ) ≤ ((k*N : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ k*N by simpa using Nat.mul_le_mul_right N hk)
  have he : Real.exp (-((k*N : ℕ) : ℝ)/125) ≤ Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
    apply Real.exp_le_exp.mpr
    norm_num [localAlpha,innerEnergy,outerEnergy] at hkn ⊢
    nlinarith only [hkn,(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact he.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hkr (Real.exp_pos (-(N : ℝ)*localAlpha*innerEnergy/2)).le)

theorem word_first_phase_failure {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (hNlarge : 140000000000000000000 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (retainedModularModel γ w hγ hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)).total x ≤ q)
    (hdecay : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy})
    (hstart : s.val.2=k*N)
    (hbirth : ∀ i, wordEnergy σ i (fun a => modularConcentration s.val i a-wordCenter z₀ z₁ σ i a) ≤ 4*innerEnergy) :
    ((retainedModularModel γ w hγ hw N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)).uniformize q hq hclock).poissonized
      (q*2688) (FiniteKernel.eventIndicator (wordFirstBad N (wordCenter z₀ z₁ σ) σ)) (some s) ≤
      2693*(k : ℝ)*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  have hM : 0 < k*N := Nat.mul_pos (by omega) (by omega)
  have ha : s.val.2 < 2*(k*N) := by omega
  have hout := word_exit_tail hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁ w hdiag hsym hw hrow
    hγ hγmax hκ hκmax outerEnergy (by norm_num [outerEnergy]) (4*innerEnergy)
    (by norm_num [innerEnergy,outerEnergy]) (by norm_num [innerEnergy,outerEnergy]) q 2688 hq hclock s hbirth
  have hearly := (word_early_division hk N hN z₀ z₁ γ σ hγ hγmax h₀ h₁ w hw outerEnergy
    (by norm_num [outerEnergy]) q hq hclock s hstart).trans (word_early_error_weaken k N hk)
  have hrec := word_retained_recovery hk N hN hNlarge z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁
    w hdiag hsym hw hrow hγ hγmax hκ hκmax outerEnergy (by norm_num [outerEnergy])
    q hq hclock hdecay s ha hbirth
  have h := poisson_mono ((retainedModularModel γ w hγ hw N
    (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)).uniformize q hq hclock)
    (q*2688) (FiniteKernel.eventIndicator (wordFirstBad N (wordCenter z₀ z₁ σ) σ))
    (fun x => FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (modularDivisionRecorded N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)) x+
       FiniteKernel.eventIndicator (wordRetainedUnrecovered N (wordCenter z₀ z₁ σ) σ
         (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) outerEnergy)) x))
    (word_first_bad_covered N (wordCenter z₀ z₁ σ) σ) (some s)
  rw [poisson_additive,poisson_additive] at h
  norm_num only [NNReal.coe_ofNat] at hout
  nlinarith only [h,hout,hearly,hrec]

end CompositionalMemory
