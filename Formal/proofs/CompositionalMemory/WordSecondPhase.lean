import proofs.CompositionalMemory.WordGenerationLaw

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

theorem word_partition_error_weaken (N : ℕ) :
    Real.exp (-(N : ℝ)*(1/1000000)^2/35) ≤ Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  apply Real.exp_le_exp.mpr
  norm_num [localAlpha,innerEnergy,outerEnergy]
  nlinarith only [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem word_late_error_weaken (k N : ℕ) (hk : 1 ≤ k) :
    Real.exp (-9*((k*N : ℕ) : ℝ)/4000) ≤ (k : ℝ)*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  have hkn : (N : ℝ) ≤ ((k*N : ℕ) : ℝ) := by
    exact_mod_cast (show N ≤ k*N by simpa using Nat.mul_le_mul_right N hk)
  have he : Real.exp (-9*((k*N : ℕ) : ℝ)/4000) ≤ Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
    apply Real.exp_le_exp.mpr
    norm_num [localAlpha,innerEnergy,outerEnergy] at hkn ⊢
    nlinarith only [hkn,(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact he.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hkr (Real.exp_pos (-(N : ℝ)*localAlpha*innerEnergy/2)).le)

theorem word_after_division_failure {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (x : StoppedModularState (productDomain N center (wordEnergy σ) (2*innerEnergy))) :
    (wordAfterDivision N hN center hc σ x).mass none ≤ FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (modularActiveLiving N (productDomain N center (wordEnergy σ) (2*innerEnergy))) x+
        8*(k : ℝ)*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2)) := by
  classical
  have hbudget : (1 : ℝ) ≤ 1+8*(k : ℝ)*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) :=
    le_add_of_nonneg_right (by positivity)
  cases x with
  | none => simpa [wordAfterDivision,FiniteLaw.pure,FiniteKernel.eventIndicator,modularActiveLiving] using hbudget
  | some s =>
    have hmem := (mem_productDomain hk N hN center hc _ (word_energy_lower σ) (2*innerEnergy)
      (by norm_num [innerEnergy,outerEnergy]) s.val).mp s.property
    by_cases hdiv : s.val.2=2*(k*N)
    · have hparent (i) : wordEnergy σ i (fun a => concentration (2*N) (s.val.1 i) a-center i a) ≤ 2*innerEnergy := by
        have h := (hmem.2.2 i).le
        change wordEnergy σ i (fun a => modularConcentration (s.val.1,s.val.2) i a-center i a) ≤ _ at h
        rw [hdiv,division_lattice_concentration hk N s.val.1 i] at h
        exact h
      have hp := (wordPartitionLaw_failure N hN center hc σ s.val.1 hparent).trans
        (mul_le_mul_of_nonneg_left (word_partition_error_weaken N) (by positivity : 0 ≤ 8*(k : ℝ)))
      simpa [wordAfterDivision,hdiv,FiniteKernel.eventIndicator,modularActiveLiving] using hp
    · have ha : s.val.2 < 2*(k*N) := by omega
      simpa [wordAfterDivision,hdiv,FiniteLaw.pure,FiniteKernel.eventIndicator,modularActiveLiving,ha] using hbudget

theorem word_second_phase_failure {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
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
    (s : {s : ModularCountState k // s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) (2*innerEnergy)})
    (hactive : s.val.2 < 2*(k*N))
    (hrecovered : ∀ i, wordEnergy σ i (fun a => modularConcentration s.val i a-wordCenter z₀ z₁ σ i a) ≤ innerEnergy) :
    (wordPhaseTwoLaw γ w hw hγ.le N hN (wordCenter z₀ z₁ σ) (word_center_bounds z₀ z₁ σ h₀ h₁).1
      σ q (modularDeadline γ hγ) hq hclock s).mass none ≤
      (k : ℝ)*(10+(modularDeadline γ hγ : ℝ))*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  have hout := word_exit_tail hk N hN z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁ w hdiag hsym hw hrow
    hγ.le hγmax hκ hκmax (2*innerEnergy) (by norm_num [innerEnergy,outerEnergy]) innerEnergy
    (by norm_num [innerEnergy,outerEnergy]) le_rfl q (modularDeadline γ hγ) hq hclock s hrecovered
  have hlate := (word_retained_late_division hk N hN z₀ z₁ γ σ hγ h₀ h₁ w hw (2*innerEnergy)
    (by norm_num [innerEnergy,outerEnergy]) q hq hclock hdecay s hactive).trans (word_late_error_weaken k N hk)
  change (poissonLaw _ _ _).expect (fun x => (wordAfterDivision N hN (wordCenter z₀ z₁ σ) hc.1 σ x).mass none) ≤ _
  rw [poissonLaw_expect]
  have h := poisson_mono ((retainedModularModel γ w hγ.le hw N
    (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) (2*innerEnergy))).uniformize q hq hclock)
    (q*modularDeadline γ hγ) (fun x => (wordAfterDivision N hN (wordCenter z₀ z₁ σ) hc.1 σ x).mass none)
    (fun x => FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (modularActiveLiving N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) (2*innerEnergy))) x+
       8*(k : ℝ)*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2)))
    (word_after_division_failure hk N hN (wordCenter z₀ z₁ σ) hc.1 σ) (some s)
  rw [poisson_additive,poisson_additive,poisson_constant] at h
  nlinarith only [h,hout,hlate]

end CompositionalMemory
