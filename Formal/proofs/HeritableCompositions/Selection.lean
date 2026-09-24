import proofs.HeritableCompositions.TimedGeneration
import proofs.HeritableCompositions.SourceBirthGeometry

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

noncomputable def highGeneration (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (n : BirthCount (highCertificate z γ hz hs hγ.le hmax) N) :
    FiniteLaw (BirthOutcome (highCertificate z γ hz hs hγ.le hmax) N) :=
  let C := highCertificate z γ hz hs hγ.le hmax
  timedGenerationLaw C hγ (highSecondDuration γ hγ hmax) N hN
    (chosenClock C hγ.le N outerEnergy ((N : ℝ)*localAlpha*innerEnergy/672))
    (chosenClock C hγ.le N (2*innerEnergy) (19*(γ*(297/100))*(N : ℝ)/400))
    (chosenClock_spec C hγ.le N outerEnergy _).1 (chosenClock_spec C hγ.le N (2*innerEnergy) _).1
    (chosenClock_spec C hγ.le N outerEnergy _).2.2 (chosenClock_spec C hγ.le N (2*innerEnergy) _).2.2 n

theorem high_faithful_reproduction (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (n : BirthCount (highCertificate z γ hz hs hγ.le hmax) N) :
    (highGeneration z γ hz hs hγ hmax N hN n).mass none ≤
      generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) := by
  let C := highCertificate z γ hz hs hγ.le hmax
  apply timed_generation_failure_bound C hγ hmax N hN hlarge _ _
    (chosenClock_spec C hγ.le N outerEnergy _).1 (chosenClock_spec C hγ.le N (2*innerEnergy) _).1
    (chosenClock_spec C hγ.le N outerEnergy _).2.2 (chosenClock_spec C hγ.le N (2*innerEnergy) _).2.2
    (chosenClock_spec C hγ.le N outerEnergy _).2.1 (γ*(297/100)) (by positivity)
    (highSecondDuration γ hγ hmax) (high_second_budget γ hγ hmax) (high_second_le_deadline γ hγ hmax)
    _ (chosenClock_spec C hγ.le N (2*innerEnergy) _).2.1 n
  intro d hd _
  exact (high_domain_membrane_rates z γ hz hγ.le N hN (2*innerEnergy)
    (by norm_num [innerEnergy,outerEnergy]) d hd).1

noncomputable def lowObservationTime (γ : ℝ) (hγ : 0 < γ) : NNReal :=
  ⟨lowTime γ, by unfold lowTime; positivity⟩

noncomputable def lowObservation (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (n : BirthCount (lowCertificate z γ hz hs hγ.le hmax) N) :=
  let C := lowCertificate z γ hz hs hγ.le hmax
  poissonLaw ((stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).uniformize
    (chosenClock C hγ.le N outerEnergy 0) (chosenClock_spec C hγ.le N outerEnergy 0).1
    (chosenClock_spec C hγ.le N outerEnergy 0).2.2)
    (chosenClock C hγ.le N outerEnergy 0*lowObservationTime γ hγ) (some (birthAsOuter C N hN n))

theorem low_undivided_bound (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (n : BirthCount (lowCertificate z γ hz hs hγ.le hmax) N) :
    (lowObservation z γ hz hs hγ hmax N hN n).expect
      (fun x => FiniteKernel.eventIndicator {none} x+
        FiniteKernel.eventIndicator (divisionRecorded N _) x) ≤
      (2+lowTime γ)*Real.exp (-(N : ℝ)*heredityExponent) := by
  let C := lowCertificate z γ hz hs hγ.le hmax
  let q := chosenClock C hγ.le N outerEnergy 0
  have hq := chosenClock_spec C hγ.le N outerEnergy 0
  have ht : (γ*(101/100))*(lowObservationTime γ hγ : ℝ) ≤ 2/5 := by
    change (γ*(101/100))*(40/(101*γ)) ≤ 2/5
    have hg : γ ≠ 0 := ne_of_gt hγ
    field_simp
    norm_num
  have hearly := (early_division_tail γ (γ*(101/100)) hγ.le (by positivity) N _
    (fun d hd _ => (low_domain_membrane_rates z γ hz hγ.le N hN outerEnergy le_rfl d hd).2)
    q (lowObservationTime γ hγ) hq.1 ht hq.2.2 (birthAsOuter C N hN n) rfl).trans (early_error_weaken N)
  have he := (mem_birthDomain C N hN n.val).mp n.property
  have hgap : C.energy (fun i => concentration (birthAsOuter C N hN n).val.2
      (birthAsOuter C N hN n).val.1 i-C.center i) ≤ outerEnergy-innerEnergy/2 := by
    change C.energy (fun i => concentration N n.val i-C.center i) ≤ _
    norm_num [innerEnergy,outerEnergy] at he ⊢
    linarith only [he]
  have hexit := certificate_exit C hγ.le hmax N hN outerEnergy le_rfl
    (by norm_num [innerEnergy,outerEnergy]) q (lowObservationTime γ hγ) hq.1 hq.2.2
    (birthAsOuter C N hN n) hgap
  change (poissonLaw _ _ _).expect _ ≤ _
  rw [poissonLaw_expect,poisson_additive]
  change _ ≤ (2+(lowObservationTime γ hγ : ℝ))*Real.exp (-(N : ℝ)*heredityExponent)
  convert add_le_add hexit hearly using 1
  ring

end HeritableCompositions
