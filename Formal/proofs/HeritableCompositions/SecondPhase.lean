import proofs.HeritableCompositions.GenerationLaw

namespace HeritableCompositions
open FiniteCopy

theorem afterDivision_failure_bound {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) (hN : 1 ≤ N)
    (x : StoppedCompartment (growthDomain N C.center C.energy (2*innerEnergy))) :
    (afterDivision C N hN x).mass none ≤ FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (activeLiving N (growthDomain N C.center C.energy (2*innerEnergy))) x+
        8*Real.exp (-(N : ℝ)*heredityExponent)) := by
  classical
  have hbudget : (1 : ℝ) ≤ 1+8*Real.exp (-(N : ℝ)*heredityExponent) := le_add_of_nonneg_right (by positivity)
  cases x with
  | none => simpa [afterDivision,FiniteLaw.pure,FiniteKernel.eventIndicator,activeLiving] using hbudget
  | some c =>
    have hb : 2*innerEnergy ≤ outerEnergy := by norm_num [innerEnergy,outerEnergy]
    have hm := (mem_growthDomain N hN c.val C.center C.center_upper C.energy C.energy_lower (2*innerEnergy) hb).mp c.property
    by_cases hdiv : c.val.2=2*N
    · have hparent : C.energy (fun i => concentration (2*N) c.val.1 i-C.center i) ≤ 2*innerEnergy := by
        simpa only [hdiv] using hm.2.2.le
      have hp := (partitionLaw_failure C N hN c.val.1 hparent).trans
        (mul_le_mul_of_nonneg_left (partition_error_weaken N) (by norm_num : (0 : ℝ) ≤ 8))
      simpa [afterDivision,hdiv,FiniteKernel.eventIndicator,activeLiving] using hp
    · have hactive : c.val.2 < 2*N := by omega
      simpa [afterDivision,hdiv,FiniteLaw.pure,FiniteKernel.eventIndicator,activeLiving,hactive] using hbudget

theorem second_phase_failure {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q)
    (hk : 19*(γ*(99/100))*(N : ℝ)/400 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy (2*innerEnergy)}) (hc : c.val.2 < 2*N)
    (he : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy) :
    (phaseTwoLaw C hγ.le N hN q (secondDuration γ hγ hγmax) hq hclock c).mass none ≤
      (10+10/(9*γ))*Real.exp (-(N : ℝ)*heredityExponent) := by
  have hb : 2*innerEnergy ≤ outerEnergy := by norm_num [innerEnergy,outerEnergy]
  have hgap : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ 2*innerEnergy-innerEnergy/2 := by
    have hA : 0 ≤ innerEnergy := by norm_num [innerEnergy,outerEnergy]
    linarith only [he,hA]
  have hexit := certificate_exit C hγ.le hγmax N hN (2*innerEnergy) hb le_rfl
    q (secondDuration γ hγ hγmax) hq hclock c hgap
  have hlate := certificate_late C hγ hγmax N hN q hq hclock hk c hc
  change (poissonLaw _ _ _).expect (fun x => (afterDivision C N hN x).mass none) ≤ _
  rw [poissonLaw_expect]
  have h := poisson_mono ((stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).uniformize q hq hclock)
    (q*secondDuration γ hγ hγmax) (fun x => (afterDivision C N hN x).mass none)
    (fun x => FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (activeLiving N (growthDomain N C.center C.energy (2*innerEnergy))) x+
        8*Real.exp (-(N : ℝ)*heredityExponent))) (afterDivision_failure_bound C N hN) (some c)
  rw [poisson_additive,poisson_additive,poisson_constant] at h
  have ht := mul_le_mul_of_nonneg_right (secondDuration_le_deadline γ hγ hγmax)
    (Real.exp_pos (-(N : ℝ)*heredityExponent)).le
  nlinarith only [h,hexit,hlate,ht]

end HeritableCompositions
