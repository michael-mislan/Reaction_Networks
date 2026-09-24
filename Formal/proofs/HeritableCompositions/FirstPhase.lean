import proofs.HeritableCompositions.GenerationLaw

namespace HeritableCompositions
open FiniteCopy

theorem firstBad_covered {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ)
    (x : StoppedCompartment (growthDomain N C.center C.energy outerEnergy)) :
    FiniteKernel.eventIndicator (firstBad C N) x ≤
      FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (divisionRecorded N (growthDomain N C.center C.energy outerEnergy)) x+
        FiniteKernel.eventIndicator (retainedUnrecovered N C.center C.energy) x) := by
  classical
  cases x with
  | none => simp [FiniteKernel.eventIndicator,firstBad,divisionRecorded,retainedUnrecovered]
  | some c =>
    by_cases hc : c.val.2 < 2*N
    · have hdiv : ¬2*N ≤ c.val.2 := not_le.mpr hc
      by_cases he : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy
      · have hE := not_lt.mpr he
        simp [FiniteKernel.eventIndicator,firstBad,divisionRecorded,retainedUnrecovered,hc,hdiv,hE]
      · have hE := not_le.mp he
        simp [FiniteKernel.eventIndicator,firstBad,divisionRecorded,retainedUnrecovered,hc,hdiv,hE]
    · have hdiv : 2*N ≤ c.val.2 := Nat.le_of_not_gt hc
      simp [FiniteKernel.eventIndicator,firstBad,divisionRecorded,retainedUnrecovered,hc,hdiv]

theorem first_phase_failure {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy outerEnergy)).total x ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy outerEnergy}) (hc : c.val.2=N)
    (hbirth : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ 4*innerEnergy) :
    ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy outerEnergy)).uniformize q hq hclock).poissonized (q*4032)
      (FiniteKernel.eventIndicator (firstBad C N)) (some c) ≤ 4037*Real.exp (-(N : ℝ)*heredityExponent) := by
  have hb : 2*innerEnergy ≤ outerEnergy := by norm_num [innerEnergy,outerEnergy]
  have hgap : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ outerEnergy-innerEnergy/2 := by
    norm_num [innerEnergy,outerEnergy] at hbirth ⊢
    linarith only [hbirth]
  have hout := certificate_exit C hγ hγmax N hN outerEnergy le_rfl hb q 4032 hq hclock c hgap
  have hearly := certificate_early C hγ hγmax N hN q hq hclock c hc
  have hrec := certificate_recovery C hγ N hN hlarge q hq hclock hk c (by omega) hbirth
  have h := poisson_mono ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy outerEnergy)).uniformize q hq hclock)
    (q*4032) (FiniteKernel.eventIndicator (firstBad C N))
    (fun x => FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (divisionRecorded N (growthDomain N C.center C.energy outerEnergy)) x+
        FiniteKernel.eventIndicator (retainedUnrecovered N C.center C.energy) x))
    (firstBad_covered C N) (some c)
  rw [poisson_additive,poisson_additive] at h
  norm_num at hout
  simp only [neg_mul] at hearly hrec ⊢
  linarith only [h,hout,hearly,hrec]

end HeritableCompositions
