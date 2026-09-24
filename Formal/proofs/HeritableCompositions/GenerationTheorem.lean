import proofs.HeritableCompositions.FirstPhase
import proofs.HeritableCompositions.SecondPhase

namespace HeritableCompositions
open FiniteCopy

theorem generation_failure_bound {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q₁)
    (hk₀ : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q₀)
    (hk₁ : 19*(γ*(99/100))*(N : ℝ)/400 ≤ q₁)
    (n : BirthCount C N) :
    (generationLaw C hγ hγmax N hN q₀ q₁ hq₀ hq₁ hc₀ hc₁ n).mass none ≤
      generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) := by
  classical
  let f := afterRecovery C hγ.le N hN q₁ (secondDuration γ hγ hγmax) hq₁ hc₁
  have hgood (x : StoppedCompartment (growthDomain N C.center C.energy outerEnergy))
      (hx : x ∉ firstBad C N) : (f x).mass none ≤
      (10+10/(9*γ))*Real.exp (-(N : ℝ)*heredityExponent) := by
    cases x with
    | none => exact False.elim (hx trivial)
    | some c =>
      have hg : c.val.2 < 2*N ∧ C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy := by
        simpa only [firstBad,Set.mem_setOf_eq,not_not] using hx
      change (afterRecovery C hγ.le N hN q₁ (secondDuration γ hγ hγmax) hq₁ hc₁ (some c)).mass none ≤ _
      rw [afterRecovery,dif_pos hg]
      exact second_phase_failure C hγ hγmax N hN q₁ hq₁ hc₁ hk₁ (enterInner C N hN c hg.2) hg.1 hg.2
  have hbirth : C.energy (fun i => concentration (birthAsOuter C N hN n).val.2
      (birthAsOuter C N hN n).val.1 i-C.center i) ≤ 4*innerEnergy :=
    (mem_birthDomain C N hN n.val).mp n.property
  have hfirst := first_phase_failure C hγ.le hγmax N hN hlarge q₀ hq₀ hc₀ hk₀
    (birthAsOuter C N hN n) rfl hbirth
  have h := poisson_bad_state_bound
    ((stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).uniformize q₀ hq₀ hc₀)
    (q₀*4032) (firstBad C N) (fun x => (f x).mass none)
    ((10+10/(9*γ))*Real.exp (-(N : ℝ)*heredityExponent)) (by positivity)
    (fun x => law_mass_le_one (f x) none) hgood (some (birthAsOuter C N hN n))
  change (poissonLaw _ _ _).expect (fun x => (f x).mass none) ≤ _
  rw [poissonLaw_expect]
  unfold generationPrefactor
  linarith only [h,hfirst]

noncomputable def chosenClock {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ)
    (N : ℕ) (b k : ℝ) : NNReal :=
  Classical.choose ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy b)).exists_clock k)

theorem chosenClock_spec {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ) (N : ℕ) (b k : ℝ) :
    0 < (chosenClock C hγ N b k : ℝ) ∧ k ≤ chosenClock C hγ N b k ∧
      ∀ x, (stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy b)).total x ≤ chosenClock C hγ N b k :=
  Classical.choose_spec ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy b)).exists_clock k)

noncomputable def certifiedGeneration {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N) (n : BirthCount C N) : FiniteLaw (BirthOutcome C N) :=
  generationLaw C hγ hγmax N hN
    (chosenClock C hγ.le N outerEnergy ((N : ℝ)*localAlpha*innerEnergy/672))
    (chosenClock C hγ.le N (2*innerEnergy) (19*(γ*(99/100))*(N : ℝ)/400))
    (chosenClock_spec C hγ.le N outerEnergy _).1 (chosenClock_spec C hγ.le N (2*innerEnergy) _).1
    (chosenClock_spec C hγ.le N outerEnergy _).2.2 (chosenClock_spec C hγ.le N (2*innerEnergy) _).2.2 n

theorem certified_generation_failure {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (n : BirthCount C N) :
    (certifiedGeneration C hγ hγmax N hN n).mass none ≤
      generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) :=
  generation_failure_bound C hγ hγmax N hN hlarge _ _
    (chosenClock_spec C hγ.le N outerEnergy _).1 (chosenClock_spec C hγ.le N (2*innerEnergy) _).1
    (chosenClock_spec C hγ.le N outerEnergy _).2.2 (chosenClock_spec C hγ.le N (2*innerEnergy) _).2.2
    (chosenClock_spec C hγ.le N outerEnergy _).2.1 (chosenClock_spec C hγ.le N (2*innerEnergy) _).2.1 n

end HeritableCompositions
