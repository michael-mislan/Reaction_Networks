import proofs.HeritableCompositions.SelectionBudget

/- Variable second-phase deadline, with a reaction-derived lower clock rate. -/

namespace HeritableCompositions
open FiniteCopy

theorem timed_second_phase_failure {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q)
    (a : ℝ) (ha : 0 ≤ a) (t : NNReal)
    (ht : 1099/1000 ≤ a*(t : ℝ)) (htop : (t : ℝ) ≤ 10/(9*γ))
    (hrate : ∀ d ∈ growthDomain N C.center C.energy (2*innerEnergy),
      d.2 < 2*N → a*(N : ℝ) ≤ γ*(d.1 2 : ℝ))
    (hk : 19*a*(N : ℝ)/400 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy (2*innerEnergy)}) (hc : c.val.2 < 2*N)
    (he : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy) :
    (phaseTwoLaw C hγ.le N hN q t hq hclock c).mass none ≤
      (10+10/(9*γ))*Real.exp (-(N : ℝ)*heredityExponent) := by
  have hb : 2*innerEnergy ≤ outerEnergy := by norm_num [innerEnergy,outerEnergy]
  have hgap : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ 2*innerEnergy-innerEnergy/2 := by
    have hA : 0 ≤ innerEnergy := by norm_num [innerEnergy,outerEnergy]
    linarith only [he,hA]
  have hexit := certificate_exit C hγ.le hγmax N hN (2*innerEnergy) hb le_rfl
    q t hq hclock c hgap
  have hm := (mem_growthDomain N hN c.val C.center C.center_upper C.energy C.energy_lower (2*innerEnergy) hb).mp c.property
  have hlate := (retained_late_tail γ a hγ.le ha N _ hrate q t hq ht hclock hk c hm.1 hc).trans (clock_error_weaken N)
  change (poissonLaw _ _ _).expect (fun x => (afterDivision C N hN x).mass none) ≤ _
  rw [poissonLaw_expect]
  have h := poisson_mono ((stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).uniformize q hq hclock)
    (q*t) (fun x => (afterDivision C N hN x).mass none)
    (fun x => FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (activeLiving N (growthDomain N C.center C.energy (2*innerEnergy))) x+
        8*Real.exp (-(N : ℝ)*heredityExponent))) (afterDivision_failure_bound C N hN) (some c)
  rw [poisson_additive,poisson_additive,poisson_constant] at h
  have ht := mul_le_mul_of_nonneg_right htop
    (Real.exp_pos (-(N : ℝ)*heredityExponent)).le
  nlinarith only [h,hexit,hlate,ht]

noncomputable def timedGenerationLaw {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (t : NNReal) (N : ℕ) (hN : 1 ≤ N)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q₁)
    (n : BirthCount C N) : FiniteLaw (BirthOutcome C N) :=
  (poissonLaw ((stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).uniformize q₀ hq₀ hc₀)
    (q₀*4032) (some (birthAsOuter C N hN n))).bind
      (afterRecovery C hγ.le N hN q₁ t hq₁ hc₁)

theorem timed_generation_failure_bound {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q₁)
    (hk₀ : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q₀)
    (a : ℝ) (ha : 0 ≤ a) (t : NNReal)
    (ht : 1099/1000 ≤ a*(t : ℝ)) (htop : (t : ℝ) ≤ 10/(9*γ))
    (hrate : ∀ d ∈ growthDomain N C.center C.energy (2*innerEnergy),
      d.2 < 2*N → a*(N : ℝ) ≤ γ*(d.1 2 : ℝ))
    (hk₁ : 19*a*(N : ℝ)/400 ≤ q₁)
    (n : BirthCount C N) :
    (timedGenerationLaw C hγ t N hN q₀ q₁ hq₀ hq₁ hc₀ hc₁ n).mass none ≤
      generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) := by
  classical
  let f := afterRecovery C hγ.le N hN q₁ t hq₁ hc₁
  have hgood (x : StoppedCompartment (growthDomain N C.center C.energy outerEnergy))
      (hx : x ∉ firstBad C N) : (f x).mass none ≤
      (10+10/(9*γ))*Real.exp (-(N : ℝ)*heredityExponent) := by
    cases x with
    | none => exact False.elim (hx trivial)
    | some c =>
      have hg : c.val.2 < 2*N ∧ C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy := by
        simpa only [firstBad,Set.mem_setOf_eq,not_not] using hx
      change (afterRecovery C hγ.le N hN q₁ t hq₁ hc₁ (some c)).mass none ≤ _
      rw [afterRecovery,dif_pos hg]
      exact timed_second_phase_failure C hγ hγmax N hN q₁ hq₁ hc₁ a ha t ht htop hrate hk₁ (enterInner C N hN c hg.2) hg.1 hg.2
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


end HeritableCompositions
