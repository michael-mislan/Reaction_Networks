import proofs.HeritableCompositions.BirthLaw
import proofs.HeritableCompositions.CertificateBounds

namespace HeritableCompositions
open FiniteCopy

theorem law_mass_le_one {α : Type*} [Fintype α] (μ : FiniteLaw α) (x : α) : μ.mass x ≤ 1 := by
  rw [← μ.total]
  exact Finset.single_le_sum (fun y _ => μ.nonneg y) (Finset.mem_univ x)

noncomputable def afterDivision {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) (hN : 1 ≤ N) :
    StoppedCompartment (growthDomain N C.center C.energy (2*innerEnergy)) → FiniteLaw (BirthOutcome C N)
  | none => FiniteLaw.pure none
  | some c => if c.val.2=2*N then partitionLaw C N hN c.val.1 else FiniteLaw.pure none

noncomputable def phaseTwoLaw {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ)
    (N : ℕ) (hN : 1 ≤ N) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy (2*innerEnergy)}) :
    FiniteLaw (BirthOutcome C N) :=
  (poissonLaw ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy (2*innerEnergy))).uniformize q hq hclock)
    (q*t) (some c)).bind (afterDivision C N hN)

noncomputable def firstBad {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) :
    Set (StoppedCompartment (growthDomain N C.center C.energy outerEnergy)) :=
  {x | match x with
    | none => True
    | some c => ¬(c.val.2 < 2*N ∧ C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy)}

noncomputable def enterInner {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) (hN : 1 ≤ N)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy outerEnergy})
    (he : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy) :
    {c : Compartment // c ∈ growthDomain N C.center C.energy (2*innerEnergy)} := by
  have hb : 2*innerEnergy ≤ outerEnergy := by norm_num [innerEnergy,outerEnergy]
  have hm := (mem_growthDomain N hN c.val C.center C.center_upper C.energy C.energy_lower outerEnergy le_rfl).mp c.property
  refine ⟨c.val,(mem_growthDomain N hN c.val C.center C.center_upper C.energy C.energy_lower (2*innerEnergy) hb).mpr ⟨hm.1,hm.2.1,?_⟩⟩
  have hA : 0 < innerEnergy := by norm_num [innerEnergy,outerEnergy]
  linarith only [he,hA]

noncomputable def afterRecovery {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ)
    (N : ℕ) (hN : 1 ≤ N) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q) :
    StoppedCompartment (growthDomain N C.center C.energy outerEnergy) → FiniteLaw (BirthOutcome C N)
  | none => FiniteLaw.pure none
  | some c => if h : c.val.2 < 2*N ∧ C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ innerEnergy then
      phaseTwoLaw C hγ N hN q t hq hclock (enterInner C N hN c h.2)
    else FiniteLaw.pure none

noncomputable def birthAsOuter {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) (hN : 1 ≤ N)
    (n : BirthCount C N) : {c : Compartment // c ∈ growthDomain N C.center C.energy outerEnergy} := by
  have he := (mem_birthDomain C N hN n.val).mp n.property
  refine ⟨(n.val,N),(mem_growthDomain N hN (n.val,N) C.center C.center_upper C.energy C.energy_lower outerEnergy le_rfl).mpr
    ⟨le_rfl,by omega,?_⟩⟩
  norm_num [innerEnergy,outerEnergy] at he ⊢
  linarith only [he]

/-- Literal two-interval growth, stopped on unsafe departure/division, followed
by the complementary binomial split. None records a prescribed path failure. -/
noncomputable def generationLaw {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q₁)
    (n : BirthCount C N) : FiniteLaw (BirthOutcome C N) :=
  (poissonLaw ((stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy outerEnergy)).uniformize q₀ hq₀ hc₀)
    (q₀*4032) (some (birthAsOuter C N hN n))).bind
      (afterRecovery C hγ.le N hN q₁ (secondDuration γ hγ hγmax) hq₁ hc₁)

end HeritableCompositions
