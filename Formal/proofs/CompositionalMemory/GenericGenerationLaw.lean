import proofs.CompositionalMemory.GenericBirthLaw
import proofs.CompositionalMemory.GenericRetainedReactions

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def generalAfterDivision {k d : ℕ} (N C : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (c radius birth parent : ℝ) (hc : 0 < c)
    (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y) :
    Option {s : GeneralCountState k d // s ∈ generalProductDomain N C center (fun i y => Q i y y) parent} →
      FiniteLaw (GeneralBirthOutcome N C center (fun i y => Q i y y) birth)
  | none => FiniteLaw.pure none
  | some s => if s.val.2=2*(k*N) then
      generalPartitionLaw N C hN Q center c radius birth hc hr hb hcenter hcoerc s.val.1
    else FiniteLaw.pure none

noncomputable def generalSecondPhaseLaw {k d : ℕ} {R : Type*} [Fintype R]
    (next : GeneralCountState k d → R → GeneralCountState k d)
    (rate : GeneralCountState k d → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (N C : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (c radius birth parent : ℝ) (hc : 0 < c)
    (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) parent)).total s ≤ q)
    (s : {s : GeneralCountState k d // s ∈ generalProductDomain N C center (fun i y => Q i y y) parent}) :
    FiniteLaw (GeneralBirthOutcome N C center (fun i y => Q i y y) birth) :=
  (poissonLaw ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
    (generalProductDomain N C center (fun i y => Q i y y) parent)).uniformize q hq hclock)
    (q*t) (some s)).bind (generalAfterDivision N C hN Q center c radius birth parent hc hr hb hcenter hcoerc)

noncomputable def generalEnterRecoveryDomain {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (outer parent recover : ℝ) (hgap : recover < parent)
    (s : {s : GeneralCountState k d // s ∈ generalProductDomain N C center E outer})
    (he : ∀ i, E i (fun a => generalConcentration s.val i a-center i a) ≤ recover) :
    {s : GeneralCountState k d // s ∈ generalProductDomain N C center E parent} := by
  classical
  refine ⟨s.val,?_⟩
  have hs := s.property
  unfold generalProductDomain at hs ⊢
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1,fun i => (he i).trans_lt hgap⟩

noncomputable def generalAfterRecovery {k d : ℕ} {R : Type*} [Fintype R]
    (next : GeneralCountState k d → R → GeneralCountState k d)
    (rate : GeneralCountState k d → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (N C : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (c radius birth outer parent recover : ℝ) (hc : 0 < c)
    (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2) (hgap : recover < parent)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) parent)).total s ≤ q) :
    Option {s : GeneralCountState k d // s ∈ generalProductDomain N C center (fun i y => Q i y y) outer} →
      FiniteLaw (GeneralBirthOutcome N C center (fun i y => Q i y y) birth) := by
  classical
  exact fun x => match x with
  | none => FiniteLaw.pure none
  | some s => if h : s.val.2 < 2*(k*N) ∧ ∀ i,
      Q i (generalConcentration s.val i-center i) (generalConcentration s.val i-center i) ≤ recover then
      generalSecondPhaseLaw next rate hrate N C hN Q center c radius birth parent hc hr hb hcenter hcoerc
        q t hq hclock (generalEnterRecoveryDomain N C center (fun i y => Q i y y) outer parent recover hgap s h.2)
    else FiniteLaw.pure none

/-- Two literal retained reaction intervals, with a recovery gate and one
complementary partition. The law is normalized; its accuracy is proved separately. -/
noncomputable def generalGenerationLaw {k d : ℕ} {R : Type*} [Fintype R]
    (hk : 1 ≤ k) (next : GeneralCountState k d → R → GeneralCountState k d)
    (rate : GeneralCountState k d → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (N C : ℕ) (hN : 1 ≤ N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (c radius birth outer parent recover : ℝ) (hc : 0 < c)
    (hr : 0 ≤ radius) (hbirth : birth ≤ outer) (houter : outer ≤ c*radius^2) (hgap : recover < parent)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (q₀ t₀ q₁ t₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
    (hc₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) outer)).total s ≤ q₀)
    (hc₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) parent)).total s ≤ q₁)
    (n : GeneralBirthCount N C center (fun i y => Q i y y) birth) :
    FiniteLaw (GeneralBirthOutcome N C center (fun i y => Q i y y) birth) := by
  let hE := fun i => norm_coercive_coordinate (Q i) c hc.le (hcoerc i)
  let start : {s : GeneralCountState k d // s ∈ generalProductDomain N C center (fun i y => Q i y y) outer} :=
    ⟨(n.val,k*N),general_birth_in_growth_domain hk N C hN center (fun i y => Q i y y)
      c radius birth outer hc hr hbirth houter hcenter hE n⟩
  exact (poissonLaw ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
    (generalProductDomain N C center (fun i y => Q i y y) outer)).uniformize q₀ hq₀ hc₀)
    (q₀*t₀) (some start)).bind
    (generalAfterRecovery next rate hrate N C (by omega) Q center c radius birth outer parent recover
      hc hr (hbirth.trans houter) hgap hcenter hcoerc q₁ t₁ hq₁ hc₁)

end CompositionalMemory
