import proofs.CompositionalMemory.GenericGenerationLaw
import proofs.CompositionalMemory.GenericFirstPhaseEvent

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

/-- Compose proved phase estimates for the literal two-interval generation
law. These are phase estimates to be supplied by the reaction bounds, not a
one-generation accuracy assumption. -/
theorem general_two_phase_failure {k d : ℕ} {R : Type*} [Fintype R]
    (next : GeneralCountState k d → R → GeneralCountState k d)
    (rate : GeneralCountState k d → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (N C : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (c radius birth outer parent recover : ℝ) (hc : 0 < c)
    (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2) (hgap : recover < parent)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (q₀ t₀ q₁ t₁ : NNReal) (hq₀ : 0 < (q₀:ℝ)) (hq₁ : 0 < (q₁:ℝ))
    (hc₀ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) outer)).total s ≤ q₀)
    (hc₁ : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) parent)).total s ≤ q₁)
    (ε₀ ε₁ : ℝ) (hε₁ : 0 ≤ ε₁)
    (hsecond : ∀ s : {s : GeneralCountState k d // s ∈ generalProductDomain N C center (fun i y => Q i y y) parent},
      s.val.2 < 2*(k*N) →
      (∀ i, Q i (generalConcentration s.val i-center i) (generalConcentration s.val i-center i) ≤ recover) →
      (generalSecondPhaseLaw next rate hrate N C hN Q center c radius birth parent hc hr hb hcenter hcoerc
        q₁ t₁ hq₁ hc₁ s).mass none ≤ ε₁)
    (s : {s : GeneralCountState k d // s ∈ generalProductDomain N C center (fun i y => Q i y y) outer})
    (hfirst : ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) outer)).uniformize q₀ hq₀ hc₀).poissonized (q₀*t₀)
      (FiniteKernel.eventIndicator (generalFirstBad N (generalProductDomain N C center (fun i y => Q i y y) outer)
        center (fun i y => Q i y y) recover)) (some s) ≤ ε₀) :
    ((poissonLaw ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) outer)).uniformize q₀ hq₀ hc₀)
      (q₀*t₀) (some s)).bind
      (generalAfterRecovery next rate hrate N C hN Q center c radius birth outer parent recover
        hc hr hb hgap hcenter hcoerc q₁ t₁ hq₁ hc₁)).mass none ≤ ε₀+ε₁ := by
  classical
  let domain := generalProductDomain N C center (fun i y => Q i y y) outer
  have hpoint (x : Option {s : GeneralCountState k d // s ∈ domain}) :
      (generalAfterRecovery next rate hrate N C hN Q center c radius birth outer parent recover
        hc hr hb hgap hcenter hcoerc q₁ t₁ hq₁ hc₁ x).mass none ≤
      FiniteKernel.eventIndicator (generalFirstBad N domain center (fun i y => Q i y y) recover) x+ε₁ := by
    cases x with
    | none =>
      simpa [generalAfterRecovery,FiniteLaw.pure,FiniteKernel.eventIndicator,generalFirstBad] using
        (le_add_of_nonneg_right hε₁ : (1:ℝ) ≤ 1+ε₁)
    | some x =>
      by_cases hx : x.val.2 < 2*(k*N) ∧ ∀ i,
          Q i (generalConcentration x.val i-center i) (generalConcentration x.val i-center i) ≤ recover
      · have h := hsecond (generalEnterRecoveryDomain N C center (fun i y => Q i y y)
          outer parent recover hgap x hx.2) hx.1 hx.2
        have hn : ¬ some x ∈ generalFirstBad N domain center (fun i y => Q i y y) recover := not_not.mpr hx
        simpa only [generalAfterRecovery,dif_pos hx,FiniteKernel.eventIndicator,if_neg hn,zero_add] using h
      · have hy : some x ∈ generalFirstBad N domain center (fun i y => Q i y y) recover := hx
        simpa only [generalAfterRecovery,dif_neg hx,FiniteLaw.pure,FiniteKernel.eventIndicator,if_pos hy,if_true] using
          (le_add_of_nonneg_right hε₁ : (1:ℝ) ≤ 1+ε₁)
  change (poissonLaw _ _ _).expect (fun x =>
    (generalAfterRecovery next rate hrate N C hN Q center c radius birth outer parent recover
      hc hr hb hgap hcenter hcoerc q₁ t₁ hq₁ hc₁ x).mass none) ≤ _
  rw [poissonLaw_expect]
  have h := poisson_mono ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain).uniformize
    q₀ hq₀ hc₀) (q₀*t₀) _ _ hpoint (some s)
  rw [poisson_additive,poisson_constant] at h
  exact h.trans (add_le_add hfirst le_rfl)

end CompositionalMemory
