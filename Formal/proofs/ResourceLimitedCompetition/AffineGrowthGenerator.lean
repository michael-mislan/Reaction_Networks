import proofs.HeritableCompositions.SourceAffine

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- Resource depletion scales only the consumptive growth channel. -/
noncomputable def resourceCoefficient (γ : ℝ) (Q Ω : ℕ) : ℝ :=
  γ * ((Q : ℝ) / (Ω : ℝ))

theorem resource_coefficient_bounds (γ : ℝ) (Q Ω : ℕ)
    (hγ : 0 ≤ γ) (hQ : Q ≤ Ω) :
    0 ≤ resourceCoefficient γ Q Ω ∧ resourceCoefficient γ Q Ω ≤ γ := by
  have hr : (Q : ℝ) / (Ω : ℝ) ≤ 1 := by
    by_cases hΩ : Ω = 0
    · simp [hΩ]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hΩ)).2
      exact_mod_cast hQ
  constructor
  · unfold resourceCoefficient
    positivity
  · exact (mul_le_mul_of_nonneg_left hr hγ).trans_eq (mul_one γ)

/-- Affinity holds for the generator, with no assertion about semigroups. -/
theorem growth_generator_interpolation (γ r : ℝ) (m : ℕ)
    (f : Point → ℝ) (x : Point) :
    growthGenerator (r*γ) m f x =
      (1-r)*growthGenerator 0 m f x+r*growthGenerator γ m f x := by
  unfold growthGenerator
  ring

/-- The inherited source inequality already covers every instantaneous bath state. -/
theorem low_resource_local_affine (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2)
    (he : lowEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator (resourceCoefficient γ Q Ω)
      (fun d => lowExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*
        lowExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1)+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ Q Ω hγ hQ
  exact low_growth_local_affine z _ hz hs hb (hbmax.trans hγmax) N hN hlarge c hNm he

theorem high_resource_local_affine (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2)
    (he : highEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator (resourceCoefficient γ Q Ω)
      (fun d => highExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*
        highExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1)+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ Q Ω hγ hQ
  exact high_growth_local_affine z _ hz hs hb (hbmax.trans hγmax) N hN hlarge c hNm he

end ResourceLimitedCompetition
