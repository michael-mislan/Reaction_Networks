import proofs.OverlappingSiphonInvasion.GeneralFlow

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

theorem populationBox_coordinate_le (R : ℝ) (x : State) (hx : x ∈ populationBox R)
    (i : Fin 4) : x i ≤ R := by
  have h0 := hx.1 0
  have h1 := hx.1 1
  have h2 := hx.1 2
  have h3 := hx.1 3
  have hN := hx.2
  dsimp [total] at hN
  fin_cases i <;> dsimp <;> linarith

theorem source_susceptible_lower (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (x : State) (hx : x ∈ populationBox R) :
    p.recruitment-coordinateLoss p R 0*x 0 ≤ field p x 0 := by
  have h1 := (hp 1).le
  have h2 := (hp 2).le
  have h3 := (hp 3).le
  have h8 := (hp 8).le
  have h9 := (hp 9).le
  simp [rateVector] at h1 h2 h3 h8 h9
  have h0 := hx.1 0
  have r1 := sub_nonneg.mpr (populationBox_coordinate_le R x hx 1)
  have r2 := sub_nonneg.mpr (populationBox_coordinate_le R x hx 2)
  have r3 := sub_nonneg.mpr (populationBox_coordinate_le R x hx 3)
  have hh : 0 ≤ x 0*(p.alpha1*(R-x 1)+p.alpha2*(R-x 2)+
      (p.alpha3+p.beta1+p.beta2)*(R-x 3)) := by positivity
  dsimp [field,coordinateLoss]
  nlinarith only [hh]

/-- Recruitment gives an eventual positive susceptible floor even on a
boundary trajectory whose susceptible coordinate was initially zero. -/
theorem bounded_source_eventual_susceptible_floor (p : Rates) (hp : PositiveRates p)
    (R : ℝ) (hR : 0 ≤ R) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → X t ∈ populationBox R)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t) :
    ∃ l : ℝ, 0 < l ∧ ∀ᶠ t in atTop, l < X t 0 := by
  have hΛ : 0 < p.recruitment := by simpa [rateVector] using hp 0
  have hμ : 0 < p.mu0 := by simpa [rateVector] using hp 10
  have h1 : 0 < p.alpha1 := by simpa [rateVector] using hp 1
  have h2 : 0 < p.alpha2 := by simpa [rateVector] using hp 2
  have h3 : 0 < p.alpha3 := by simpa [rateVector] using hp 3
  have h8 : 0 < p.beta1 := by simpa [rateVector] using hp 8
  have h9 : 0 < p.beta2 := by simpa [rateVector] using hp 9
  let q := coordinateLoss p R 0
  have hq : 0 < q := by dsimp [q,coordinateLoss]; positivity
  let l := (p.recruitment/q)/2
  have hl : 0 < l := by dsimp [l]; positivity
  have hh := CoreCouplingGlobal.eventual_upper_of_linear_drift
    (fun t => -X t 0) (fun t => -field p (X t) 0) 0 (-p.recruitment) q (-l) hq
    (by dsimp [l]; rw [neg_div]; linarith [div_pos hΛ hq])
    (fun t ht => (hasDerivAt_pi.1 (hd t ht) 0).neg)
    (by
      intro t ht
      have hb := source_susceptible_lower p hp R (X t) (hX t ht)
      dsimp [q]
      linarith)
  refine ⟨l,hl,?_⟩
  filter_upwards [hh] with t ht
  linarith

theorem bounded_source_coordinate_positive (p : Rates) (hp : PositiveRates p)
    (R : ℝ) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → X t ∈ populationBox R)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t)
    (i : Fin 4) (hi : 0 < X 0 i) (t : ℝ) (ht : 0 ≤ t) : 0 < X t i := by
  exact CoreCouplingGlobal.positive_of_linear_lower
    (fun s => X s i) (fun s => field p (X s) i) (lossBound p R)
    (fun s hs => hasDerivAt_pi.1 (hd s hs) i) hi
    (fun s hs => field_linear_lower p hp R (X s) (hX s hs).1
      (populationBox_coordinate_le R (X s) (hX s hs)) i) t ht

end OverlappingSiphonInvasion
