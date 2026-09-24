import proofs.OverlappingSiphonInvasion.BoundaryBounds
import proofs.OverlappingSiphonInvasion.SourceResidentDynamics

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

theorem bounded_face1_converges (p : Rates) (hp : PositiveRates p) (R : ℝ) (hR : 0 ≤ R)
    (he : p.mu1/p.alpha1 < p.recruitment/p.mu0) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → X t ∈ populationBox R)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t)
    (hf : ∀ t, 0 ≤ t → X t = face1 (X t 0) (X t 1)) (hu : 0 < X 0 1) :
    Tendsto X atTop (𝓝 (face1 (p.mu1/p.alpha1)
      ((p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1))) := by
  obtain ⟨l,hl,hsl⟩ := bounded_source_eventual_susceptible_floor p hp R hR X hX hd
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hsl.and (eventually_ge_atTop (0:ℝ)))
  have hT0 := (hT T le_rfl).2
  have hpos : ∀ t, 0 ≤ t → 0 < X (t+T) 0 ∧ 0 < X (t+T) 1 := by
    intro t ht
    exact ⟨hl.trans (hT (t+T) (by linarith)).1,
      bounded_source_coordinate_positive p hp R X hX hd 1 hu (t+T) (by linarith)⟩
  have hdc : ∀ i t, 0 ≤ t → HasDerivAt (fun τ => X (τ+T) i)
      (source.massAction (rateVector p) (face1 (X (t+T) 0) (X (t+T) 1)) i) t := by
    intro i t ht
    have h := (hasDerivAt_pi.1 (hd (t+T) (by linarith)) i).comp t ((hasDerivAt_id t).add_const T)
    simp only [mul_one] at h
    rw [source_field,← hf (t+T) (by linarith)]
    exact h
  obtain ⟨hs,hu'⟩ := source_resident1_converges p hp he
    (fun t => X (t+T) 0) (fun t => X (t+T) 1) hpos (hdc 0) (hdc 1)
  have hshift : Tendsto (fun t : ℝ => t-T) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
  have hs' : Tendsto (fun t => X t 0) atTop (𝓝 (p.mu1/p.alpha1)) := by
    simpa [Function.comp_def] using hs.comp hshift
  have hu'' : Tendsto (fun t => X t 1) atTop
      (𝓝 ((p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1)) := by
    simpa [Function.comp_def] using hu'.comp hshift
  have hfconv : Tendsto (fun t => face1 (X t 0) (X t 1)) atTop
      (𝓝 (face1 (p.mu1/p.alpha1) ((p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1))) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · exact hs'
    · exact hu''
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  apply hfconv.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (hf t ht).symm

theorem bounded_face2_converges (p : Rates) (hp : PositiveRates p) (R : ℝ) (hR : 0 ≤ R)
    (he : p.mu2/p.alpha2 < p.recruitment/p.mu0) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → X t ∈ populationBox R)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t)
    (hf : ∀ t, 0 ≤ t → X t = face2 (X t 0) (X t 2)) (hu : 0 < X 0 2) :
    Tendsto X atTop (𝓝 (face2 (p.mu2/p.alpha2)
      ((p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2))) := by
  obtain ⟨l,hl,hsl⟩ := bounded_source_eventual_susceptible_floor p hp R hR X hX hd
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hsl.and (eventually_ge_atTop (0:ℝ)))
  have hT0 := (hT T le_rfl).2
  have hpos : ∀ t, 0 ≤ t → 0 < X (t+T) 0 ∧ 0 < X (t+T) 2 := by
    intro t ht
    exact ⟨hl.trans (hT (t+T) (by linarith)).1,
      bounded_source_coordinate_positive p hp R X hX hd 2 hu (t+T) (by linarith)⟩
  have hdc : ∀ i t, 0 ≤ t → HasDerivAt (fun τ => X (τ+T) i)
      (source.massAction (rateVector p) (face2 (X (t+T) 0) (X (t+T) 2)) i) t := by
    intro i t ht
    have h := (hasDerivAt_pi.1 (hd (t+T) (by linarith)) i).comp t ((hasDerivAt_id t).add_const T)
    simp only [mul_one] at h
    rw [source_field,← hf (t+T) (by linarith)]
    exact h
  obtain ⟨hs,hu'⟩ := source_resident2_converges p hp he
    (fun t => X (t+T) 0) (fun t => X (t+T) 2) hpos (hdc 0) (hdc 2)
  have hshift : Tendsto (fun t : ℝ => t-T) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
  have hs' : Tendsto (fun t => X t 0) atTop (𝓝 (p.mu2/p.alpha2)) := by
    simpa [Function.comp_def] using hs.comp hshift
  have hu'' : Tendsto (fun t => X t 2) atTop
      (𝓝 ((p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2)) := by
    simpa [Function.comp_def] using hu'.comp hshift
  have hfconv : Tendsto (fun t => face2 (X t 0) (X t 2)) atTop
      (𝓝 (face2 (p.mu2/p.alpha2) ((p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2))) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · exact hs'
    · exact tendsto_const_nhds
    · exact hu''
    · exact tendsto_const_nhds
  apply hfconv.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (hf t ht).symm

theorem bounded_diseaseFree_converges (p : Rates) (hp : PositiveRates p) (X : ℝ → State)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t)
    (hf : ∀ t, 0 ≤ t → X t = face1 (X t 0) 0) :
    Tendsto X atTop (𝓝 (face1 (p.recruitment/p.mu0) 0)) := by
  have hs := source_diseaseFree_converges p hp (fun t => X t 0) (by
    intro t ht
    rw [source_field,← hf t ht]
    exact hasDerivAt_pi.1 (hd t ht) 0)
  have hc : Tendsto (fun t => face1 (X t 0) 0) atTop (𝓝 (face1 (p.recruitment/p.mu0) 0)) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · exact hs
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  apply hc.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (hf t ht).symm

end OverlappingSiphonInvasion
