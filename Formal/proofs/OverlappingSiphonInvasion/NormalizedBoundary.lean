import proofs.OverlappingSiphonInvasion.NormalizedMassDynamics
import proofs.OverlappingSiphonInvasion.BoundaryProjection

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

private theorem two_mass_zero (a c r : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hr : 0 < r) (hz : a+r*c = 0) : a = 0 ∧ c = 0 := by
  have hp := mul_nonneg hr.le hc
  have he : r*c = 0 := by linarith
  have hc0 := (mul_eq_zero.mp he).resolve_left hr.ne'
  exact ⟨by rw [hc0] at hz; simpa using hz,hc0⟩

theorem extinctionProduct_zero_mass (ru rv rj : ℝ) (k : ℕ) (hrj : 0 < rj)
    (z : LiftState) (hx : ∀ i, 0 ≤ z.1 i) (hP : extinctionProduct ru rv rj k z = 0) :
    massU ru z.1 = 0 ∨ massV rv z.1 = 0 := by
  rcases mul_eq_zero.mp hP with hUV | hJ
  · exact mul_eq_zero.mp hUV
  · have hj : massJ rj z.1 = 0 := by
      by_contra hn
      exact pow_ne_zero k hn hJ
    have ha := hx 1
    have hb := hx 2
    have hc := hx 3
    obtain ⟨hab,hc0⟩ := two_mass_zero (z.1 1+z.1 2) (z.1 3) rj (add_nonneg ha hb) hc hrj hj
    have ha0 : z.1 1 = 0 := by linarith
    exact Or.inl (by simp [massU,ha0,hc0])

/-- Every extinction trajectory of the normalized source projects to one of
the three source equilibria. This includes initially zero susceptible density. -/
theorem normalized_boundary_projection_converges (p : Rates) (hp : PositiveRates p)
    (ru rv rj R : ℝ) (k : ℕ) (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hR : 0 ≤ R)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0)
    (X : ℝ → LiftState)
    (hX : ∀ t, 0 ≤ t → X t ∈ physicalLiftClosure ru rv rj R)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (normalizedField p ru rv rj (X t)) t)
    (hP : extinctionProduct ru rv rj k (X 0) = 0) :
    Tendsto (fun t => (X t).1) atTop (𝓝 (face1 (p.recruitment/p.mu0) 0)) ∨
    Tendsto (fun t => (X t).1) atTop (𝓝 (face1 (p.mu1/p.alpha1)
      ((p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1))) ∨
    Tendsto (fun t => (X t).1) atTop (𝓝 (face2 (p.mu2/p.alpha2)
      ((p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2))) := by
  have hbox : ∀ t, 0 ≤ t → (X t).1 ∈ populationBox R :=
    fun t ht => physicalLiftClosure_projection ru rv rj R (X t) (hX t ht)
  have hds : ∀ t, 0 ≤ t → HasDerivAt (fun s => (X s).1) (field p (X t).1) t :=
    fun t ht => (hd t ht).fst
  have hUcoords (h0 : massU ru (X 0).1 = 0) :
      ∀ t, 0 ≤ t → (X t).1 1 = 0 ∧ (X t).1 3 = 0 := by
    intro t ht
    exact two_mass_zero _ _ _ ((hbox t ht).1 1) ((hbox t ht).1 3) hru
      (normalized_massU_zero p ru rv rj R hru hrv hrj X hX hd h0 t ht)
  have hVcoords (h0 : massV rv (X 0).1 = 0) :
      ∀ t, 0 ≤ t → (X t).1 2 = 0 ∧ (X t).1 3 = 0 := by
    intro t ht
    exact two_mass_zero _ _ _ ((hbox t ht).1 2) ((hbox t ht).1 3) hrv
      (normalized_massV_zero p ru rv rj R hru hrv hrj X hX hd h0 t ht)
  have hdf (hU : massU ru (X 0).1 = 0) (hV : massV rv (X 0).1 = 0) :
      Tendsto (fun t => (X t).1) atTop (𝓝 (face1 (p.recruitment/p.mu0) 0)) := by
    apply bounded_diseaseFree_converges p hp _ hds
    intro t ht
    obtain ⟨ha,hc⟩ := hUcoords hU t ht
    have hb := (hVcoords hV t ht).1
    ext i
    fin_cases i <;> simp [face1,ha,hb,hc]
  rcases extinctionProduct_zero_mass ru rv rj k hrj (X 0) (hbox 0 le_rfl).1 hP with hU | hV
  · by_cases hb : (X 0).1 2 = 0
    · have hc := (hUcoords hU 0 le_rfl).2
      exact Or.inl (hdf hU (by simp [massV,hb,hc]))
    · right; right
      apply bounded_face2_converges p hp R hR he2 _ hbox hds ?_
        (lt_of_le_of_ne ((hbox 0 le_rfl).1 2) (Ne.symm hb))
      intro t ht
      obtain ⟨ha,hc⟩ := hUcoords hU t ht
      ext i
      fin_cases i <;> simp [face2,ha,hc]
  · by_cases ha : (X 0).1 1 = 0
    · have hc := (hVcoords hV 0 le_rfl).2
      exact Or.inl (hdf (by simp [massU,ha,hc]) hV)
    · right; left
      apply bounded_face1_converges p hp R hR he1 _ hbox hds ?_
        (lt_of_le_of_ne ((hbox 0 le_rfl).1 1) (Ne.symm ha))
      intro t ht
      obtain ⟨hb,hc⟩ := hVcoords hV t ht
      ext i
      fin_cases i <;> simp [face1,hb,hc]

end OverlappingSiphonInvasion
