import proofs.OverlappingSiphonInvasion.NormalizedIdentities
import proofs.OverlappingSiphonInvasion.ResidentInvasion

noncomputable section
namespace OverlappingSiphonInvasion

def normalGrowth (p : Rates) (ru rv rj : ℝ) (k : ℕ) (z : LiftState) : ℝ :=
  normalHU p ru z.1 (z.2 0)+normalHV p rv z.1 (z.2 1)+
    (k:ℝ)*normalHJ p rj z.1 (z.2 2) (z.2 3)

private theorem convex_lower (a b d θ : ℝ) (ha : d ≤ a) (hb : d ≤ b)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : d ≤ a*θ+b*(1-θ) := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hθ,
    mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hθ1)]

private theorem simplex_lower (a b c d ξ ζ : ℝ) (ha : d ≤ a) (hb : d ≤ b)
    (hc : d ≤ c) (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) (hs : ξ+ζ ≤ 1) :
    d ≤ a*ξ+b*ζ+c*(1-ξ-ζ) := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hξ,
    mul_nonneg (sub_nonneg.mpr hb) hζ,
    mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ 1-ξ-ζ by linarith)]

/-- At the first resident equilibrium the two nonmissing factors have zero
relative growth throughout the physical fiber. -/
theorem resident1_fiber_nonmissing (p : Rates) (ru rv rj R s u : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hu : 0 < u)
    (he : p.alpha1*s = p.mu1) (z : LiftState)
    (hz : z ∈ physicalLiftClosure ru rv rj R) (hx : z.1 = face1 s u) :
    normalHU p ru z.1 (z.2 0) = 0 ∧ normalHJ p rj z.1 (z.2 2) (z.2 3) = 0 := by
  obtain ⟨hU,_,hJ⟩ := closure_mass_identities p ru rv rj R hru hrv hrj z hz
  rw [hx] at hU hJ ⊢
  simp [massU,massJ,field,face1,he] at hU hJ
  exact ⟨hU.resolve_right hu.ne',hJ.resolve_right hu.ne'⟩

theorem resident2_fiber_nonmissing (p : Rates) (ru rv rj R s u : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hu : 0 < u)
    (he : p.alpha2*s = p.mu2) (z : LiftState)
    (hz : z ∈ physicalLiftClosure ru rv rj R) (hx : z.1 = face2 s u) :
    normalHV p rv z.1 (z.2 1) = 0 ∧ normalHJ p rj z.1 (z.2 2) (z.2 3) = 0 := by
  obtain ⟨_,hV,hJ⟩ := closure_mass_identities p ru rv rj R hru hrv hrj z hz
  rw [hx] at hV hJ ⊢
  simp [massV,massJ,field,face2,he] at hV hJ
  exact ⟨hV.resolve_right hu.ne',hJ.resolve_right hu.ne'⟩

theorem resident1_fiber_growth (p : Rates) (ru rv rj R s u δ : ℝ) (k : ℕ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hu : 0 < u)
    (he : p.alpha1*s = p.mu1)
    (h1 : δ ≤ p.alpha2*s-p.gamma2*u-p.mu2+rv*((p.gamma1+p.gamma2)*u))
    (h2 : δ*rv ≤ p.beta2*s+rv*(p.eta1*u+p.alpha3*s-p.mu3))
    (z : LiftState) (hz : z ∈ physicalLiftClosure ru rv rj R)
    (hx : z.1 = face1 s u) : δ ≤ normalGrowth p ru rv rj k z := by
  obtain ⟨hU,hJ⟩ := resident1_fiber_nonmissing p ru rv rj R s u hru hrv hrj hu he z hz hx
  have hd := (closure_direction_bounds ru rv rj R hru hrv hrj z hz).1 1
  simp only [normalGrowth,hU,hJ,mul_zero,zero_add,add_zero]
  rw [hx]
  apply convex_lower _ _ δ _ ?_ ?_ hd.1 hd.2
  · simpa [privateB,face1,mul_assoc] using h1
  · apply (le_div_iff₀ hrv).mpr
    simpa [sharedC,face1] using h2

theorem resident2_fiber_growth (p : Rates) (ru rv rj R s u δ : ℝ) (k : ℕ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hu : 0 < u)
    (he : p.alpha2*s = p.mu2)
    (h1 : δ ≤ p.alpha1*s-p.gamma1*u-p.mu1+ru*((p.gamma1+p.gamma2)*u))
    (h2 : δ*ru ≤ p.beta1*s+ru*(p.eta2*u+p.alpha3*s-p.mu3))
    (z : LiftState) (hz : z ∈ physicalLiftClosure ru rv rj R)
    (hx : z.1 = face2 s u) : δ ≤ normalGrowth p ru rv rj k z := by
  obtain ⟨hV,hJ⟩ := resident2_fiber_nonmissing p ru rv rj R s u hru hrv hrj hu he z hz hx
  have hd := (closure_direction_bounds ru rv rj R hru hrv hrj z hz).1 0
  simp only [normalGrowth,hV,hJ,mul_zero,add_zero]
  rw [hx]
  apply convex_lower _ _ δ _ ?_ ?_ hd.1 hd.2
  · simpa [privateA,face2,mul_assoc] using h1
  · apply (le_div_iff₀ hru).mpr
    simpa [sharedC,face2] using h2

/-- The disease-free compensating factor grows in every physical limiting
direction; no direction convergence or irreducibility is required. -/
theorem diseaseFree_fiber_J_lower (p : Rates) (ru rv rj R s δ : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj)
    (ha : δ ≤ p.alpha1*s-p.mu1) (hb : δ ≤ p.alpha2*s-p.mu2)
    (hc : δ*rj ≤ (p.beta1+p.beta2)*s+rj*(p.alpha3*s-p.mu3))
    (z : LiftState) (hz : z ∈ physicalLiftClosure ru rv rj R)
    (hx : z.1 = face1 s 0) : δ ≤ normalHJ p rj z.1 (z.2 2) (z.2 3) := by
  have hd := closure_direction_bounds ru rv rj R hru hrv hrj z hz
  rw [hx]
  apply simplex_lower _ _ _ δ _ _ ?_ ?_ ?_ (hd.1 2).1 (hd.1 3).1 hd.2
  · simpa [privateA,face1] using ha
  · simpa [privateB,face1] using hb
  · apply (le_div_iff₀ hrj).mpr
    simpa [sharedC,face1] using hc

end OverlappingSiphonInvasion
