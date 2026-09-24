import proofs.OverlappingSiphonInvasion.NormalizedGrowth

noncomputable section
namespace OverlappingSiphonInvasion

private theorem direction_min (a b θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min a b ≤ a*θ+b*(1-θ) := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr (min_le_left a b)) hθ,
    mul_nonneg (sub_nonneg.mpr (min_le_right a b)) (sub_nonneg.mpr hθ1)]

/-- Strict mutual invasion supplies one weighted product with positive
logarithmic growth at every physical lifted boundary equilibrium. The exponent
is chosen from explicit disease-free directional bounds. -/
theorem boundary_growth_weights (p : Rates) (s0 s1 u1 s2 u2 : ℝ)
    (hu1 : 0 < u1) (hu2 : 0 < u2)
    (he1 : p.alpha1*s1 = p.mu1) (he2 : p.alpha2*s2 = p.mu2)
    (hB1 : 0 < p.beta2*s1) (hC1 : 0 < (p.gamma1+p.gamma2)*u1)
    (hi1 : 0 ≤ p.alpha2*s1-p.gamma2*u1-p.mu2 ∨
      0 ≤ p.eta1*u1+p.alpha3*s1-p.mu3 ∨
      (p.alpha2*s1-p.gamma2*u1-p.mu2)*(p.eta1*u1+p.alpha3*s1-p.mu3) <
        (p.beta2*s1)*((p.gamma1+p.gamma2)*u1))
    (hB2 : 0 < p.beta1*s2) (hC2 : 0 < (p.gamma1+p.gamma2)*u2)
    (hi2 : 0 ≤ p.alpha1*s2-p.gamma1*u2-p.mu1 ∨
      0 ≤ p.eta2*u2+p.alpha3*s2-p.mu3 ∨
      (p.alpha1*s2-p.gamma1*u2-p.mu1)*(p.eta2*u2+p.alpha3*s2-p.mu3) <
        (p.beta1*s2)*((p.gamma1+p.gamma2)*u2))
    (ha : 0 < p.alpha1*s0-p.mu1) (hb : 0 < p.alpha2*s0-p.mu2)
    (hk : 0 < (p.beta1+p.beta2)*s0) :
    ∃ ru rv rj : ℝ, ∃ k : ℕ, 0 < ru ∧ 0 < rv ∧ 0 < rj ∧ 0 < k ∧
      ∀ R z, z ∈ physicalLiftClosure ru rv rj R →
        (z.1 = face1 s0 0 ∨ z.1 = face1 s1 u1 ∨ z.1 = face2 s2 u2) →
          0 < normalGrowth p ru rv rj k z := by
  obtain ⟨rv,dv,hrv,hdv,hv1,hv2⟩ := positive_covector_margin _ _ _ _ hB1 hC1 hi1
  obtain ⟨ru,du,hru,hdu,hu1',hu2'⟩ := positive_covector_margin _ _ _ _ hB2 hC2 hi2
  obtain ⟨rj,hrj,_,hj⟩ :=
    (positive_covector_iff 1 ((p.beta1+p.beta2)*s0) 1 (p.alpha3*s0-p.mu3)
      hk (by norm_num)).mpr (Or.inl (by norm_num))
  let A := p.alpha1*s0-p.mu1
  let B := p.alpha2*s0-p.mu2
  let D := p.alpha3*s0-p.mu3
  let C := ((p.beta1+p.beta2)*s0+rj*D)/rj
  let δ := min A (min B C)
  have hδ : 0 < δ := lt_min ha (lt_min hb (div_pos hj hrj))
  have hδa : δ ≤ A := min_le_left _ _
  have hδb : δ ≤ B := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ*rj ≤ (p.beta1+p.beta2)*s0+rj*D :=
    (le_div_iff₀ hrj).mp ((min_le_right A (min B C)).trans (min_le_right B C))
  let L := min A ((p.beta1*s0+ru*D)/ru)+min B ((p.beta2*s0+rv*D)/rv)
  obtain ⟨k,hk'⟩ := exists_nat_gt (max 1 ((1-L)/δ))
  have hk0 : 0 < k := by
    have hh : (0:ℝ) < k := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hk')
    exact_mod_cast hh
  have hkδ : 1-L < (k:ℝ)*δ := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hk')
  refine ⟨ru,rv,rj,k,hru,hrv,hrj,hk0,?_⟩
  intro R z hz hx
  rcases hx with hx | hx | hx
  · have hd := (closure_direction_bounds ru rv rj R hru hrv hrj z hz).1
    have hU : min A ((p.beta1*s0+ru*D)/ru) ≤ normalHU p ru z.1 (z.2 0) := by
      rw [hx]
      simpa [normalHU,privateA,sharedC,face1,A,D] using
        direction_min A ((p.beta1*s0+ru*D)/ru) (z.2 0) (hd 0).1 (hd 0).2
    have hV : min B ((p.beta2*s0+rv*D)/rv) ≤ normalHV p rv z.1 (z.2 1) := by
      rw [hx]
      simpa [normalHV,privateB,sharedC,face1,B,D] using
        direction_min B ((p.beta2*s0+rv*D)/rv) (z.2 1) (hd 1).1 (hd 1).2
    have hJ := diseaseFree_fiber_J_lower p ru rv rj R s0 δ hru hrv hrj hδa hδb hδc z hz hx
    have hm := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    dsimp [normalGrowth]
    dsimp [L] at hkδ
    linarith
  · have hh := resident1_fiber_growth p ru rv rj R s1 u1 (2*dv) k hru hrv hrj
      hu1 he1 hv1 hv2 z hz hx
    exact (by positivity : (0:ℝ) < 2*dv).trans_le hh
  · have hh := resident2_fiber_growth p ru rv rj R s2 u2 (2*du) k hru hrv hrj
      hu2 he2 hu1' hu2' z hz hx
    exact (by positivity : (0:ℝ) < 2*du).trans_le hh

end OverlappingSiphonInvasion
