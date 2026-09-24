import proofs.CoreCouplingGlobal.RoutedCoupling

namespace CoreCouplingGlobal
open CoreCouplingCAC Set
noncomputable def routedDen (g z : ℝ) := 3-g+g*z
noncomputable def routedK (z : ℝ) := (20004*z^2-159984*z)/20001
noncomputable def routedNumerA (g z : ℝ) := 60*z*g+routedK z*routedDen g z
noncomputable def routedPoly (e g z : ℝ) :=
  27*g^2*(routedDen g z)^2-(2+e-g+g*z)*60*g^2*routedDen g z+
    routedNumerA g z*g*routedDen g z+e*(routedNumerA g z)^2
noncomputable def routedLift (g z : ℝ) : State :=
  ⟨routedNumerA g z/(g*routedDen g z),60/routedDen g z,z,
    (16*z+2*z^2)/(20001/10000)⟩

theorem routed_lift_stationary (e g z : ℝ) (hg : g ≠ 0)
    (hd : routedDen g z ≠ 0) (hp : routedPoly e g z = 0) :
    RoutedStationary e g (routedLift g z) := by
  have hb : fB (flagshipRates e) (routedLift g z).A (routedLift g z).B
      (1-g+g*(routedLift g z).z) = routedPoly e g z/(g^2*(routedDen g z)^2) := by
    dsimp [fB,flagshipRates,routedLift,routedPoly]
    field_simp [hg,hd]
    ring
  have ha : fA (flagshipRates e) (routedLift g z).A (routedLift g z).B
      (1-g+g*(routedLift g z).z) +
      2*fB (flagshipRates e) (routedLift g z).A (routedLift g z).B
      (1-g+g*(routedLift g z).z) = 0 := by
    dsimp [fA,fB,flagshipRates,routedLift]
    field_simp [hg,hd]
    dsimp [routedDen]
    ring
  rw [hp,zero_div] at hb
  refine ⟨by linarith,hb,?_,?_⟩
  · dsimp [routedZ,routedLift]
    field_simp [hg,hd]
    dsimp [routedNumerA,routedDen,routedK]
    ring
  · dsimp [fH,flagshipRates,routedLift]
    ring

theorem routed_lift_positive (g z : ℝ) (hg : (999/1000:ℝ) ≤ g) (hg1 : g ≤ 1)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) : (routedLift g z).Positive := by
  have hgp : 0 < g := by linarith
  have hzp : 0 < z := by linarith [hz.1]
  have hd : 0 < routedDen g z := by
    dsimp [routedDen]
    nlinarith [mul_pos hgp hzp]
  have hdu : routedDen g z ≤ 61/10 := by
    have hgz := mul_le_mul_of_nonneg_right hg1 hzp.le
    dsimp [routedDen]
    nlinarith [hz.2]
  have hB : (9:ℝ) < 60/routedDen g z := by
    apply (lt_div_iff₀ hd).2
    linarith
  have hgb : 8 < g*(60/routedDen g z) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hg) (sub_nonneg.mpr hB.le)]
  have hk : -8*z ≤ routedK z := by
    dsimp [routedK]
    nlinarith [sq_nonneg z]
  have hA : 0 < z*(60/routedDen g z)+routedK z/g := by
    apply (mul_pos_iff_of_pos_right hgp).1
    have hc : (z*(60/routedDen g z)+routedK z/g)*g =
        z*(g*(60/routedDen g z))+routedK z := by
      field_simp
    rw [hc]
    nlinarith [mul_pos hzp (sub_pos.mpr hgb)]
  have hid : (routedLift g z).A = z*(60/routedDen g z)+routedK z/g := by
    dsimp [routedLift,routedNumerA]
    field_simp
  refine ⟨hid.symm ▸ hA,by dsimp [routedLift]; positivity,hzp,?_⟩
  dsimp [routedLift]
  positivity

theorem routed_poly_affine (e g z : ℝ) :
    routedPoly e g z = (1-50000*e)*routedPoly 0 g z+
      (50000*e)*routedPoly (1/50000) g z := by
  dsimp [routedPoly]
  ring

theorem positive_quartic_bernstein (t a b c d e : ℝ)
    (ht : 0 ≤ t) (htu : t ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    0 < a*(1-t)^4+4*b*t*(1-t)^3+6*c*t^2*(1-t)^2+4*d*t^3*(1-t)+e*t^4 := by
  have h1 : 0 ≤ 1-t := by linarith
  by_cases hzero : t = 0
  · subst t
    simpa using ha
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    positivity
theorem routed_positive_affine_mix (t a b : ℝ) (ht : 0 ≤ t) (htu : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < (1-t)*a+t*b := by
  have h1 : 0 ≤ 1-t := by linarith
  by_cases h0 : t = 0
  · subst t
    simpa using ha
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
    positivity
end CoreCouplingGlobal
