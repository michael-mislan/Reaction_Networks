import proofs.OverlappingSiphonInvasion.TrajectoryBounds

noncomputable section
namespace OverlappingSiphonInvasion

def deathFloor (p : Rates) : ℝ := min p.mu0 (min p.mu1 (min p.mu2 p.mu3))

theorem deathFloor_pos (p : Rates) (hp : PositiveRates p) : 0 < deathFloor p := by
  have h0 := hp 10
  have h1 := hp 11
  have h2 := hp 12
  have h3 := hp 13
  simp [rateVector] at h0 h1 h2 h3
  exact lt_min h0 (lt_min h1 (lt_min h2 h3))

def coordinateLoss (p : Rates) (R : ℝ) : State :=
  ![p.mu0+(p.alpha1+p.alpha2+p.alpha3+p.beta1+p.beta2)*R,
    p.mu1+(p.gamma1+p.eta1)*R, p.mu2+(p.gamma2+p.eta2)*R,p.mu3]

def lossBound (p : Rates) (R : ℝ) : ℝ :=
  max (coordinateLoss p R 0) (max (coordinateLoss p R 1)
    (max (coordinateLoss p R 2) (coordinateLoss p R 3)))

theorem field_coordinate_loss_nonneg (p : Rates) (hp : PositiveRates p)
    (R : ℝ) (x : State) (hx : ∀ i, 0 ≤ x i) (hu : ∀ i, x i ≤ R) (i : Fin 4) :
    0 ≤ field p x i+coordinateLoss p R i*x i := by
  have h0 := (hp 0).le
  have h1 := (hp 1).le
  have h2 := (hp 2).le
  have h3 := (hp 3).le
  have h4 := (hp 4).le
  have h5 := (hp 5).le
  have h6 := (hp 6).le
  have h7 := (hp 7).le
  have h8 := (hp 8).le
  have h9 := (hp 9).le
  simp [rateVector] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have x0 := hx 0
  have x1 := hx 1
  have x2 := hx 2
  have x3 := hx 3
  have r1 := sub_nonneg.mpr (hu 1)
  have r2 := sub_nonneg.mpr (hu 2)
  have r3 := sub_nonneg.mpr (hu 3)
  fin_cases i
  · simp [field,coordinateLoss]
    have hc : 0 ≤ p.recruitment+x 0*(p.alpha1*(R-x 1)+p.alpha2*(R-x 2)+
        (p.alpha3+p.beta1+p.beta2)*(R-x 3)) := by positivity
    convert hc using 1
    ring
  · simp [field,coordinateLoss]
    have hc : 0 ≤ p.alpha1*x 0*x 1+p.beta1*x 0*x 3+
        p.gamma1*x 1*(R-x 2)+p.eta1*x 1*(R-x 3) := by positivity
    convert hc using 1
    ring
  · simp [field,coordinateLoss]
    have hc : 0 ≤ p.alpha2*x 0*x 2+p.beta2*x 0*x 3+
        p.gamma2*x 2*(R-x 1)+p.eta2*x 2*(R-x 3) := by positivity
    convert hc using 1
    ring
  · simp [field,coordinateLoss]
    have hc : 0 ≤ (p.gamma1+p.gamma2)*x 1*x 2+
        x 3*(p.eta1*x 1+p.eta2*x 2+p.alpha3*x 0) := by positivity
    convert hc using 1
    ring

theorem field_linear_lower (p : Rates) (hp : PositiveRates p) (R : ℝ) (x : State)
    (hx : ∀ i, 0 ≤ x i) (hu : ∀ i, x i ≤ R) (i : Fin 4) :
    -(lossBound p R)*x i ≤ field p x i := by
  have hi : coordinateLoss p R i ≤ lossBound p R := by
    dsimp [lossBound]
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hm := mul_le_mul_of_nonneg_right hi (hx i)
  have hh := field_coordinate_loss_nonneg p hp R x hx hu i
  linarith only [hm,hh]

theorem field_boundary_nonneg (p : Rates) (hp : PositiveRates p) (x : State)
    (hx : ∀ i, 0 ≤ x i) (i : Fin 4) (hi : x i = 0) : 0 ≤ field p x i := by
  let R := max (x 0) (max (x 1) (max (x 2) (x 3)))
  have hu : ∀ i, x i ≤ R := by
    intro j
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  simpa only [hi,mul_zero] using field_linear_lower p hp R x hx hu i

theorem total_mortality_bound (p : Rates) (x : State) (hx : ∀ i, 0 ≤ x i) :
    p.recruitment-p.mu0*x 0-p.mu1*x 1-p.mu2*x 2-p.mu3*x 3 ≤
      p.recruitment-deathFloor p*total x := by
  have h0 : deathFloor p ≤ p.mu0 := min_le_left _ _
  have h1 : deathFloor p ≤ p.mu1 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : deathFloor p ≤ p.mu2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : deathFloor p ≤ p.mu3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have m0 := mul_le_mul_of_nonneg_right h0 (hx 0)
  have m1 := mul_le_mul_of_nonneg_right h1 (hx 1)
  have m2 := mul_le_mul_of_nonneg_right h2 (hx 2)
  have m3 := mul_le_mul_of_nonneg_right h3 (hx 3)
  dsimp [total]
  linarith only [m0,m1,m2,m3]

end OverlappingSiphonInvasion
