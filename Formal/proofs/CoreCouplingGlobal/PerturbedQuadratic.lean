import proofs.CoreCouplingGlobal.TrajectoryPairEnergy

namespace CoreCouplingGlobal
open Set

theorem saddlePairing_self_nonneg (x : SaddleVector) : 0 ≤ saddlePairing x x := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

theorem saddlePairing_self_norm_lower (x : SaddleVector) : ‖x‖^2 ≤ saddlePairing x x := by
  calc
    ‖x‖^2 ≤ (x 0)^2+(x 1)^2+(x 2)^2+(x 3)^2 := saddle_vector_norm_sq_le x
    _ = saddlePairing x x := by simp [saddlePairing,Fin.sum_univ_succ]; ring

noncomputable def perturbedGradient (G : SaddleVector →L[ℝ] SaddleVector) (α : ℝ) :
    SaddleVector →L[ℝ] SaddleVector := G+α • ContinuousLinearMap.id ℝ SaddleVector

theorem perturbedGradient_pairing (G : SaddleVector →L[ℝ] SaddleVector) (α : ℝ)
    (x v : SaddleVector) :
    saddlePairing (perturbedGradient G α x) v = saddlePairing (G x) v+α*saddlePairing x v := by
  simp [perturbedGradient,saddlePairing,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

/-- A whole interval of nonnegative gradient perturbations preserves strict
linear dissipation. This permits an independent choice of a negative direction. -/
theorem positive_gradient_perturbation_range (G L : SaddleVector →L[ℝ] SaddleVector)
    (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ x, saddlePairing (G x) (L x) ≤ -(κ*‖x‖^2)) :
    ∃ αmax : ℝ, 0 < αmax ∧ ∀ α : ℝ, 0 ≤ α → α ≤ αmax →
      ∀ x, saddlePairing (perturbedGradient G α x) (L x) ≤ -((κ/2)*‖x‖^2) := by
  obtain ⟨C,hC,hL⟩ := L.bound
  refine ⟨κ/(8*C),by positivity,?_⟩
  intro α hα hαmax x
  have hp := saddlePairing_abs_bound x (L x)
  have hn := mul_le_mul_of_nonneg_left (hL x) (by positivity : 0 ≤ 4*‖x‖)
  have hb : saddlePairing x (L x) ≤ 4*C*‖x‖^2 := by
    nlinarith only [hp,hn,le_abs_self (saddlePairing x (L x))]
  have hακ := (le_div_iff₀ (by positivity : 0 < 8*C)).1 hαmax
  have hscaled := mul_le_mul_of_nonneg_right hακ (sq_nonneg ‖x‖)
  have hterm := mul_le_mul_of_nonneg_left hb hα
  rw [perturbedGradient_pairing]
  have hl := hlinear x
  nlinarith only [hscaled,hterm,hl]

noncomputable def perturbedSaddleQuadratic (e z α : ℝ) (x : SaddleVector) : ℝ :=
  saddleQuadraticValue e z x+α/2*saddlePairing x x

/-- Nonpositive perturbed energy implies a strict quadratic margin for the
original energy, measured by displacement norm. -/
theorem perturbed_quadratic_margin (e z α : ℝ) (hα : 0 ≤ α) (x : SaddleVector)
    (hq : perturbedSaddleQuadratic e z α x ≤ 0) :
    saddleQuadraticValue e z x ≤ -(α/2*‖x‖^2) := by
  have hm := mul_le_mul_of_nonneg_left (saddlePairing_self_norm_lower x)
    (by positivity : 0 ≤ α/2)
  unfold perturbedSaddleQuadratic at hq
  linarith only [hq,hm]

theorem negative_quadratic_survives_small_perturbation (e z αmax : ℝ)
    (hmax : 0 < αmax) (v : SaddleVector) (hv : saddleQuadraticValue e z v < 0) :
    ∃ α : ℝ, 0 < α ∧ α ≤ αmax ∧ perturbedSaddleQuadratic e z α v < 0 := by
  let S := saddlePairing v v
  have hS : 0 ≤ S := saddlePairing_self_nonneg v
  let α := min αmax (-saddleQuadraticValue e z v/(S+1))
  have hα : 0 < α := lt_min hmax (div_pos (neg_pos.mpr hv) (by positivity))
  have hbound : α*(S+1) ≤ -saddleQuadraticValue e z v :=
    (le_div_iff₀ (by positivity : 0 < S+1)).1 (min_le_right _ _)
  refine ⟨α,hα,min_le_left _ _,?_⟩
  unfold perturbedSaddleQuadratic
  change saddleQuadraticValue e z v+α/2*S < 0
  nlinarith only [hbound,hv,hα]

/-- A positive quadratic perturbation simultaneously preserves a negative
tangent and strict local dissipation for the actual nonlinear response field. -/
theorem middle_perturbed_pair_certificate (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ α η δ : ℝ, 0 < α ∧ 0 < η ∧ 0 < δ ∧
      perturbedSaddleQuadratic e z α
        ![-(60/(z+2))/(z+2),1,(16+4*z)/(20001/10000),0] < 0 ∧
      ∀ x y : SaddleVector, dist x ![60/(z+2),z,H,0] < δ →
        dist y ![60/(z+2),z,H,0] < δ →
        saddlePairing (perturbedGradient (saddleGradient e z).toContinuousLinearMap α (x-y))
          (responseCoordinateField e x-responseCoordinateField e y) ≤ -(η*‖x-y‖^2) := by
  let B := 60/(z+2)
  let a := 1+2*e*responseA e B
  let p : SaddleVector := ![B,z,H,0]
  let v : SaddleVector := ![-B/(z+2),1,(16+4*z)/(20001/10000),0]
  let G : SaddleVector →L[ℝ] SaddleVector := (saddleGradient e z).toContinuousLinearMap
  let L : SaddleVector →L[ℝ] SaddleVector :=
    (responseCoordinateLinear B z (responseSlope e B) a).toContinuousLinearMap
  have hB : B ∈ Icc (2:ℝ) 34 :=
    curve_B_bounds z ⟨by linarith [hz.1],by linarith [hz.2]⟩
  obtain ⟨hAl,hAu⟩ := response_bounds e B he hu hB.1 hB.2
  have hEl := mul_le_mul_of_nonneg_left hAl he
  have hEu := mul_le_mul_of_nonneg_left hAu he
  have ha : 99/100 ≤ a := by dsimp [a]; nlinarith
  have ha' : a ≤ 101/100 := by dsimp [a]; nlinarith
  have hF : 60-(2+p 1)*p 0 = 0 := by
    have hd : z+2 ≠ 0 := by linarith [hz.1]
    dsimp [p,B]
    field_simp
    ring
  have hd : HasStrictFDerivAt (responseCoordinateField e) L p :=
    responseCoordinateField_hasStrictFDerivAt e p he hu hB (by rfl) hF
  obtain ⟨κ,hκ,hlin⟩ := middle_quadratic_rate_coercive e z he hu hz
  have hlinear : ∀ x, saddlePairing (G x) (L x) ≤ -(κ*‖x‖^2) := by
    intro x
    change saddlePairing (saddleGradient e z x)
      (responseCoordinateLinear (60/(z+2)) z (responseSlope e (60/(z+2))) a x) ≤ _
    rw [saddleGradient_linear_rate]
    exact hlin a ha ha' x
  obtain ⟨αmax,hmax,hpert⟩ := positive_gradient_perturbation_range G L κ hκ hlinear
  have hv : saddleQuadraticValue e z v < 0 := middle_response_direction_negative e z he hu hz
  obtain ⟨α,hα,hαmax,hvα⟩ := negative_quadratic_survives_small_perturbation e z αmax hmax v hv
  obtain ⟨δ,hδ,hpair⟩ := strict_linear_dissipation_persists (responseCoordinateField e)
    (perturbedGradient G α) L p hd (κ/2) (by positivity) (hpert α hα.le hαmax)
  refine ⟨α,(κ/2)/2,δ,hα,by positivity,hδ,hvα,?_⟩
  exact hpair

theorem perturbedSaddleQuadratic_hasDerivAt (e z α : ℝ) (hz : 0 ≤ z)
    (x : ℝ → SaddleVector) (dx : SaddleVector) (t : ℝ) (hx : HasDerivAt x dx t) :
    HasDerivAt (fun s => perturbedSaddleQuadratic e z α (x s))
      (saddlePairing (perturbedGradient (saddleGradient e z).toContinuousLinearMap α (x t)) dx) t := by
  have h0 := ((hasDerivAt_pi.mp hx) 0).mul ((hasDerivAt_pi.mp hx) 0)
  have h1 := ((hasDerivAt_pi.mp hx) 1).mul ((hasDerivAt_pi.mp hx) 1)
  have h2 := ((hasDerivAt_pi.mp hx) 2).mul ((hasDerivAt_pi.mp hx) 2)
  have h3 := ((hasDerivAt_pi.mp hx) 3).mul ((hasDerivAt_pi.mp hx) 3)
  have hs : HasDerivAt (fun s => saddlePairing (x s) (x s)) (2*saddlePairing (x t) dx) t := by
    convert ((h0.add h1).add h2).add h3 using 1
    · funext s
      simp [saddlePairing,Fin.sum_univ_succ]
      ring
    · simp [saddlePairing,Fin.sum_univ_succ]
      ring
  have hv := (saddleQuadraticValue_hasDerivAt e z hz x dx t hx).add ((hs.const_mul α).div_const 2)
  convert hv using 1
  · funext s
    dsimp [perturbedSaddleQuadratic]
    ring
  · rw [perturbedGradient_pairing]
    simp
    ring

theorem perturbedSaddleQuadratic_norm_bound (e z α : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : SaddleVector, |perturbedSaddleQuadratic e z α x| ≤ M*‖x‖^2 := by
  let G := perturbedGradient (saddleGradient e z).toContinuousLinearMap α
  obtain ⟨C,hC,hbound⟩ := G.bound
  refine ⟨2*C,by positivity,?_⟩
  intro x
  have hi : 2*perturbedSaddleQuadratic e z α x = saddlePairing (G x) x := by
    dsimp [G]
    rw [perturbedGradient_pairing]
    simp [perturbedSaddleQuadratic,saddleQuadraticValue,saddleGradient,saddlePairing,
      responseQuadratic,Fin.sum_univ_succ]
    ring
  have hp := saddlePairing_abs_bound (G x) x
  have hm := mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg x)
  have ha : |saddlePairing (G x) x| = 2*|perturbedSaddleQuadratic e z α x| := by
    rw [← hi,abs_mul]
    norm_num
  nlinarith only [hp,hm,ha]

theorem perturbed_negative_B_ne_zero (e z α : ℝ) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hα : 0 ≤ α) (x : SaddleVector) (hq : perturbedSaddleQuadratic e z α x < 0) : x 0 ≠ 0 := by
  have hterm := mul_nonneg (show 0 ≤ α/2 by positivity) (saddlePairing_self_nonneg x)
  have hq' : saddleQuadraticValue e z x < 0 := by
    unfold perturbedSaddleQuadratic at hq
    linarith only [hq,hterm]
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hB : 8 ≤ 60/(z+2) := by
    apply (le_div_iff₀ (by positivity : 0 < z+2)).2
    linarith [hz.2]
  exact negative_quadratic_B_ne_zero (60/(z+2)) z (localForkSlope e (60/(z+2)) z)
    (localWeight z) (x 0) (x 1) (x 2) (x 3) hB hz0
    (by unfold localWeight; positivity) hq'

/-- The closed negative cone has a quantitative B component, sufficient to
compare its side with a nearby moving reference point. -/
theorem perturbed_cone_B_bound (e z α : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) (hα : 0 < α)
    (x : SaddleVector) (hq : perturbedSaddleQuadratic e z α x ≤ 0) :
    α / (2 * localForkSlope e (60/(z+2)) z * (60/(z+2))) * ‖x‖ ≤ |x 0| := by
  let B := 60/(z+2)
  let m := localForkSlope e B z
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hB := curve_B_bounds z
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hB8 : 8 ≤ B := by
    apply (le_div_iff₀ (by positivity : 0 < z+2)).2
    linarith [hz.2]
  have hm : 0 < m := by
    have hc := local_response_coefficients e 0 B z he hu (by norm_num)
      (by norm_num) hB.1 hB.2 hz0 (by linarith [hz.2])
    dsimp [m]
    linarith [hc.2.2.2.2.1]
  have hmB : 0 < m*B := mul_pos hm (by linarith)
  have hplane := quadratic_B_plane_nonnegative B z m (localWeight z)
    (x 1) (x 2) (x 3) hB8 hz0 (by unfold localWeight; positivity)
  have hsplit : saddleQuadraticValue e z x =
      responseQuadratic B z m (localWeight z) (localHSlope z) 0 (x 1) (x 2) (x 3)
        + m*(2+z)*(x 0)^2/2 + m*B*(x 0)*(x 1) := by
    dsimp [saddleQuadraticValue, responseQuadratic, B, m]
    ring
  have hpure : 0 ≤ m*(2+z)*(x 0)^2/2 := by positivity
  have hmargin := perturbed_quadratic_margin e z α hα.le x hq
  have hcross : -(m*B*(x 0)*(x 1)) ≤ m*B*|x 0| *|x 1| := by
    calc
      _ ≤ |m*B*(x 0)*(x 1)| := neg_le_abs _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hmB]
  have hcoord : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x 1
  have hcross' := mul_le_mul_of_nonneg_left hcoord
    (mul_nonneg hmB.le (abs_nonneg (x 0)))
  have hmain : α/2*‖x‖^2 ≤ m*B*|x 0| *‖x‖ := by
    change 0 ≤ responseQuadratic B z m (localWeight z) (localHSlope z)
      0 (x 1) (x 2) (x 3) at hplane
    nlinarith only [hmargin, hsplit, hplane, hpure, hcross, hcross']
  rcases eq_or_lt_of_le (norm_nonneg x) with hn | hn
  · rw [← hn, mul_zero]
    exact abs_nonneg _
  · have hcancel : α/2*‖x‖ ≤ m*B*|x 0| := by
      nlinarith only [hmain, hn]
    change α/(2*m*B)*‖x‖ ≤ |x 0|
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2*m*B by positivity)).2
    nlinarith only [hcancel]

/-- A reference offset smaller than the cone's B margin does not change
which B side contains the displaced point. -/
theorem perturbed_cone_side_transfer (e z α : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) (hα : 0 < α)
    (x y p : SaddleVector) (hq : perturbedSaddleQuadratic e z α (x-y) ≤ 0)
    (hoff : |x 0-p 0| <
      α/(2*localForkSlope e (60/(z+2)) z*(60/(z+2)))*‖x-y‖) :
    (y 0 < p 0 ↔ y 0 < x 0) ∧ (p 0 < y 0 ↔ x 0 < y 0) := by
  have hb := perturbed_cone_B_bound e z α he hu hz hα (x-y) hq
  change _ ≤ |x 0-y 0| at hb
  have hgap : |x 0-p 0| < |x 0-y 0| := hoff.trans_le hb
  have hlow := neg_abs_le (x 0-p 0)
  have hupp := le_abs_self (x 0-p 0)
  rcases le_total (x 0) (y 0) with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hgap
    have hpy : p 0 < y 0 := by linarith
    have hxy' : x 0 < y 0 := by linarith [abs_nonneg (x 0-p 0)]
    exact ⟨⟨fun h => False.elim ((not_lt_of_ge hpy.le) h),
      fun h => False.elim ((not_lt_of_ge hxy) h)⟩,
      ⟨fun _ => hxy', fun _ => hpy⟩⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hgap
    have hyp : y 0 < p 0 := by linarith
    have hyx' : y 0 < x 0 := by linarith [abs_nonneg (x 0-p 0)]
    exact ⟨⟨fun _ => hyx', fun _ => hyp⟩,
      ⟨fun h => False.elim ((not_lt_of_ge hyp.le) h),
      fun h => False.elim ((not_lt_of_ge hyx) h)⟩⟩

end CoreCouplingGlobal
