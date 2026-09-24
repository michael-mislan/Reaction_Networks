import proofs.CoreCouplingGlobal.PotentialHessian

namespace CoreCouplingGlobal
open Set

theorem middle_potential_unit_box (z : ℝ) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (x : SaddleVector)
    (hx : dist x ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0] < 1) :
    x 0 ∈ Icc (2:ℝ) 34 ∧ x 1 ∈ Icc (0:ℝ) 12 ∧
      x 2 ∈ Icc (0:ℝ) (1536/7) := by
  let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
  have hc (i : Fin 4) : |x i-p i| < 1 :=
    lt_of_le_of_lt (norm_le_pi_norm (x-p) i) hx
  have h0 := abs_lt.mp (hc 0)
  have h1 := abs_lt.mp (hc 1)
  have h2 := abs_lt.mp (hc 2)
  dsimp [p] at h0 h1 h2
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hBl : (10:ℝ) ≤ 60/(z+2) :=
    (le_div_iff₀ (by positivity)).2 (by linarith [hz.2])
  have hBu : 60/(z+2) ≤ (20:ℝ) :=
    (div_le_iff₀ (by positivity)).2 (by linarith [hz.1])
  have hzsq := pow_le_pow_left₀ hz0 hz.2 2
  have hHl : (1:ℝ) ≤ (16*z+2*z^2)/(20001/10000) :=
    (le_div_iff₀ (by norm_num)).2 (by nlinarith [hz.1,sq_nonneg z])
  have hHu : (16*z+2*z^2)/(20001/10000) ≤ (40:ℝ) :=
    (div_le_iff₀ (by norm_num)).2 (by nlinarith [hz.2])
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith [hz.1],by linarith [hz.2]⟩,
    ⟨by linarith,by linarith⟩⟩

/-- The actual potential has an arbitrarily small norm-square error relative
to the saddle quadratic near the middle stationary response point. -/
theorem responsePotential_quadratic_remainder (e z : ℝ) (P : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hZ : responseTotal e (60/(z+2))-(1+z)*(60/(z+2))-16*z-4*z^2+
      3*((16*z+2*z^2)/(20001/10000)) = 0) (ε : ℝ) (hε : 0 < ε) :
    let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : SaddleVector, dist x p < δ →
      |responsePotential e P (x 0) (x 1) (x 2) (x 3)-
        responsePotential e P (p 0) (p 1) (p 2) (p 3)-
        saddleQuadraticValue e z (x-p)| ≤ ε*‖x-p‖^2 := by
  dsimp only
  let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
  obtain ⟨d,hd,hrem⟩ := potentialGradient_linear_remainder e z he hu hz hZ
    (ε/4) (by positivity)
  let δ := min d 1
  refine ⟨δ,lt_min hd (by norm_num),?_⟩
  intro x hx
  let v := x-p
  let γ := fun t : ℝ => p+t • v
  let f := fun t : ℝ => responsePotential e P (γ t 0) (γ t 1) (γ t 2) (γ t 3)-
    saddleQuadraticValue e z (t • v)
  let df := fun t : ℝ => saddlePairing
    (potentialGradient e (γ t)-saddleGradient e z (t • v)) v
  have hn (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖t • v‖ ≤ ‖v‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg v) ht.2
  have hdist (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : dist (γ t) p < δ := by
    have heq : γ t-p = t • v := by dsimp [γ]; abel
    rw [dist_eq_norm,heq]
    exact (hn t ht).trans_lt hx
  have hderiv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (df t) t := by
    intro t ht
    have hbox := middle_potential_unit_box z hz (γ t)
      ((hdist t ht).trans_le (min_le_right _ _))
    have dv : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    have dγ : HasDerivAt γ v t := dv.const_add p
    have dV := responsePotential_gradient_hasDerivAt e P he hu γ v t dγ
      hbox.1 hbox.2.1 hbox.2.2
    have dQ := saddleQuadraticValue_hasDerivAt e z (by linarith [hz.1])
      (fun s => s • v) v t dv
    convert dV.sub dQ using 1
    simp [df,saddlePairing,sub_mul,Finset.sum_sub_distrib]
  have hbound : ∀ t ∈ Ico (0:ℝ) 1, ‖df t‖ ≤ ε*‖v‖^2 := by
    intro t ht
    have htt : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hh := hrem (γ t) ((hdist t htt).trans_le (min_le_left _ _))
    have heq : γ t-p = t • v := by dsimp [γ]; abel
    rw [heq] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (hn t htt) (by positivity : 0 ≤ ε/4))
    have hp := saddlePairing_abs_bound
      (potentialGradient e (γ t)-saddleGradient e z (t • v)) v
    have hm := mul_le_mul_of_nonneg_right hh' (norm_nonneg v)
    change |df t| ≤ _
    dsimp [df]
    nlinarith only [hp,hm]
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound
  have hγ1 : γ 1 = x := by dsimp [γ,v]; simp
  have hγ0 : γ 0 = p := by dsimp [γ]; simp
  have hQ0 : saddleQuadraticValue e z (0:SaddleVector) = 0 := by
    simp [saddleQuadraticValue,responseQuadratic]
  dsimp [f] at hmean
  rw [hγ1,hγ0,one_smul,zero_smul,hQ0,sub_zero] at hmean
  change |responsePotential e P (x 0) (x 1) (x 2) (x 3)-saddleQuadraticValue e z v-
    responsePotential e P (p 0) (p 1) (p 2) (p 3)| ≤ _ at hmean
  convert hmean using 1
  congr 1
  ring

end CoreCouplingGlobal
