import proofs.CoreCouplingGlobal.PotentialTaylor

namespace CoreCouplingGlobal
open Set

theorem saddleQuadratic_shift_bound (e z : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ v w : SaddleVector,
      |saddleQuadraticValue e z (v+w)-saddleQuadraticValue e z v| ≤
        K*‖w‖*(‖v‖+‖w‖) := by
  obtain ⟨C,hC,hG⟩ := (saddleGradient e z).toContinuousLinearMap.bound
  obtain ⟨M,hM,hQ⟩ := perturbedSaddleQuadratic_norm_bound e z 0
  refine ⟨4*C+M,by positivity,?_⟩
  intro v w
  have hi : saddleQuadraticValue e z (v+w)-saddleQuadraticValue e z v =
      saddlePairing (saddleGradient e z v) w+saddleQuadraticValue e z w := by
    simp [saddleQuadraticValue,responseQuadratic,saddlePairing,saddleGradient,Fin.sum_univ_succ]
    ring
  have hQw : |saddleQuadraticValue e z w| ≤ M*‖w‖^2 := by
    simpa [perturbedSaddleQuadratic] using hQ w
  have hp := saddlePairing_abs_bound (saddleGradient e z v) w
  have hg := mul_le_mul_of_nonneg_right (hG v) (norm_nonneg w)
  change ‖saddleGradient e z v‖*‖w‖ ≤ C*‖v‖*‖w‖ at hg
  rw [hi]
  have ha := abs_add_le (saddlePairing (saddleGradient e z v) w) (saddleQuadraticValue e z w)
  have hnon := mul_nonneg hM.le (mul_nonneg (norm_nonneg v) (norm_nonneg w))
  have hnon' := mul_nonneg hC.le (sq_nonneg ‖w‖)
  nlinarith only [hQw,hp,hg,ha,hnon,hnon']

/-- A negative pair cone reaches energy below the middle equilibrium when
the reference offset is sufficiently small relative to the exit radius. -/
theorem negative_cone_exit_energy (e z α : ℝ) (P : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hZ : responseTotal e (60/(z+2))-(1+z)*(60/(z+2))-16*z-4*z^2+
      3*((16*z+2*z^2)/(20001/10000)) = 0) (hα : 0 < α) :
    let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
    ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧ θ ≤ 1/2 ∧
      ∀ r : ℝ, 0 < r → r < δ → ∀ x y : SaddleVector,
      dist x p < θ*r → dist y p = r → perturbedSaddleQuadratic e z α (y-x) ≤ 0 →
      responsePotential e P (y 0) (y 1) (y 2) (y 3) <
        responsePotential e P (p 0) (p 1) (p 2) (p 3) := by
  dsimp only
  let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
  obtain ⟨K,hK,hshift⟩ := saddleQuadratic_shift_bound e z
  obtain ⟨δ,hδ,hTaylor⟩ := responsePotential_quadratic_remainder e z P he hu hz hZ
    (α/32) (by positivity)
  let θ := min (1/2:ℝ) (α/(48*K))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hα (by positivity))
  have hθh : θ ≤ 1/2 := min_le_left _ _
  have hθK : 48*K*θ ≤ α := by
    have hh := (le_div_iff₀ (show 0 < 48*K by positivity)).1 (min_le_right (1/2:ℝ) (α/(48*K)))
    nlinarith only [hh]
  refine ⟨δ,θ,hδ,hθ,hθh,?_⟩
  intro r hr hrδ x y hx hy hq
  let v := y-x
  let w := x-p
  have hi : v+w = y-p := by dsimp [v,w]; abel
  have hw : ‖w‖ < θ*r := hx
  have hw' : ‖w‖ ≤ r/2 := by nlinarith [mul_le_mul_of_nonneg_right hθh hr.le]
  have hyp : ‖y-p‖ = r := hy
  have hsum : r ≤ ‖v‖+‖w‖ := by rw [← hyp,← hi]; exact norm_add_le _ _
  have hvlow : r/2 ≤ ‖v‖ := by linarith
  have hvup : ‖v‖ ≤ 2*r := by
    have heq : v = (y-p)-w := by dsimp [v,w]; abel
    rw [heq]
    have hh := norm_sub_le (y-p) w
    rw [hyp] at hh
    linarith
  have hmargin := perturbed_quadratic_margin e z α hα.le v hq
  have hsquare : r^2/4 ≤ ‖v‖^2 := by nlinarith [sq_nonneg (‖v‖-r/2)]
  have hmul := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ α/2 by positivity)
  have hQv : saddleQuadraticValue e z v ≤ -(α*r^2/8) := by nlinarith only [hmargin,hmul]
  have herror := hshift v w
  have hprod : K*‖w‖*(‖v‖+‖w‖) ≤ K*(θ*r)*(3*r) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hw.le hK.le
    · linarith
    · positivity
    · positivity
  have hscale : K*(θ*r)*(3*r) ≤ α*r^2/16 := by
    have hh := mul_le_mul_of_nonneg_right hθK (sq_nonneg r)
    nlinarith only [hh]
  have hQy : saddleQuadraticValue e z (y-p) ≤ -(α*r^2/16) := by
    have ha := le_abs_self (saddleQuadraticValue e z (v+w)-saddleQuadraticValue e z v)
    rw [hi] at herror ha
    linarith only [hQv,herror,ha,hprod,hscale]
  have hT := hTaylor y (by rw [hy]; exact hrδ)
  rw [hyp] at hT
  change |responsePotential e P (y 0) (y 1) (y 2) (y 3)-
    responsePotential e P (p 0) (p 1) (p 2) (p 3)-saddleQuadraticValue e z (y-p)| ≤
    α/32*r^2 at hT
  have ha := le_abs_self (responsePotential e P (y 0) (y 1) (y 2) (y 3)-
    responsePotential e P (p 0) (p 1) (p 2) (p 3)-saddleQuadraticValue e z (y-p))
  have hpos : 0 < α*r^2 := mul_pos hα (sq_pos_of_pos hr)
  change responsePotential e P (y 0) (y 1) (y 2) (y 3) <
    responsePotential e P (p 0) (p 1) (p 2) (p 3)
  nlinarith only [hT,ha,hQy,hpos]

end CoreCouplingGlobal
