import proofs.CoreCouplingGlobal.RoutedLoadMechanism

open Filter Topology
namespace CoreCouplingGlobal
open CoreCouplingCAC Set

/-- Analytic certificate: root signs, positive reconstruction and uniform matrix
bounds. No stationary-state existence or trajectory conclusion is assumed. -/
structure RoutedAttractorCriterion (e g l r : ℝ) (lo hi : State)
    (L R : Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ) : Prop where
  interval : l ≤ r
  left_sign : routedPoly e g l < 0
  right_sign : 0 < routedPoly e g r
  positive_lift : ∀ z ∈ Icc l r, (routedLift g z).Positive
  denominator : ∀ z ∈ Icc l r, routedDen g z ≠ 0
  left_positive : ∀ i, 0 < L i
  right_positive : ∀ i, 0 < R i
  weight_lower : ∀ i, (1/4:ℝ) ≤ L i/R i
  near_energy : ∀ c x, Near c x →
    energy L R (transform c) (transform x) ≤ (1/1000000000000:ℝ)
  sublevel_box : ∀ z ∈ Icc l r, ∀ x,
    energy L R (transform (routedLift g z)) (transform x) ≤ (1/1000000000000:ℝ) →
      InBox x lo hi
  box_positive : ∀ x, InBox x lo hi → x.Positive
  box_norm : ∀ x, InBox x lo hi → ‖transform x‖ ≤ 100
  domination : ∀ x, InBox x lo hi →
    (∀ i, routedJacobian e g (transform x) i i ≤ M i i) ∧
    (∀ i j, i ≠ j → |routedJacobian e g (transform x) i j| ≤ M i j)
  row_decay : ∀ i, L i*(∑ j, M i j*R j)+R i*(∑ j, M j i*L j) ≤
    -(1/100:ℝ)*(L i*R i)

theorem routed_criterion_attractor (e g l r : ℝ) (hg : g ≠ 0)
    (lo hi : State) (L R : Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ)
    (h : RoutedAttractorCriterion e g l r lo hi L R M) :
    ∃ c : State, c.Positive ∧ RoutedStationary e g c ∧ c.z ∈ Icc l r ∧
      RoutedSelected e g L R c := by
  obtain ⟨z,hz,hr⟩ := intermediate_value_Icc h.interval
    (routed_poly_continuous e g).continuousOn ⟨h.left_sign.le,h.right_sign.le⟩
  let c := routedLift g z
  have hc : c.Positive := h.positive_lift z hz
  have hs : RoutedStationary e g c := routed_lift_stationary e g z hg (h.denominator z hz) hr
  have hsub : ∀ x, energy L R (transform c) (transform x) ≤ (1/1000000000000:ℝ) →
      InBox x lo hi := h.sublevel_box z hz
  have hcbox : InBox c lo hi := hsub c (by simp [energy])
  have hdec : ∀ x, InBox x lo hi → routedEnergyRate e g L R (transform c) (transform x) ≤
      -(1/100:ℝ)*energy L R (transform c) (transform x) := by
    intro x hx
    have hm := h.domination (midpointState x c) (midpoint_inBox x c lo hi hx hcbox)
    rw [midpoint_transform] at hm
    exact routed_nonlinear_energy_bound e g M L R (transform c) (transform x) (1/100)
      h.left_positive h.right_positive (routed_stationary_transformed e g c hs)
      hm.1 hm.2 h.row_decay
  refine ⟨c,hc,hs,hz,?_⟩
  intro x₀ hx₀
  have h0 := h.near_energy c x₀ hx₀
  constructor
  · obtain ⟨X,hX0,hX,hlim⟩ := routed_local_selection e g L R c lo hi h.weight_lower
      hsub h.box_norm h.box_positive hdec x₀ h0
    exact ⟨X,hX0,fun t ht => ⟨(hX t ht).1,(hX t ht).2.1,(hX t ht).2.2.2⟩,hlim⟩
  · intro Y hY0 hY
    exact (routed_all_local_solutions_converge e g L R c lo hi h.weight_lower hsub
      hdec Y hY (by simpa only [hY0] using h0)).2

theorem routed_two_certificates_bistability (e g l₁ r₁ l₂ r₂ : ℝ) (hg : g ≠ 0)
    (lo₁ hi₁ lo₂ hi₂ : State) (L₁ R₁ L₂ R₂ : Fin 4 → ℝ)
    (M₁ M₂ : Fin 4 → Fin 4 → ℝ) (hsep : r₁ < l₂)
    (h₁ : RoutedAttractorCriterion e g l₁ r₁ lo₁ hi₁ L₁ R₁ M₁)
    (h₂ : RoutedAttractorCriterion e g l₂ r₂ lo₂ hi₂ L₂ R₂ M₂) :
    ∃ x y : State, x.Positive ∧ y.Positive ∧ RoutedStationary e g x ∧
      RoutedStationary e g y ∧ x.z < y.z ∧
      RoutedSelected e g L₁ R₁ x ∧ RoutedSelected e g L₂ R₂ y := by
  obtain ⟨x,hx,hsx,hzx,hselx⟩ := routed_criterion_attractor e g l₁ r₁ hg lo₁ hi₁ L₁ R₁ M₁ h₁
  obtain ⟨y,hy,hsy,hzy,hsely⟩ := routed_criterion_attractor e g l₂ r₂ hg lo₂ hi₂ L₂ R₂ M₂ h₂
  exact ⟨x,y,hx,hy,hsx,hsy,lt_of_le_of_lt hzx.2 (lt_of_lt_of_le hsep hzy.1),hselx,hsely⟩

theorem routed_low_creation_certificate (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1) :
    RoutedAttractorCriterion e g (9957/10000) (9959/10000)
      routedLowLower routedLowUpper lowLeft lowRight routedLowComparison := by
  refine ⟨by norm_num,(by linarith [routed_stable_sign_lowLeft e g he heu hg hgu]),
    (by linarith [routed_stable_sign_lowRight e g he heu hg hgu]),?_,?_,
    low_comparison_certificate.2.1,low_comparison_certificate.1,low_weight_lower,
    low_near_energy,?_,routedLow_box_positive,routedLow_box_norm,
    routedLow_jacobian_domination e g he heu hg hgu,routedLow_energy_row⟩
  · intro z hz
    exact routed_lift_positive g z (by linarith) hgu ⟨by linarith [hz.1],by linarith [hz.2]⟩
  · intro z hz
    exact ne_of_gt (routed_den_positive g z (by linarith) hgu (by linarith [hz.1]))
  · intro z hz x hx
    exact routedLow_energy_inBox x (routedLift g z) (routedLow_root_enclosure g z hg hgu hz) hx

theorem routed_high_creation_certificate (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1) :
    RoutedAttractorCriterion e g (14881/5000) (14883/5000)
      routedHighLower routedHighUpper highLeft highRight routedHighComparison := by
  refine ⟨by norm_num,(by linarith [routed_stable_sign_highLeft e g he heu hg hgu]),
    (by linarith [routed_stable_sign_highRight e g he heu hg hgu]),?_,?_,
    high_comparison_certificate.2.1,high_comparison_certificate.1,high_weight_lower,
    high_near_energy,?_,routedHigh_box_positive,routedHigh_box_norm,
    routedHigh_jacobian_domination e g he heu hg hgu,routedHigh_energy_row⟩
  · intro z hz
    exact routed_lift_positive g z (by linarith) hgu ⟨by linarith [hz.1],by linarith [hz.2]⟩
  · intro z hz
    exact ne_of_gt (routed_den_positive g z (by linarith) hgu (by linarith [hz.1]))
  · intro z hz x hx
    exact routedHigh_energy_inBox x (routedLift g z) (routedHigh_root_enclosure g z hg hgu hz) hx

end CoreCouplingGlobal
