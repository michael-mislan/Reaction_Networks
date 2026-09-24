import proofs.CoreCouplingGlobal.RoutedWeakCoupling

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem routed_den_positive (g z : ℝ) (hg : 0 < g) (hgu : g ≤ 1)
    (hz : 0 < z) : 0 < routedDen g z := by
  dsimp [routedDen]
  nlinarith [mul_pos hg hz]

theorem routed_lift_residual (e g z : ℝ) (hg : g ≠ 0)
    (hd : routedDen g z ≠ 0) :
    fB (flagshipRates e) (routedLift g z).A (routedLift g z).B
      (1-g+g*z) = routedPoly e g z/(g^2*(routedDen g z)^2) := by
  dsimp [fB,flagshipRates,routedLift,routedPoly]
  field_simp [hg,hd]
  ring

theorem routed_stationary_reconstruction (e g : ℝ) (hg : 0 < g) (hgu : g ≤ 1)
    (x : State) (hx : x.Positive) (hs : RoutedStationary e g x) :
    x=routedLift g x.z ∧ routedPoly e g x.z=0 := by
  obtain ⟨hB,_,hK⟩ := routed_stationary_balances e g x hs
  have hd := routed_den_positive g x.z hg hgu hx.2.2.1
  have hb : x.B=60/routedDen g x.z := (eq_div_iff (ne_of_gt hd)).2 hB
  have ha : x.A=(routedLift g x.z).A := by
    dsimp [routedLift,routedNumerA]
    apply (eq_div_iff (mul_ne_zero (ne_of_gt hg) (ne_of_gt hd))).2
    rw [hb] at hK
    field_simp [ne_of_gt hd] at hK
    nlinarith only [hK]
  have hh : x.H=(routedLift g x.z).H := by
    have h := hs.2.2.2
    dsimp [fH,flagshipRates] at h
    dsimp [routedLift]
    linarith only [h]
  have heq : x=routedLift g x.z := by
    cases x
    simp_all [routedLift]
  have hr := routed_lift_residual e g x.z (ne_of_gt hg) (ne_of_gt hd)
  have hzero : fB (flagshipRates e) (routedLift g x.z).A (routedLift g x.z).B
      (1-g+g*x.z)=0 := by
    rw [← ha]
    change fB (flagshipRates e) x.A (60/routedDen g x.z) (1-g+g*x.z)=0
    rw [← hb]
    exact hs.2.1
  rw [hzero] at hr
  exact ⟨heq,(div_eq_zero_iff).mp hr.symm |>.resolve_right (by positivity)⟩

theorem routed_lift_positive_iff (g z : ℝ) (hg : 0 < g) (hgu : g ≤ 1)
    (hz : 0 < z) : (routedLift g z).Positive ↔ 0 < routedNumerA g z := by
  have hd := routed_den_positive g z hg hgu hz
  constructor
  · intro h
    have ha := h.1
    dsimp [routedLift] at ha
    exact (div_pos_iff_of_pos_right (mul_pos hg hd)).mp ha
  · intro hn
    refine ⟨?_,?_,hz,?_⟩ <;> dsimp [routedLift] <;> positivity

/-- All positive stationary states, with no hidden bracket restriction, are
exactly the positive admissible roots of the scalar compatibility polynomial. -/
theorem routed_positive_stationary_iff (e g : ℝ) (hg : 0 < g) (hgu : g ≤ 1)
    (x : State) :
    (x.Positive ∧ RoutedStationary e g x) ↔
    ∃ z : ℝ, 0 < z ∧ 0 < routedNumerA g z ∧ routedPoly e g z=0 ∧ x=routedLift g z := by
  constructor
  · rintro ⟨hx,hs⟩
    obtain ⟨heq,hp⟩ := routed_stationary_reconstruction e g hg hgu x hx hs
    refine ⟨x.z,hx.2.2.1,?_,hp,heq⟩
    apply (routed_lift_positive_iff g x.z hg hgu hx.2.2.1).1
    rw [← heq]
    exact hx
  · rintro ⟨z,hz,hn,hp,rfl⟩
    exact ⟨(routed_lift_positive_iff g z hg hgu hz).2 hn,
      routed_lift_stationary e g z (ne_of_gt hg)
        (ne_of_gt (routed_den_positive g z hg hgu hz)) hp⟩

theorem routed_compatibility_factorization (e g z a : ℝ) (hg : g ≠ 0)
    (hd : routedDen g z ≠ 0)
    (ha : e*a^2+a=33-(1-e)*(60/routedDen g z)) :
    routedPoly e g z/(g^2*(routedDen g z)^2)=
      ((routedLift g z).A-a)*(1+e*((routedLift g z).A+a)) := by
  have hb : (60/routedDen g z)*routedDen g z=60 := div_mul_cancel₀ _ hd
  rw [← routed_lift_residual e g z hg hd]
  dsimp [fB,flagshipRates,routedLift]
  dsimp [routedDen] at hb ha ⊢
  linear_combination ha-hb

/-- A positive compatibility multiplier preserves the load/response sign;
this is a stationary identity, not an invariant scalar ODE. -/
theorem routed_compatibility_zero_iff (e g z a : ℝ) (he : 0 ≤ e)
    (hg : 0 < g) (hgu : g ≤ 1) (hz : 0 < z)
    (ha : 0 < a) (hload : 0 < (routedLift g z).A)
    (hq : e*a^2+a=33-(1-e)*(60/routedDen g z)) :
    routedPoly e g z=0 ↔ (routedLift g z).A=a := by
  have hd := routed_den_positive g z hg hgu hz
  have hp : 0 < 1+e*((routedLift g z).A+a) := by positivity
  have hf := routed_compatibility_factorization e g z a (ne_of_gt hg) (ne_of_gt hd) hq
  constructor
  · intro h
    rw [h,zero_div] at hf
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf.symm).resolve_right (ne_of_gt hp))
  · intro h
    rw [h,sub_self,zero_mul] at hf
    exact (div_eq_zero_iff.mp hf).resolve_right (by positivity)

end CoreCouplingGlobal
