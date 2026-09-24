import proofs.MultiConsumerPermanence.RateComposition

namespace MultiConsumerPermanence
open Filter Topology Set

/-- Variable-speed damping retains a linear, rather than quadratic, floor. -/
theorem variable_speed_eventual_bound (u v S : ℝ → ℝ) (T a b s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hS : ∀ t, T ≤ t → s ≤ S t)
    (du : ∀ t, T ≤ t → HasDerivAt u (v t) t)
    (hv : ∀ t, T ≤ t → v t ≤ S t*(a-b*u t)) :
    ∀ᶠ t in atTop, u t < 2*a/b := by
  let R := 3*a/(2*b)
  let K := max (u T-R) 0
  let B := fun t => R+K*Real.exp (-(b*s)*(t-T))
  let B' := fun t => -(b*s)*K*Real.exp (-(b*s)*(t-T))
  have hK : 0 ≤ K := le_max_right _ _
  have hR : a-b*R = -a/2 := by dsimp [R]; field_simp; ring
  have dB (t : ℝ) : HasDerivAt B (B' t) t := by
    convert ((((hasDerivAt_id t).sub_const T).const_mul (-(b*s))).exp.const_mul K).const_add R using 1
    dsimp [B,B']
    ring
  have hbound : ∀ t, T ≤ t → u t ≤ B t := by
    intro t ht
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun r hr => (du r hr.1).continuousAt.continuousWithinAt)
      (fun r hr => (du r hr.1).hasDerivWithinAt) (B := B) (B' := B') _ dB _ ⟨ht,le_rfl⟩
    · dsimp [B,K]
      simp only [sub_self,mul_zero,Real.exp_zero,mul_one]
      have hh := le_max_left (u T-R) 0
      linarith only [hh]
    · intro r hr heq
      have hp : 0 ≤ K*Real.exp (-(b*s)*(r-T)) := mul_nonneg hK (Real.exp_pos _).le
      have hneg : a-b*u r < 0 := by
        rw [heq]
        dsimp [B]
        nlinarith only [hR,hp,ha,hb]
      have hm := mul_le_mul_of_nonpos_right (hS r hr.1) hneg.le
      have hd := hv r hr.1
      rw [heq] at hm hd
      dsimp [B,B'] at hm hd ⊢
      have has := mul_pos ha hs
      have hrs := congrArg (fun q : ℝ => s*q) hR
      nlinarith only [hm,hd,hrs,has]
  have he : Tendsto (fun t : ℝ => Real.exp (-(b*s)*(t-T))) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => t-T) atTop atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
    exact Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (neg_neg_of_pos (mul_pos hb hs)))
  have hlim : Tendsto B atTop (𝓝 R) := by
    simpa only [mul_zero,add_zero] using (he.const_mul K).const_add R
  have hlt : R < 2*a/b := by
    dsimp [R]
    apply (div_lt_div_iff₀ (by positivity : 0 < 2*b) hb).2
    nlinarith only [mul_pos ha hb]
  filter_upwards [hlim.eventually_lt_const hlt,eventually_ge_atTop T] with t ht htT
  exact (hbound t htT).trans_lt ht

theorem sharp_species_floor (S x v : ℝ → ℝ) (T a b s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hx : ∀ t, T ≤ t → 0 < x t) (hS : ∀ t, T ≤ t → s ≤ S t)
    (du : ∀ t, T ≤ t → HasDerivAt (fun t => S t/x t) (v t) t)
    (hv : ∀ t, T ≤ t → v t ≤ S t*(a-b*(S t/x t))) :
    ∀ᶠ t in atTop, s*b/(2*a) < x t := by
  have hh := variable_speed_eventual_bound _ v S T a b s ha hb hs hS du hv
  filter_upwards [hh,eventually_ge_atTop T] with t ht htT
  have hq := (div_lt_iff₀ (hx t htT)).mp ht
  have hm := mul_lt_mul_of_pos_right ((hS t htT).trans_lt hq) hb
  apply (div_lt_iff₀ (by positivity : 0 < 2*a)).2
  field_simp at hm
  nlinarith only [hm]

theorem sharp_reference_recovery (S Q x g : ℝ → ℝ) (T n s : ℝ)
    (hn : 0 < n) (hs : 0 < s)
    (hx : ∀ t, T ≤ t → 0 < x t) (hS : ∀ t, T ≤ t → s ≤ S t)
    (hc : ∀ t, T ≤ t → (S t)^2 ≤ n*Q t)
    (dS : ∀ t, T ≤ t → HasDerivAt S (g t*S t-n*Q t) t)
    (dx : ∀ t, T ≤ t → HasDerivAt x (x t*(g t-n*x t)) t) :
    ∀ᶠ t in atTop, s/(2*n) < x t := by
  simpa only [mul_one] using sharp_species_floor S x _ T n 1 s hn (by norm_num) hs hx hS
    (fun t ht => (dS t ht).div (dx t ht) (ne_of_gt (hx t ht)))
    (fun t ht => by
      have hh := ratio_drift (S t) (Q t) (x t) (g t) n (hx t ht) (hc t ht)
      nlinarith only [hh])

theorem sharp_perturbed_ratio_drift (S A H x a rho N eps s : ℝ)
    (hx : 0 < x) (hs : 0 < s) (hS : s ≤ S)
    (hr : rho ≤ N) (heps : eps ≤ s/8)
    (hA : A-a*S ≤ 2*eps*S) (hH : S^2/2 ≤ H) :
    ((A-H)*x-S*(x*(a-rho*x)))/x^2 ≤ S*(N-(S/x)/4) := by
  have hid : ((A-H)*x-S*(x*(a-rho*x)))/x^2 = (A-a*S-H)/x+rho*S := by field_simp; ring
  rw [hid]
  have hnum : A-a*S-H ≤ 2*eps*S-S^2/2 := by linarith only [hA,hH]
  have hdiv := div_le_div_of_nonneg_right hnum hx.le
  have hu : 0 ≤ S/x := div_nonneg (hs.le.trans hS) hx.le
  have hdamp := mul_le_mul_of_nonneg_right (show 2*eps-S/2 ≤ -S/4 by linarith only [heps,hS]) hu
  have hrS := mul_le_mul_of_nonneg_right hr (hs.le.trans hS)
  calc
    _ ≤ (2*eps*S-S^2/2)/x+rho*S := add_le_add hdiv le_rfl
    _ = (2*eps-S/2)*(S/x)+rho*S := by ring
    _ ≤ S*(N-(S/x)/4) := by nlinarith only [hdamp,hrS]

end MultiConsumerPermanence
