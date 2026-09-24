import proofs.OverlappingSiphonInvasion.ResidentEntropy
import proofs.CoreCouplingGlobal.DissipationLimit

noncomputable section
open Set Filter Topology
namespace OverlappingSiphonInvasion

private theorem compact_observable_uniform {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : Set E) (hK : IsCompact K) (f : E → E) (q : E → ℝ)
    (hf : ContinuousOn f K) (hq : ContinuousOn q K) (X : ℝ → E) (T : ℝ)
    (hX : ∀ t, T ≤ t → X t ∈ K)
    (hd : ∀ t, T ≤ t → HasDerivAt X (f (X t)) t) :
    UniformContinuousOn (fun t => q (X t)) (Ici T) := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image hf.nnnorm
  have hlip : LipschitzOnWith C X (Ici T) :=
    (convex_Ici T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t ht => hC (mem_image_of_mem _ (hX t ht)))
  exact (hK.uniformContinuousOn_of_continuous hq).comp hlip.uniformContinuousOn hX

private theorem tendsto_of_square_bound (x q : ℝ → ℝ) (a c T : ℝ)
    (hc : 0 < c) (hq : Tendsto q atTop (𝓝 0))
    (hb : ∀ t, T ≤ t → c*(x t-a)^2 ≤ q t) :
    Tendsto x atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have he : 0 < c*ε^2 := mul_pos hc (sq_pos_of_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hq (Iio_mem_nhds he))
  refine ⟨max T N,?_⟩
  intro t ht
  have hsmall := hN t ((le_max_right T N).trans ht)
  have hbound := hb t ((le_max_left T N).trans ht)
  rw [Real.dist_eq]
  by_contra hn
  have hlarge : ε ≤ |x t-a| := le_of_not_gt hn
  have hsquare : ε^2 ≤ (x t-a)^2 := by
    nlinarith [sq_abs (x t-a),abs_nonneg (x t-a)]
  have hm := mul_le_mul_of_nonneg_left hsquare hc.le
  exact (not_lt_of_ge (hm.trans hbound)) hsmall

/-- Convergence on a resident plane, requiring only a source upper box and a
susceptible floor. No infected floor or limiting-behavior premise is used. -/
theorem resident_converges_of_box (se ue α μ₀ M l T : ℝ) (s u : ℝ → ℝ)
    (hse : 0 < se) (hue : 0 < ue) (hα : 0 < α) (hμ : 0 < μ₀)
    (hM : 0 < M) (hl : 0 < l)
    (hb : ∀ t, T ≤ t → 0 < s t ∧ 0 < u t ∧ l ≤ s t ∧ s t ≤ M ∧ u t ≤ M)
    (hds : ∀ t, T ≤ t → HasDerivAt s (-(μ₀+α*ue)*(s t-se)-α*s t*(u t-ue)) t)
    (hdu : ∀ t, T ≤ t → HasDerivAt u (α*u t*(s t-se)) t) :
    Tendsto s atTop (𝓝 se) ∧ Tendsto u atTop (𝓝 ue) := by
  let K := μ₀+α*ue
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := min (K/(4*M)/(α*M)) ((α*l/2)/(K*M)) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε*α*M ≤ K/(4*M) := by
    have hh := min_le_left (K/(4*M)/(α*M)) ((α*l/2)/(K*M))
    have hh' : ε ≤ K/(4*M)/(α*M) := by dsimp [ε] at hε ⊢; linarith
    have hm := (le_div_iff₀ (mul_pos hα hM)).mp hh'
    nlinarith only [hm]
  have hε2 : ε*K*M ≤ α*l/2 := by
    have hh := min_le_right (K/(4*M)/(α*M)) ((α*l/2)/(K*M))
    have hh' : ε ≤ (α*l/2)/(K*M) := by dsimp [ε] at hε ⊢; linarith
    have hm := (le_div_iff₀ (mul_pos hK hM)).mp hh'
    nlinarith only [hm]
  let c := K/(2*M)
  let d := ε*α*l/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  let X : ℝ → ℝ × ℝ := fun t => (s t,u t)
  let F : ℝ × ℝ → ℝ × ℝ := fun x => (-K*(x.1-se)-α*x.1*(x.2-ue),α*x.2*(x.1-se))
  let Q : ℝ × ℝ → ℝ := fun x => c*(x.1-se)^2+d*(x.2-ue)^2
  let V : ℝ → ℝ := fun t => residentEntropy se ue ε (s t) (u t)
  let v : ℝ → ℝ := fun t => -(K/s t-ε*α*u t)*(s t-se)^2-
    ε*K*(s t-se)*(u t-ue)-ε*α*s t*(u t-ue)^2
  have hVd : ∀ t, T ≤ t → HasDerivAt V (v t) t := by
    intro t ht
    exact residentEntropy_derivative se ue α μ₀ ε s u t hse hue
      (hb t ht).1 (hb t ht).2.1 (hds t ht) (hdu t ht)
  have hv : ∀ t, T ≤ t → v t ≤ -Q (X t) := by
    intro t ht
    have hh := resident_strict_drift α K M l ε (s t) (u t) (s t-se) (u t-ue)
      hα hK hM hl hε (hb t ht).2.2.1 (hb t ht).2.2.2.1 (hb t ht).2.2.2.2 hε1 hε2
    dsimp [v,Q,X,c,d]
    linarith only [hh]
  have hq0 : ∀ t, T ≤ t → 0 ≤ Q (X t) := by
    intro t _
    dsimp [Q]
    positivity
  have hlow : ∀ t, T ≤ t → -ε*M*(ue+se) ≤ V t := by
    intro t ht
    exact residentEntropy_lower se ue ε M (s t) (u t) hse hue hε.le
      (hb t ht).1 (hb t ht).2.1 (hb t ht).2.2.2.1 (hb t ht).2.2.2.2
  have huq : UniformContinuousOn (fun t => Q (X t)) (Ici T) := by
    apply compact_observable_uniform (Icc ((0:ℝ),0) (M,M)) isCompact_Icc F Q
    · exact (by dsimp [F]; fun_prop : Continuous F).continuousOn
    · exact (by dsimp [Q]; fun_prop : Continuous Q).continuousOn
    · intro t ht
      exact ⟨⟨(hb t ht).1.le,(hb t ht).2.1.le⟩,
        ⟨(hb t ht).2.2.2.1,(hb t ht).2.2.2.2⟩⟩
    · intro t ht
      exact (hds t ht).prodMk (hdu t ht)
  obtain ⟨L,hL⟩ := CoreCouplingGlobal.potential_tendsto_of_bounded_dissipation
    V v (fun t => Q (X t)) T (-ε*M*(ue+se)) hVd hv hq0 hlow
  have hq := CoreCouplingGlobal.dissipation_tendsto_zero
    V v (fun t => Q (X t)) T L hVd hv hq0 huq hL
  constructor
  · apply tendsto_of_square_bound s (fun t => Q (X t)) se c T hc hq
    intro t _
    dsimp [Q,X]
    nlinarith [mul_nonneg hd.le (sq_nonneg (u t-ue))]
  · apply tendsto_of_square_bound u (fun t => Q (X t)) ue d T hd hq
    intro t _
    dsimp [Q,X]
    nlinarith [mul_nonneg hc.le (sq_nonneg (s t-se))]

end OverlappingSiphonInvasion
