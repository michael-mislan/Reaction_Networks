import proofs.CoreCouplingGlobal.PhysicalPerron

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff BoundedContinuousFunction

theorem perron_evaluation_norm (v : PerronSpace) (t : ℝ) :
    ‖(fun i => v i t : ResponseVector)‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
  intro i
  exact (v i).norm_coe_le_norm t |>.trans (norm_le_pi_norm v i)

theorem weighted_physical_norm (C : ResponseVector ≃L[ℝ] ResponseVector)
    (β : ℝ) (v : PerronSpace) (t : ℝ) :
    ‖C (Real.exp (-β*t) • (fun i => v i t))‖ ≤
      (‖C.toContinuousLinearMap‖*‖v‖)*Real.exp (-β*t) := by
  calc
    _ ≤ ‖C.toContinuousLinearMap‖*‖Real.exp (-β*t) • (fun i => v i t)‖ :=
      C.toContinuousLinearMap.le_opNorm _
    _ = ‖C.toContinuousLinearMap‖*(Real.exp (-β*t)*‖(fun i => v i t : ResponseVector)‖) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    _ ≤ ‖C.toContinuousLinearMap‖*(Real.exp (-β*t)*‖v‖) := by
      gcongr
      exact perron_evaluation_norm v t
    _ = _ := by ring

theorem weighted_physical_uniform_norm (C : ResponseVector ≃L[ℝ] ResponseVector)
    (β : ℝ) (hβ : 0 < β) (v : PerronSpace) (t : ℝ) (ht : 0 ≤ t) :
    ‖C (Real.exp (-β*t) • (fun i => v i t))‖ ≤ ‖C.toContinuousLinearMap‖*‖v‖ := by
  have he : Real.exp (-β*t) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) ht)
  exact (weighted_physical_norm C β v t).trans (by
    simpa using mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem weighted_physical_tendsto (C : ResponseVector ≃L[ℝ] ResponseVector)
    (β : ℝ) (hβ : 0 < β) (v : PerronSpace) (p : ResponseVector)
    (Y : ℝ → ResponseVector)
    (hY : ∀ t, 0 ≤ t → Y t=p+C (Real.exp (-β*t) • (fun i => v i t))) :
    Tendsto Y atTop (𝓝 p) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have he : Tendsto (fun t : ℝ => Real.exp (-β*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hβ))
  have hlim : Tendsto (fun t => (‖C.toContinuousLinearMap‖*‖v‖)*Real.exp (-β*t))
      atTop (𝓝 0) := by simpa using he.const_mul (‖C.toContinuousLinearMap‖*‖v‖)
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg (Y t-p))) ?_ hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [hY t ht,add_sub_cancel_left]
  exact weighted_physical_norm C β v t

/-- Every sufficiently small parameter gives an actual physical trajectory
inside any prescribed neighborhood of the middle, positive for all future time
and convergent to the middle. This is a constructed subset of the stable set;
coverage by that subset remains a separate theorem. -/
theorem middle_positive_trapped_perron_family (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
    ∃ hC : MiddlePerronCoordinates e s μ C,
    ∃ ψ : StableData → PerronSpace, ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧
      HasFDerivAt ψ (perronLinear μ (1/4) hC.shiftedStable) 0 ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ ξ in 𝓝 (0:StableData), ∃ Y : ℝ → ResponseVector,
        (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
        (∀ t, 0 ≤ t → Y t ∈ positiveDomain ∧ dist (Y t) (encodeState s) < ε) ∧
        Tendsto Y atTop (𝓝 (encodeState s)) ∧
        (∀ i : Fin 3, C.symm (Y 0-encodeState s) i.castSucc=ξ i) ∧
        ∀ t, 0 ≤ t → Y t=encodeState s+
          C (Real.exp (-(1/4:ℝ)*t) • (fun i => ψ ξ i t)) := by
  obtain ⟨μ,C,hC,ψ,hzero,hcd,hd,htraj⟩ := middle_actual_perron_family e he hu s hs hss hz
  refine ⟨μ,C,hC,ψ,hzero,hcd,hd,?_⟩
  intro ε hε
  have hp : encodeState s ∈ positiveDomain := by
    simpa only [positiveDomain,mem_setOf_eq,decode_encodeState] using hs
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.1 positiveDomain_isOpen (encodeState s) hp
  have hm : 0 < min r ε := lt_min hr hε
  have hsmall : ∀ᶠ ξ in 𝓝 (0:StableData),
      ‖C.toContinuousLinearMap‖*‖ψ ξ‖ < min r ε := by
    have hc : ContinuousAt (fun ξ => ‖C.toContinuousLinearMap‖*‖ψ ξ‖) 0 :=
      continuousAt_const.mul hcd.continuousAt.norm
    have hh := hc.eventually_lt_const (show ‖C.toContinuousLinearMap‖*‖ψ 0‖ < min r ε by
      simpa [hzero] using hm)
    exact hh
  filter_upwards [htraj,hsmall] with ξ hξ hξsmall
  obtain ⟨Y,hY,hinit,hrep⟩ := hξ
  refine ⟨Y,hY,?_,weighted_physical_tendsto C (1/4) (by norm_num)
    (ψ ξ) (encodeState s) Y hrep,hinit,hrep⟩
  intro t ht
  have hd : dist (Y t) (encodeState s) < min r ε := by
    rw [dist_eq_norm,hrep t ht,add_sub_cancel_left]
    exact (weighted_physical_uniform_norm C (1/4) (by norm_num) (ψ ξ) t ht).trans_lt hξsmall
  exact ⟨hball (hd.trans_le (min_le_left _ _)),hd.trans_le (min_le_right _ _)⟩

end CoreCouplingGlobal
