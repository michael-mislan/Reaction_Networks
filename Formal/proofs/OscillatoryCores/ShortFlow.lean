import proofs.OscillatoryCores.FlowRegularity

namespace OscillatoryCores

open Set
open scoped NNReal

/-- Produce an actual short-time flow and its C1 endpoint maps. Neither a
trajectory nor a variational solution is an assumption of this theorem. -/
theorem exists_short_c1_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (D : E → E →L[ℝ] E) (T K L M : ℝ≥0)
    (hf : LipschitzWith K f) (hD : LipschitzWith L D)
    (hderiv : ∀ x, HasFDerivAt f (D x) x)
    (hbound : ∀ x, ‖f x‖ ≤ M) (hshort : (2*K)*T ≤ 1) :
    ∃ X : E → ℝ → E,
      (∀ x, X x 0 = x) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T →
        HasDerivWithinAt (X x) (f (X x t)) (Icc (0 : ℝ) T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 1 (fun x => X x t)) := by
  obtain ⟨X, hX⟩ := Bressan.exists_odeTrajectoryOn_Icc_of_global_bounded_lipschitz
    (fun _ => f) T K M (fun _ => hf)
    (fun _ => continuousOn_const) (fun _ _ x => hbound x)
  have hzero (x) := (hX x).1
  have hflow (x t) (ht : t ∈ Icc (0 : ℝ) T) := (hX x).2 t ht
  have hex (x : E) : ∃ J : ℝ → E →L[ℝ] E,
      J 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt J ((D (X x t)).comp (J t)) (Icc (0 : ℝ) T) t := by
    apply Bressan.exists_variationalOn_Icc_of_two_mul_le_one
      (fun t => D (X x t)) T K
    · exact hD.continuous.comp_continuousOn (HasDerivWithinAt.continuousOn (hflow x))
    · intro t _
      rw [← (hderiv (X x t)).fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ hf
    · exact hshort
  choose J hJzero hJ using hex
  have hJeval (x h t) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt (fun q => J x q h) (D (X x t) (J x t h))
        (Icc (0 : ℝ) T) t := by
    simpa using (ContinuousLinearMap.apply ℝ E h).hasFDerivAt.comp_hasDerivWithinAt
      t (hJ x t ht)
  have hF := Bressan.hasFDerivAt_trajectory_of_lipschitz_fderiv_and_variational
    (fun _ => f) (fun _ => D) X J T K L (fun _ => hf) (fun _ => hderiv)
    (fun _ => hD) hflow hzero hJeval hJzero
  refine ⟨X, hzero, hflow, fun t ht => ?_⟩
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨fun x => J x t,
    variational_endpoint_continuous (fun _ => f) (fun _ => D) X J T K L
      (fun _ => hf) (fun _ => hderiv) (fun _ => hD) hflow hzero hJ hJzero ht,
    fun x => hF x t ht⟩

end OscillatoryCores
