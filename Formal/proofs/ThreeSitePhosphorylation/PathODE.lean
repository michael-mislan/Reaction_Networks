import proofs.ThreeSitePhosphorylation.SourceFlow

namespace ThreeSitePhosphorylation
noncomputable section

def pathContinuation (p : FlowData) (u : SourcePath) (t : ℝ) : ReducedState :=
  p.2+∫ s in (0:ℝ)..t, pathExtension (pathField p.1 u) s

theorem pathContinuation_initial (p : FlowData) (u : SourcePath) :
    pathContinuation p u 0=p.2 := by simp [pathContinuation]

theorem pathContinuation_eq (p : FlowData) (u : SourcePath)
    (hu : pathResidual (p,u)=0) (t : UnitTime) : u t=pathContinuation p u t := by
  change u-constantPath p.2-linearPicard (ContinuousLinearMap.id ℝ ReducedState)
    (pathField p.1 u)=0 at hu
  have hh := sub_eq_iff_eq_add.mp (sub_eq_zero.mp hu)
  rw [add_comm] at hh
  have ht := congrArg (fun v : SourcePath => v t) hh
  exact ht

theorem pathContinuation_derivative (p : FlowData) (u : SourcePath) (t : ℝ) :
    HasDerivAt (pathContinuation p u)
      (p.1.2.2 • rescaledField p.1.1 p.1.2.1 (pathExtension u t)) t := by
  have hc := pathExtension_continuous (pathField p.1 u)
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : pathExtension (pathField p.1 u) t =
      p.1.2.2 • rescaledField p.1.1 p.1.2.1 (pathExtension u t) := by
    exact pathField_apply p.1.1 p.1.2.1 p.1.2.2 u _
  simpa only [pathContinuation,he] using hd.const_add p.2

/-- The constructed integral paths satisfy the actual rescaled ODE, including
one-sided endpoint data. This does not impose periodicity on nearby paths. -/
theorem pathContinuation_solves (p : FlowData) (u : SourcePath)
    (hu : pathResidual (p,u)=0) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (pathContinuation p u)
      (p.1.2.2 • rescaledField p.1.1 p.1.2.1 (pathContinuation p u t)) t := by
  have he : pathExtension u t=pathContinuation p u t := by
    rw [pathExtension,Set.projIcc_of_mem _ ht]
    exact pathContinuation_eq p u hu ⟨t,ht⟩
  simpa only [he] using pathContinuation_derivative p u t

end
end ThreeSitePhosphorylation
