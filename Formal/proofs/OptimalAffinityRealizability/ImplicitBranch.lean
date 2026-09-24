import proofs.OptimalAffinityRealizability.ReducedJacobian
import Mathlib.Analysis.Calculus.Implicit

namespace OptimalAffinityRealizability

open Filter
open scoped Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The local branch obtained by inverting an augmented square stationarity map
along one target direction. -/
def inverseFunctionBranch (F : E → E) (a : E) (D : E ≃L[ℝ] E)
    (hF : HasStrictFDerivAt F (D : E →L[ℝ] E) a) (direction : E) (s : ℝ) : E :=
  hF.localInverse F D a (F a + s • direction)

omit [CompleteSpace E] in
theorem affineLine_tendsto (b direction : E) :
    Tendsto (fun s : ℝ => b + s • direction) (𝓝 0) (𝓝 b) := by
  have hb : ContinuousAt (fun _ : ℝ => b) 0 := continuousAt_const
  have hs : ContinuousAt (fun s : ℝ => s) 0 := continuousAt_id
  have hd : ContinuousAt (fun _ : ℝ => direction) 0 := continuousAt_const
  simpa using (hb.add (hs.smul hd)).tendsto

theorem inverseFunctionBranch_zero (F : E → E) (a : E) (D : E ≃L[ℝ] E)
    (hF : HasStrictFDerivAt F (D : E →L[ℝ] E) a) (direction : E) :
    inverseFunctionBranch F a D hF direction 0 = a := by
  change hF.localInverse F D a (F a + (0 : ℝ) • direction) = a
  rw [zero_smul, add_zero]
  exact hF.localInverse_apply_image

theorem inverseFunctionBranch_eventually_equation (F : E → E) (a : E)
    (D : E ≃L[ℝ] E) (hF : HasStrictFDerivAt F (D : E →L[ℝ] E) a)
    (direction : E) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      F (inverseFunctionBranch F a D hF direction s) = F a + s • direction := by
  exact (affineLine_tendsto (F a) direction).eventually hF.eventually_right_inverse

theorem inverseFunctionBranch_tendsto (F : E → E) (a : E) (D : E ≃L[ℝ] E)
    (hF : HasStrictFDerivAt F (D : E →L[ℝ] E) a) (direction : E) :
    Tendsto (inverseFunctionBranch F a D hF direction) (𝓝 0) (𝓝 a) := by
  unfold inverseFunctionBranch
  exact hF.localInverse_tendsto.comp (affineLine_tendsto (F a) direction)

def scalarDirectionMap (direction : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight direction

theorem inverseFunctionBranch_hasStrictFDerivAt (F : E → E) (a : E)
    (D : E ≃L[ℝ] E) (hF : HasStrictFDerivAt F (D : E →L[ℝ] E) a)
    (direction : E) :
    HasStrictFDerivAt (inverseFunctionBranch F a D hF direction)
      ((D.symm : E →L[ℝ] E).comp (scalarDirectionMap direction)) 0 := by
  have hline : HasStrictFDerivAt (fun s : ℝ => F a + s • direction)
      (scalarDirectionMap direction) 0 := by
    change HasStrictFDerivAt (fun s : ℝ => F a + s • direction)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight direction) 0
    exact ((hasStrictFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const direction).const_add (F a)
  have hinv : HasStrictFDerivAt (hF.localInverse F D a) (D.symm : E →L[ℝ] E)
      (F a + (0 : ℝ) • direction) := by
    simpa using hF.to_localInverse
  change HasStrictFDerivAt (fun s : ℝ =>
    hF.localInverse F D a (F a + s • direction)) _ 0
  exact hinv.comp 0 hline

end
end OptimalAffinityRealizability
