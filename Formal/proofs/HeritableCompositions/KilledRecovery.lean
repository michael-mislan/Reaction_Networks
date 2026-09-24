import proofs.HeritableCompositions.AffineRecovery
import proofs.HeritableCompositions.StoppedGrowth
import proofs.HeritableCompositions.GrowingEnvelope

namespace HeritableCompositions
open FiniteCopy

/-- D contains only pre-division states; departure is killed with observable zero. -/
theorem killed_growth_affine_bound (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ)
    (D : Finset Compartment) (hD : ∀ s ∈ D, s.2 < 2*N)
    (f : Compartment → ℝ) (hf : ∀ s, 0 ≤ f s) (k C : ℝ)
    (hk0 : 0 ≤ k) (hC : 0 ≤ C)
    (hgen : ∀ s ∈ D, compartmentGenerator γ f s ≤ -k*f s+k*C)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (stoppedGrowthModel γ hγ N D).total s ≤ q) (hk : k ≤ q)
    (A : Set (StoppedCompartment D)) (a : ℝ)
    (hA : ∀ s ∈ A, a ≤ growthObservable D f 0 s)
    (s : {s : Compartment // s ∈ D}) :
    a*((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some s) ≤ Real.exp (-k*(t : ℝ))*f s.val+C := by
  classical
  apply uniformized_event_affine (stoppedGrowthModel γ hγ N D) q t hq hclock
    A (growthObservable D f 0) a k C
  · intro x
    cases x with
    | none => exact le_rfl
    | some x => exact hf x.val
  · exact hA
  · exact hk
  · exact hC
  · intro x
    cases x with
    | none => simpa [stoppedGrowthModel,FiniteJumpModel.generator,growthObservable] using mul_nonneg hk0 hC
    | some x =>
      exact (stopped_growth_generator_le γ hγ N D f 0
        (fun y _ _ r _ => hf (nextCompartment y r)) x (hD x.val x.property)).trans
          (hgen x.val x.property)

theorem fixed_time_recovery_tail (u p W : ℝ) (hu : 0 ≤ u)
    (hW : W ≤ Real.exp (4*u))
    (hbound : Real.exp u*p ≤ Real.exp (-6*u)*W+2*Real.exp (u/2)) :
    p ≤ 3*Real.exp (-u/2) := by
  have hm := mul_le_mul_of_nonneg_left hW (Real.exp_pos (-6*u)).le
  have he1 : Real.exp (-6*u)*Real.exp (4*u) = Real.exp (-2*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he1] at hm
  have he2 : Real.exp (-2*u) ≤ Real.exp (u/2) := Real.exp_le_exp.mpr (by linarith only [hu])
  have hb : Real.exp u*p ≤ 3*Real.exp (u/2) := by linarith only [hbound,hm,he2]
  have he3 : Real.exp u*(3*Real.exp (-u/2)) = 3*Real.exp (u/2) := by
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring
  rw [← he3] at hb
  nlinarith only [hb,Real.exp_pos u]

end HeritableCompositions
