import proofs.DiagnosticWindows.Spectral

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem poissonized_nonpos (P : FiniteKernel α) (f : α → ℝ)
    (hf : ∀ x, f x ≤ 0) (t : NNReal) (x : α) : P.poissonized t f x ≤ 0 := by
  apply tsum_nonpos
  intro n
  have hs := P.steps_mono hf n x
  rw [P.steps_const] at hs
  exact mul_nonpos_of_nonneg_of_nonpos (poissonWeight_nonneg t n) hs

/-- Dissipation of a source observable proves monotonicity of its exact spectral
formula. This supplies continuous-time coverage for a separating no-window test. -/
theorem spectral_antitone (P : FiniteKernel α) (f : α → ℝ)
    (V : ι → α → ℝ) (r : ι → ℝ)
    (hsum : ∀ x, f x = ∑ i, V i x)
    (heigen : ∀ i x, P.step (V i) x = r i*V i x)
    (hdecay : ∀ x, P.step f x ≤ f x) (x : α) :
    AntitoneOn (fun t : ℝ => ∑ i, Real.exp (t*(r i-1))*V i x) (Set.Ici 0) := by
  let W : ι → α → ℝ := fun i y => (r i-1)*V i y
  let g : α → ℝ := fun y => ∑ i, W i y
  have hg (y : α) : g y ≤ 0 := by
    have he : g y = P.step f y-f y := by
      rw [show f = (fun y => ∑ i, V i y) from funext hsum,step_sum]
      simp_rw [heigen]
      simp only [g,W,Finset.sum_sub_distrib,sub_mul,one_mul]
    rw [he]
    exact sub_nonpos.mpr (hdecay y)
  have hw (i : ι) (y : α) : P.step (W i) y = r i*W i y := by
    dsimp [W]
    rw [P.step_scale,heigen]
    ring
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => ∑ i, Real.exp (s*(r i-1))*V i x)
      (∑ i, Real.exp (t*(r i-1))*W i x) t := by
    apply HasDerivAt.fun_sum
    intro i _
    convert (((hasDerivAt_id t).mul_const (r i-1)).exp).mul_const (V i x) using 1
    simp [W]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun t _ => (hd t).continuousAt.continuousWithinAt
  · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht)
    rw [(hd t).deriv]
    have hs := spectral_survival P g W r (fun _ => rfl) hw ⟨t,ht0⟩ x
    exact hs.symm ▸ poissonized_nonpos P g hg ⟨t,ht0⟩ x

end DiagnosticWindows
