import proofs.CoreCouplingCAC.Dynamics
import proofs.CoreCouplingCAC.GlobalExistence

namespace CoreCouplingCAC

theorem dynamics_contDiff (p : Rates) : ContDiff ℝ 1 (dynamics p) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [dynamics] <;> fun_prop

/-- A globally solvable extension agrees with the actual polynomial field on
the entire ball containing both certified neighborhoods. -/
theorem exists_global_extension (p : Rates) :
    ∃ f : (Fin 4 → ℝ) → (Fin 4 → ℝ),
      (∀ x, ‖x‖ ≤ 100 → f x = dynamics p x) ∧
      (∀ x₀, ∃ x : ℝ → Fin 4 → ℝ, x 0 = x₀ ∧ ∀ t, HasDerivAt x (f (x t)) t) := by
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨100,200,by norm_num,by norm_num⟩
  let f : (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun x => b x • dynamics p x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (dynamics_contDiff p)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  refine ⟨f,?_,?_⟩
  · intro x hx
    have hb : b x = 1 := b.one_of_mem_closedBall (by simpa [b,dist_zero_right] using hx)
    simp [f,hb]
  · intro x₀
    exact bounded_lipschitz_global_solution f K ⟨max C 0,le_max_right _ _⟩ hK
      (fun x => (hC x).trans (le_max_left _ _)) x₀

end CoreCouplingCAC
