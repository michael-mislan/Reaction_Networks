import proofs.CompositionalMemory.FrozenCountTrajectory
import proofs.CompositionalMemory.FiniteRestriction
import proofs.CompositionalMemory.RetainedModular
import proofs.CompositionalMemory.JumpSelfPadding

namespace CompositionalMemory
open Classical FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

/-- Restricting the unbounded frozen source gives the retained source generator exactly. -/
theorem frozen_restriction_generator {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (D : Finset (ModularCountState k))
    (hD : ∀ s ∈ D,0 < s.2) (H : StoppedModularState D → ℝ) (s : StoppedModularState D) :
    (finiteRestrictionModel (frozenCountNext N) (frozenCountRate γ w N)
      (frozen_count_rate_nonneg γ w hγ hw N) D).generator H s=
      (retainedModularModel γ w hγ hw N D).generator H s := by
  cases s with
  | none => simp [FiniteJumpModel.generator,finiteRestrictionModel,retainedModularModel]
  | some s =>
    have hp := hD s.val s.property
    by_cases ht : s.val.2 < 2*(k*N)
    · simp [FiniteJumpModel.generator,finiteRestrictionModel,retainedModularModel,
        frozenCountNext,frozenCountRate,Fintype.sum_sum_type,hp,ht,s.property]
    · simp [FiniteJumpModel.generator,finiteRestrictionModel,retainedModularModel,
        frozenCountNext,frozenCountRate,hp,ht,s.property]

theorem frozen_restriction_uniformize {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (D : Finset (ModularCountState k))
    (hD : ∀ s ∈ D,0 < s.2) (q : ℝ) (hq : 0 < q)
    (hF : ∀ s,(finiteRestrictionModel (frozenCountNext N) (frozenCountRate γ w N)
      (frozen_count_rate_nonneg γ w hγ hw N) D).total s ≤ q)
    (hR : ∀ s,(retainedModularModel γ w hγ hw N D).total s ≤ q) :
    (finiteRestrictionModel (frozenCountNext N) (frozenCountRate γ w N)
      (frozen_count_rate_nonneg γ w hγ hw N) D).uniformize q hq hF=
      (retainedModularModel γ w hγ hw N D).uniformize q hq hR := by
  apply finiteKernel_eq_of_prob
  funext x y
  let f : StoppedModularState D → ℝ := fun z => if z=y then 1 else 0
  have hs (P : FiniteKernel (StoppedModularState D)) : P.step f x=P.prob x y := by
    simp [FiniteKernel.step,f]
  have he : ((finiteRestrictionModel (frozenCountNext N) (frozenCountRate γ w N)
      (frozen_count_rate_nonneg γ w hγ hw N) D).uniformize q hq hF).step f x=
      ((retainedModularModel γ w hγ hw N D).uniformize q hq hR).step f x := by
    rw [FiniteJumpModel.uniformize_step,FiniteJumpModel.uniformize_step,
      frozen_restriction_generator γ w hγ hw N D hD]
  rw [hs,hs] at he
  exact he

end
end CompositionalMemory
