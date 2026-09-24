import proofs.CompositionalMemory.FiniteTimeDependentCertificate

namespace MemoryPrediction
noncomputable section
open FiniteCopy CompositionalMemory

/-- A checked finite backward solution identifies the actual finite semigroup.
The generator/derivative identity, not a terminal-law premise, drives the proof. -/
theorem finite_backward_identity {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (v : ℝ → α → ℝ)
    (hv : ∀ t x, HasDerivAt (fun u => v u x) (M.generator (v t) x) t)
    (T : NNReal) (x : α) : finiteTimeExpectation M T (v 0) x = v T x := by
  have bound (w : ℝ → α → ℝ)
      (hw : ∀ t x, HasDerivAt (fun u => w u x) (M.generator (w t) x) t) :
      finiteTimeExpectation M T (w 0) x ≤ w T x := by
    let u := fun t y => w ((T : ℝ)-t) y
    let du := fun t y => -M.generator (w ((T : ℝ)-t)) y
    have hd (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) T) (y : α) :
        HasDerivAt (fun r => u r y) (du t y) t := by
      simpa [u,du] using (hw ((T : ℝ)-t) y).comp t
        ((hasDerivAt_id t).const_sub (T : ℝ))
    have hg (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) T) (y : α) :
        du t y+M.generator (u t) y ≤ 0 := by dsimp [du,u]; linarith
    have h := finite_time_dependent_drift_bound M T u du 0 hd hg x
    simpa [u] using h
  apply le_antisymm (bound v hv)
  have hn : ∀ t y, HasDerivAt (fun u => -v u y) (M.generator (fun y => -v t y) y) t := by
    intro t y
    have he : M.generator (fun y => -v t y) y = -M.generator (v t) y := by
      simp only [FiniteJumpModel.generator, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [he]
    exact (hv t y).neg
  have h := bound (fun t y => -v t y) hn
  have he : finiteTimeExpectation M T (fun y => -v 0 y) x =
      -finiteTimeExpectation M T (v 0) x := by
    simp [finiteTimeExpectation, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
  rw [he] at h
  linarith

end
end MemoryPrediction
