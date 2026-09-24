import proofs.FiniteCopyReactor.KernelEmbedding
import proofs.CompositionalMemory.CanonicalFiniteLaw

namespace InheritedCellAssay
noncomputable section
open FiniteCopy FiniteCopyReactor CompositionalMemory

/-- A one-step projection identifies all finite-clock expectations. It needs
    no equality of rates at states outside the observed live set. -/
theorem marked_law_finite_projection {α β γ : Type*} [Fintype β] [Fintype γ]
    (P : MarkedKernel α β) (K : FiniteKernel γ) (φ : α → γ)
    (hs : ∀ (g : γ → ℝ) x,
      (∑ b, P.prob x b * g (φ (P.next x b))) = K.step g (φ x))
    (f : γ → ℝ) (n : ℕ) (x : α) (z : ℝ) :
    P.law n (fun y _ => f (φ y)) x z = K.steps n f (φ x) := by
  induction n generalizing x z with
  | zero => rfl
  | succ n ih =>
    change (∑ b, P.prob x b * P.law n (fun y _ => f (φ y))
      (P.next x b) (z + P.mark b)) = _
    simp_rw [ih]
    exact hs (K.steps n f) x

theorem clock_finite_projection {α β γ δ : Type*} [Fintype β] [Fintype γ]
    [Fintype δ] [DecidableEq γ]
    (P : MarkedKernel α β) (M : FiniteJumpModel γ δ) (φ : α → γ)
    (q T : NNReal) (hq : 0 < (q : ℝ)) (hb : ∀ y, M.total y ≤ q)
    (hs : ∀ (g : γ → ℝ) x,
      (∑ b, P.prob x b * g (φ (P.next x b))) =
      (M.uniformize q hq hb).step g (φ x))
    (f : γ → ℝ) (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (x : α) :
    clockEndpoint P q T (fun y => ENNReal.ofReal (f (φ y))) x =
      ENNReal.ofReal (finiteTimeExpectation M T f (φ x)) := by
  rw [clock_endpoint_real_nn P q T (fun y => f (φ y)) 1 (fun y => hf (φ y)) x 0]
  rw [finite_time_eq_uniformized M q T hq hb]
  congr 1
  unfold MarkedKernel.poissonized FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [marked_law_finite_projection P _ φ hs]

end
end InheritedCellAssay
