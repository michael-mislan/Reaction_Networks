import proofs.InheritedCellAssay.FiniteClockProjection

namespace MemoryPrediction
noncomputable section
open FiniteCopy FiniteCopyReactor CompositionalMemory

/-- One-step inequalities on a preserved class of observables suffice for
all finite histories. This lemma has no unproved coverage premise. -/
theorem marked_law_lower {α β γ : Type*} [Fintype β] [Fintype γ]
    (P : MarkedKernel α β) (K : FiniteKernel γ) (φ : α → γ)
    (C : (γ → ℝ) → Prop) (hclosed : ∀ g, C g → C (K.step g))
    (hstep : ∀ g, C g → ∀ x, K.step g (φ x) ≤
      ∑ b, P.prob x b * g (φ (P.next x b)))
    (f : γ → ℝ) (hf : C f) (n : ℕ) (x : α) (z : ℝ) :
    K.steps n f (φ x) ≤ P.law n (fun y _ => f (φ y)) x z := by
  have hc (m : ℕ) : C (K.steps m f) := by
    induction m with
    | zero => exact hf
    | succ m ih => exact hclosed _ ih
  induction n generalizing x z with
  | zero => exact le_rfl
  | succ n ih =>
    apply (hstep _ (hc n) x).trans
    exact Finset.sum_le_sum (fun b _ =>
      mul_le_mul_of_nonneg_left (ih (P.next x b) (z+P.mark b)) (P.nonneg x b))

/-- Poisson mixing transports the comparison to physical time at any common
clock rate. Applications must establish the one-step inequality from rates. -/
theorem clock_finite_lower {α β γ δ : Type*} [Fintype β] [Fintype γ]
    [Fintype δ] [DecidableEq γ]
    (P : MarkedKernel α β) (M : FiniteJumpModel γ δ) (φ : α → γ)
    (q T : NNReal) (hq : 0 < (q : ℝ)) (hb : ∀ y, M.total y ≤ q)
    (C : (γ → ℝ) → Prop)
    (hclosed : ∀ g, C g → C ((M.uniformize q hq hb).step g))
    (hstep : ∀ g, C g → ∀ x, (M.uniformize q hq hb).step g (φ x) ≤
      ∑ b, P.prob x b * g (φ (P.next x b)))
    (f : γ → ℝ) (hf : C f) (hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (x : α) :
    ENNReal.ofReal (finiteTimeExpectation M T f (φ x)) ≤
      clockEndpoint P q T (fun y => ENNReal.ofReal (f (φ y))) x := by
  rw [clock_endpoint_real_nn P q T (fun y => f (φ y)) 1 (fun y => hf01 (φ y)) x 0,
    finite_time_eq_uniformized M q T hq hb]
  apply ENNReal.ofReal_le_ofReal
  unfold FiniteKernel.poissonized MarkedKernel.poissonized
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left
      (marked_law_lower P _ φ C hclosed hstep f hf n x 0)
      (poissonWeight_nonneg (q*T) n)
  · exact (M.uniformize q hq hb).nonneg_summable (q*T) f (fun y => (hf01 y).1) (φ x)
  · exact marked_summable P (fun y _ => f (φ y)) 1 (fun y _ => hf01 (φ y)) (q*T) x 0

end
end MemoryPrediction
