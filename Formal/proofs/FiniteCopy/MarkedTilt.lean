import proofs.FiniteCopy.MarkedKernel

namespace FiniteCopy
open scoped NNReal
namespace MarkedKernel
variable {α β : Type*} [Fintype β] (P : MarkedKernel α β)

noncomputable def aliveExponential (alive : Set α) (θ : ℝ) (x : α) (z : ℝ) : ℝ := by
  classical
  exact if x ∈ alive then Real.exp (θ*z) else 0

noncomputable def tiltedRow (alive : Set α) (θ : ℝ) (x : α) : ℝ := by
  classical
  exact ∑ r, P.prob x r*(if P.next x r ∈ alive then Real.exp (θ*P.mark r) else 0)

theorem step_aliveExponential (alive : Set α) (θ : ℝ) (x : α) (z : ℝ) :
    P.step (aliveExponential alive θ) x z = Real.exp (θ*z)*P.tiltedRow alive θ x := by
  classical
  unfold step aliveExponential tiltedRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : P.next x r ∈ alive
  · simp only [hr,ite_true,mul_add,Real.exp_add]
    ring
  · simp [hr]

theorem aliveExponential_decay (alive : Set α) (θ r : ℝ)
    (hrow : ∀ x, P.tiltedRow alive θ x ≤ r*FiniteKernel.eventIndicator alive x) (x : α) (z : ℝ) :
    P.step (aliveExponential alive θ) x z ≤ r*aliveExponential alive θ x z := by
  classical
  rw [P.step_aliveExponential]
  have h := mul_le_mul_of_nonneg_left (hrow x) (Real.exp_pos (θ*z)).le
  by_cases hx : x ∈ alive <;> simpa [aliveExponential,FiniteKernel.eventIndicator,hx,mul_comm] using h

theorem activity_chernoff (alive : Set α) (θ r h : ℝ) (hθ : 0 ≤ θ) (hr : 0 ≤ r)
    (hrow : ∀ x, P.tiltedRow alive θ x ≤ r*FiniteKernel.eventIndicator alive x)
    (t : ℝ≥0) (x : α) (hx : x ∈ alive) :
    P.poissonized t (eventIndicator {s | s.1 ∈ alive ∧ h ≤ s.2}) x 0 ≤
      Real.exp (-θ*h+(t : ℝ)*(r-1)) := by
  classical
  have hA (y : α) (z : ℝ) : eventIndicator {s | s.1 ∈ alive ∧ h ≤ s.2} y z ≤
      Real.exp (-θ*h)*aliveExponential alive θ y z := by
    by_cases hy : y ∈ alive
    · by_cases hz : h ≤ z
      · have he : 1 ≤ Real.exp (-θ*h+θ*z) :=
          Real.one_le_exp_iff.mpr (by nlinarith only [mul_nonneg hθ (sub_nonneg.mpr hz)])
        simpa [eventIndicator,aliveExponential,hy,hz,Real.exp_add] using he
      · simp [eventIndicator,aliveExponential,hy,hz]
        positivity
    · simp [eventIndicator,aliveExponential,hy]
  have hh := P.poissonized_event_decay t {s | s.1 ∈ alive ∧ h ≤ s.2}
    (aliveExponential alive θ) (Real.exp (-θ*h)) r (Real.exp_pos _).le hr hA
    (P.aliveExponential_decay alive θ r hrow) x 0
  simpa [aliveExponential,hx,← Real.exp_add] using hh

end MarkedKernel
end FiniteCopy

