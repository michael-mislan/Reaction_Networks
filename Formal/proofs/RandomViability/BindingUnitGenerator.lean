import proofs.RandomViability.BindingMoietyDrift
import proofs.RandomViability.BindingResourceExponential

namespace RandomViability.Binding
noncomputable section
open Classical
open scoped BigOperators

def unitObs (side : Bool) (N : Counts) : ℝ := if side then uCount N else wCount N
def unitMark (side : Bool) (j : Fin 18) : ℝ := if side then uUnitJump j else wUnitJump j
def literalGenerator (N : Counts) (V eps k r : ℝ) (f : Counts → ℝ) : ℝ :=
  ∑ j,countRate N V eps k r j*(f (countNext N j)-f N)

theorem unit_actual_jump (side : Bool) (N : Counts) (j : Fin 18)
    (hf : ∀ i,reactants j i ≤ N i) :
    unitObs side (countNext N j)-unitObs side N = unitMark side j := by
  cases side
  · exact (next_linear_difference N j wUnits hf).trans (w_units_stoich j)
  · exact (next_linear_difference N j uUnits hf).trans (u_units_stoich j)

theorem unit_mark_drift (side : Bool) (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*unitMark side j) = V-unitObs side N := by
  cases side
  · change (∑ j,countRate N V eps k r j*wUnitJump j) = V-wCount N
    simpa only [wCount,rated_linear_jump,w_units_stoich] using wCount_actual_drift N V eps k r
  · change (∑ j,countRate N V eps k r j*uUnitJump j) = V-uCount N
    simpa only [uCount,rated_linear_jump,u_units_stoich] using uCount_actual_drift N V eps k r

theorem unit_mark_quadratic (side : Bool) (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*(unitMark side j)^2) ≤ V+2*unitObs side N := by
  cases side
  · exact wCount_quadratic_bound N V eps k r
  · exact uCount_quadratic_bound N V eps k r

theorem unit_mark_bound (side : Bool) (j : Fin 18) : |unitMark side j| ≤ (2:ℝ) := by
  cases side
  · exact wUnitJump_bound j
  · exact uUnitJump_bound j

theorem unit_exponential_generator (side : Bool) (N : Counts) (V eps k r θ b : ℝ) :
    literalGenerator N V eps k r (fun X => Real.exp (θ*(unitObs side X-b))) =
      Real.exp (θ*(unitObs side N-b)) *
      (∑ j,countRate N V eps k r j*(Real.exp (θ*unitMark side j)-1)) := by
  rw [literalGenerator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : countRate N V eps k r j = 0
  · simp [hz]
  · have hj := unit_actual_jump side N j (rate_support N V eps k r j hz)
    have he : unitObs side (countNext N j) = unitObs side N+unitMark side j := by linarith
    rw [he,show θ*(unitObs side N+unitMark side j-b) =
      θ*(unitObs side N-b)+θ*unitMark side j by ring,Real.exp_add]
    ring

theorem unit_exponential_tilt (side : Bool) (N : Counts) (V eps k r θ : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hθ : |θ| ≤ 1/100) :
    (∑ j,countRate N V eps k r j*(Real.exp (θ*unitMark side j)-1)) ≤
      θ*(V-unitObs side N)+(3/5)*θ^2*(V+2*unitObs side N) :=
  moiety_exponential_tilt (countRate N V eps k r) (unitMark side) V (unitObs side N) θ
    (countRate_nonneg N V eps k r hV heps hk hr) (unit_mark_bound side) hθ
    (unit_mark_drift side N V eps k r) (unit_mark_quadratic side N V eps k r)

/-- Away from the dangerous resource boundary, the positive generator is
paid by its exponentially small value and the literal total-rate cap. -/
theorem unit_exponential_small_value (side : Bool) (N : Counts) (V eps k r θ b C : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hθ : |θ| ≤ 1/100) (hsmall : θ*(unitObs side N-b) ≤ C) :
    literalGenerator N V eps k r (fun X => Real.exp (θ*(unitObs side X-b))) ≤
      Real.exp (C+1/50)*(∑ j,countRate N V eps k r j) := by
  rw [literalGenerator,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : countRate N V eps k r j = 0
  · simp [hz]
  · have hj := unit_actual_jump side N j (rate_support N V eps k r j hz)
    have ha : θ*unitMark side j ≤ 1/50 := by
      calc
        _ ≤ |θ*unitMark side j| := le_abs_self _
        _ = |θ| * |unitMark side j| := abs_mul _ _
        _ ≤ (1/100)*2 := mul_le_mul hθ (unit_mark_bound side j) (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hx : Real.exp (θ*(unitObs side (countNext N j)-b)) ≤ Real.exp (C+1/50) := by
      apply Real.exp_le_exp.mpr
      have he : unitObs side (countNext N j) = unitObs side N+unitMark side j := by linarith
      rw [he]
      nlinarith
    have he : Real.exp (θ*(unitObs side (countNext N j)-b))-
        Real.exp (θ*(unitObs side N-b)) ≤ Real.exp (C+1/50) := by
      linarith [Real.exp_pos (θ*(unitObs side N-b))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he
      (countRate_nonneg N V eps k r hV heps hk hr j)

end
end RandomViability.Binding
