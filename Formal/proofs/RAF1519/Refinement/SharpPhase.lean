import proofs.RAF1519.Refinement.Phase
import proofs.RAF1519.Refinement.CountSource
import proofs.RAF1519.Refinement.CountRateBinding

namespace RAF1519.Refinement
noncomputable section

theorem refined_sharp_phase (r d : ℝ) (c : State) (hc : ∀ i, 0 ≤ c i)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : materialA c ≤ 11/10) (hB : materialB c ≤ 11/10) :
    -48*c 2+20*c 3+38*c 5 ≤ field r d (1/100) (1/100) c 2 ∧
    -43*c 3+20*c 4 ≤ field r d (1/100) (1/100) c 3 ∧
    -41*c 4+2*c 5 ≤ field r d (1/100) (1/100) c 4 := by
  have hb := coordinate_bound c hc hA hB
  have hsum : c 0+c 2 ≤ 11/10 := by
    dsimp [materialA,free,ProductiveRecovery.A] at hA
    linarith [hc 3,hc 4,hc 5,hc 6]
  have hux := mul_le_mul_of_nonneg_right hsum (hc 2)
  have hwc := mul_le_mul_of_nonneg_right (hb 1) (hc 3)
  have hrx := mul_le_mul_of_nonneg_right hr' (sq_nonneg (c 2))
  have hrl := mul_le_mul_of_nonneg_right hr (hc 5)
  have hdx := mul_le_mul_of_nonneg_right hd' (hc 2)
  have him : 0 ≤ (1/500000000:ℝ)*c 0*c 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (hc 0)) (hc 1)
  have hxu := mul_nonneg (hc 2) (hc 0)
  have hcw := mul_nonneg (hc 3) (hc 1)
  have hret : 0 ≤ d*c 6 := mul_nonneg hd (hc 6)
  simp [field,firstFlux,ProductiveRecovery.flux,free]
  constructor
  · nlinarith [hc 2]
  constructor
  · nlinarith [hc 3]
  · nlinarith

/-- The final row uses nonnegative falling-factorial production, including zero
    and one molecule, rather than a fictitious quadratic production term. -/
theorem count_sharp_phase (r d V : ℝ) (N : Fin 7 → ℕ) (hV : 0 < V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : materialA (concentration V N) ≤ 11/10)
    (hB : materialB (concentration V N) ≤ 11/10) :
    let c := concentration V N;
    -48*c 2+20*c 3+38*c 5 ≤ countDrift r d (1/100) (1/100) V c 2 ∧
    -43*c 3+20*c 4 ≤ countDrift r d (1/100) (1/100) V c 3 ∧
    -41*c 4+2*c 5 ≤ countDrift r d (1/100) (1/100) V c 4 ∧
    -24*c 5+20*c 4 ≤ countDrift r d (1/100) (1/100) V c 5 := by
  let c := concentration V N
  have hc : ∀ i, 0 ≤ c i := fun i => div_nonneg (Nat.cast_nonneg _) hV.le
  have hp := refined_sharp_phase r d c hc hr hr' hd hd' hA hB
  have he := count_drift_correction r d (1/100) (1/100) V c
  have he2 := congrFun he 2
  have he3 := congrFun he 3
  have he4 := congrFun he 4
  have he5 := congrFun he 5
  change countDrift r d (1/100) (1/100) V c 2 = field r d (1/100) (1/100) c 2+2*r*c 2/V at he2
  change countDrift r d (1/100) (1/100) V c 3 = field r d (1/100) (1/100) c 3+0 at he3
  change countDrift r d (1/100) (1/100) V c 4 = field r d (1/100) (1/100) c 4+0 at he4
  change countDrift r d (1/100) (1/100) V c 5 = field r d (1/100) (1/100) c 5+(-r)*c 2/V at he5
  have hcorr : 0 ≤ 2*r*c 2/V := div_nonneg (mul_nonneg (by linarith) (hc 2)) hV.le
  have hff : 0 ≤ r*(c 2^2-c 2/V) := by
    change 0 ≤ r*(((N 2:ℝ)/V)^2-((N 2:ℝ)/V)/V)
    rw [falling_factorial_rate]
    exact mul_nonneg (by linarith) (div_nonneg (falling_factorial_nonnegative _) (sq_nonneg V))
  have hrz := mul_le_mul_of_nonneg_right hr' (hc 5)
  dsimp only
  refine ⟨by linarith [hp.1],by linarith [hp.2.1],by linarith [hp.2.2],?_⟩
  change -24*c 5+20*c 4 ≤ countDrift r d (1/100) (1/100) V c 5
  have he5' : countDrift r d (1/100) (1/100) V c 5 =
      20*c 4-3*c 5-r*c 5+r*(c 2^2-c 2/V) := by
    rw [he5]
    simp [field,ProductiveRecovery.flux,free]
    ring
  linarith

end
end RAF1519.Refinement
