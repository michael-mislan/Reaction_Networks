import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace SerialTransferSelection

/-- Log count odds equal log size odds minus the mean-size phase. -/
theorem count_size_phase_identity (BH BL CH CL : ℝ)
    (hBH : 0 < BH) (hBL : 0 < BL) (hCH : 0 < CH) (hCL : 0 < CL) :
    Real.log (CH / CL) = Real.log (BH / BL) -
      Real.log ((BH / CH) / (BL / CL)) := by
  simp only [Real.log_div (ne_of_gt hBH) (ne_of_gt hBL),
    Real.log_div (ne_of_gt hCH) (ne_of_gt hCL),
    Real.log_div (ne_of_gt (div_pos hBH hCH)) (ne_of_gt (div_pos hBL hCL)),
    Real.log_div (ne_of_gt hBH) (ne_of_gt hCH),
    Real.log_div (ne_of_gt hBL) (ne_of_gt hCL)]
  ring

/-- The mean-size phase lies between minus and plus log two. -/
theorem mean_size_phase_bounds (N x y : ℝ) (hN : 0 < N)
    (hx : N ≤ x) (hx' : x ≤ 2*N) (hy : N ≤ y) (hy' : y ≤ 2*N) :
    -Real.log 2 ≤ Real.log (x/y) ∧ Real.log (x/y) ≤ Real.log 2 := by
  have hxp : 0 < x := hN.trans_le hx
  have hyp : 0 < y := hN.trans_le hy
  have hlo : (1/2 : ℝ) ≤ x/y := (le_div_iff₀ hyp).mpr (by linarith)
  have hhi : x/y ≤ 2 := (div_le_iff₀ hyp).mpr (by linarith)
  constructor
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hlo
    simpa [Real.log_div, Real.log_one] using h
  · exact Real.log_le_log (div_pos hxp hyp) hhi

/-- Only endpoint phases survive the sum, irrespective of intermediate phases. -/
theorem phase_corrected_cumulative_gain (B C d g : ℕ → ℝ) (m : ℕ) (D : ℝ)
    (hid : ∀ k, C k = B k - d k)
    (hstep : ∀ k < m, g k ≤ B (k+1)-B k)
    (hstart : -D ≤ d 0) (hend : d m ≤ D) :
    (∑ k ∈ Finset.range m, g k)-2*D ≤ C m-C 0 := by
  have ht : ∀ n ≤ m, (∑ k ∈ Finset.range n, g k) ≤ B n-B 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp := ih (by omega)
      have hs := hstep n (by omega)
      linarith
  have h := ht m le_rfl
  rw [hid m, hid 0]
  linarith

theorem newborn_phase_corrected_cumulative_gain (B C d g : ℕ → ℝ) (m : ℕ) (D : ℝ)
    (hid : ∀ k, C k = B k - d k)
    (hstep : ∀ k < m, g k ≤ B (k+1)-B k)
    (hstart : d 0 = 0) (hend : d m ≤ D) :
    (∑ k ∈ Finset.range m, g k)-D ≤ C m-C 0 := by
  have ht : ∀ n ≤ m, (∑ k ∈ Finset.range n, g k) ≤ B n-B 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp := ih (by omega)
      have hs := hstep n (by omega)
      linarith
  have h := ht m le_rfl
  rw [hid m, hid 0, hstart]
  linarith

end SerialTransferSelection
