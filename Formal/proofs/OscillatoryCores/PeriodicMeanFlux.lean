import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! Integrate the actual ODE, without substituting an equilibrium. Unnormalized
period integrals suffice for the kernel obstruction, avoiding division by T. -/

namespace OscillatoryCores

open scoped BigOperators
open MeasureTheory

theorem integrated_flux_balanced
    {n m : ℕ} (S : Fin n → Fin m → ℝ)
    (x : ℝ → Fin n → ℝ) (v : ℝ → Fin m → ℝ) (T : ℝ)
    (hv : ∀ j, Continuous (fun t => v t j))
    (hode : ∀ t i, HasDerivAt (fun s => x s i) (∑ j, S i j * v t j) t)
    (hreturn : x T = x 0) (i : Fin n) :
    ∑ j, S i j * (∫ t in (0 : ℝ)..T, v t j) = 0 := by
  have hint (j : Fin m) : IntervalIntegrable (fun t => S i j * v t j) volume 0 T :=
    (continuous_const.mul (hv j)).intervalIntegrable _ _
  have hsum : IntervalIntegrable (fun t => ∑ j, S i j * v t j) volume 0 T := by
    exact (continuous_finsetSum _ (fun j _ => continuous_const.mul (hv j))).intervalIntegrable _ _
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hode t i) hsum
  rw [intervalIntegral.integral_finsetSum (fun j _ => hint j)] at heq
  simp only [intervalIntegral.integral_const_mul] at heq
  simpa only [hreturn, sub_self] using heq

theorem integrated_flux_positive (v : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hv : Continuous v) (hpos : ∀ t, 0 < v t) :
    0 < ∫ t in (0 : ℝ)..T, v t := by
  exact intervalIntegral.integral_pos hT hv.continuousOn
    (fun t _ => (hpos t).le) ⟨0, ⟨le_rfl, hT.le⟩, hpos 0⟩

theorem constant_of_zero_velocity {n : ℕ} (x : ℝ → Fin n → ℝ)
    (hode : ∀ t i, HasDerivAt (fun s => x s i) 0 t) :
    ∀ t, x t = x 0 := by
  intro t
  funext i
  exact is_const_of_deriv_eq_zero
    (fun s => (hode s i).differentiableAt) (fun s => (hode s i).deriv) t 0

end OscillatoryCores
