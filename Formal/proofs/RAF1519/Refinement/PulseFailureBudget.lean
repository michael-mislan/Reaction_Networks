import proofs.RAF1519.Refinement.PulseProbability
import proofs.RAF1519.Refinement.MarkFailureBudget

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem pulse_error_root_budget (n : ℕ) (V Δ : ℝ) (hV : 0 ≤ V) (hΔ : 0 ≤ Δ) :
    4*n*Real.exp (-V/100000)+n*Real.exp (-V/100000000) ≤
      5*n*Real.exp (-V/(200000000000000*(1+Δ)^3)) := by
  have hm := mark_exponent_root_margin V Δ hV hΔ
  have h1 : -V/100000 ≤ -V/160000000 := by linarith
  have h2 : -V/100000000 ≤ -V/160000000 := by linarith
  have he1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h1.trans hm))
    (show 0 ≤ 4*(n:ℝ) by positivity)
  have he2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h2.trans hm)) (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem graphPulse_preparation_root_failure {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 10000 ≤ V)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    (graphPulsePMF N p).toMeasure {o | ¬CountPrepared V (postPulseState N V p o)} ≤
      5*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))) := by
  have hb := (graphPulse_preparation_failure N V hV p hready).trans
    (ENNReal.ofReal_le_ofReal (pulse_error_root_budget n V Δ (Nat.cast_nonneg _) hΔ))
  simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 5*n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5),ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast] using hb

end
end RAF1519.Refinement
