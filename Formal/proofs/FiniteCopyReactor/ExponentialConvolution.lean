import proofs.RandomViability.ExponentialLaplace
import Mathlib.MeasureTheory.Group.Integral

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Exponential waiting time written in residual-time coordinates for a causal payoff. -/
theorem exponential_residual_integral (q T : ℝ) (F : ℝ → ℝ≥0∞)
    (hm : Measurable F) (hn : ∀ t < 0,F t=0) :
    (∫⁻ w,F (T-w) ∂expMeasure q)=
      ∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (q*Real.exp (-q*(T-u)))*F u := by
  change (∫⁻ w,F (T-w) ∂volume.withDensity (exponentialPDF q))=_
  have hmD : Measurable (exponentialPDF q) := (measurable_exponentialPDFReal q).ennreal_ofReal
  have hmF : Measurable (fun w : ℝ => F (T-w)) := hm.comp (measurable_const.sub measurable_id)
  rw [lintegral_withDensity_eq_lintegral_mul volume hmD hmF]
  have he (w : ℝ) : exponentialPDF q w*F (T-w)=
      (Set.Icc 0 T).indicator (fun w => ENNReal.ofReal (q*Real.exp (-q*w))*F (T-w)) w := by
    by_cases h0 : 0 ≤ w
    · rw [exponentialPDF_of_nonneg h0]
      by_cases hT : w ≤ T
      · rw [Set.indicator_of_mem (show w ∈ Set.Icc 0 T from ⟨h0,hT⟩),neg_mul]
      · rw [hn (T-w) (by linarith),mul_zero,Set.indicator_of_notMem (by simpa only [Set.mem_Icc,not_and] using fun _ => hT)]
    · rw [exponentialPDF_of_neg (lt_of_not_ge h0),zero_mul,
        Set.indicator_of_notMem (fun h => h0 h.1)]
  simp only [Pi.mul_apply,he]
  rw [lintegral_indicator measurableSet_Icc]
  let G := fun u : ℝ => ENNReal.ofReal (q*Real.exp (-q*(T-u)))*F u
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hp : (fun w : ℝ => T-w) ⁻¹' Set.Icc 0 T=Set.Icc 0 T := by
    ext w
    simp only [Set.mem_preimage,Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have hh := (volume.measurePreserving_sub_left T).setLIntegral_comp_preimage
    (s := Set.Icc 0 T) measurableSet_Icc hG
  rw [hp] at hh
  have hi : (∫⁻ w in Set.Icc 0 T,ENNReal.ofReal (q*Real.exp (-q*w))*F (T-w))=
      ∫⁻ u in Set.Icc 0 T,G u := by
    convert hh using 1
    simp only [G,sub_sub_cancel]
  rw [restrict_Ioc_eq_restrict_Icc]
  exact hi

end
end FiniteCopyReactor
