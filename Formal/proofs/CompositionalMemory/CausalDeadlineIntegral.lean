import proofs.CompositionalMemory.CausalExponential

namespace CompositionalMemory
open Classical MeasureTheory
open scoped ENNReal
noncomputable section

theorem causalConv_deadline_integral (q T : ℝ) (H : ℝ → ℝ≥0∞)
    (hH : ∀ t,t < 0 → H t=0) :
    renewalConv (causalExp q) H T =
      ∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (Real.exp (-q*(T-u)))*H u := by
  have he : renewalConv (causalExp q) H T=∫⁻ u,causalExp q (T-u)*H u := by
    have hh := lintegral_sub_left_eq_self (fun u : ℝ => causalExp q u*H (T-u)) T (μ := volume)
    convert hh.symm using 1
    simp only [sub_sub_cancel]
  rw [he]
  have hi (u : ℝ) : causalExp q (T-u)*H u =
      (Set.Icc 0 T).indicator (fun u => ENNReal.ofReal (Real.exp (-q*(T-u)))*H u) u := by
    by_cases hu : 0 ≤ u
    · by_cases ht : u ≤ T <;> simp [causalExp,sub_nonneg,Set.indicator,Set.mem_Icc,hu,ht]
    · have hz := hH u (lt_of_not_ge hu)
      simp [hz,Set.indicator,Set.mem_Icc,hu]
  simp_rw [hi]
  rw [lintegral_indicator measurableSet_Icc]
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := T)).symm]

end
end CompositionalMemory
