import proofs.FiniteCopyReactor.SurvivalResolvent

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

/-- Convolving the scalar survival resolvent preserves its inhomogeneous term. -/
theorem survival_convolution_resolvent (q r T : ℝ) (hrq : r ≤ q)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    positiveConvolution (survivalKernel r) H T=positiveConvolution (survivalKernel q) H T+
      ENNReal.ofReal (q-r)*positiveConvolution (survivalKernel q)
        (positiveConvolution (survivalKernel r) H) T := by
  have he : survivalKernel r=(fun t => survivalKernel q t+
      ENNReal.ofReal (q-r)*positiveConvolution (survivalKernel q) (survivalKernel r) t) :=
    funext (fun t => survival_kernel_resolvent q r t hrq)
  calc
    _ = positiveConvolution (fun t => survivalKernel q t+
        ENNReal.ofReal (q-r)*positiveConvolution (survivalKernel q) (survivalKernel r) t) H T :=
      congrArg (fun K => positiveConvolution K H T) he
    _ = _ := by
      rw [positive_convolution_add_left _ _ H (survival_kernel_measurable q) hH,
        positive_convolution_const_mul_left _ H
          (positive_convolution_measurable _ _ (survival_kernel_measurable q) (survival_kernel_measurable r)) hH,
        positive_convolution_assoc _ _ H (survival_kernel_measurable q) (survival_kernel_measurable r) hH]

/-- The genuine-rate continuation solves the equation containing dummy self events. -/
theorem dummy_renewal_candidate (q r T : ℝ) (hrq : r ≤ q) (a : ℝ≥0∞)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    a*survivalKernel r T+positiveConvolution (survivalKernel r) H T=
      a*survivalKernel q T+positiveConvolution (survivalKernel q) H T+
        ENNReal.ofReal (q-r)*positiveConvolution (survivalKernel q)
          (fun t => a*survivalKernel r t+positiveConvolution (survivalKernel r) H t) T := by
  rw [positive_convolution_add_right _ _ _ (survival_kernel_measurable q)
      (measurable_const.mul (survival_kernel_measurable r)),
    positive_convolution_const_mul _ _ (survival_kernel_measurable q) (survival_kernel_measurable r)]
  rw [survival_kernel_resolvent q r T hrq,survival_convolution_resolvent q r T hrq H hH]
  simp only [mul_add]
  ac_rfl

end
end FiniteCopyReactor
