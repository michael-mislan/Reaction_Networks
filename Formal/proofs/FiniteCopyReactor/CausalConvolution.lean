import proofs.FiniteCopyReactor.ExponentialConvolution
import Mathlib.MeasureTheory.Measure.Prod

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

def positiveConvolution (f g : ℝ → ℝ≥0∞) (T : ℝ) : ℝ≥0∞ := ∫⁻ u,f u*g (T-u)

theorem positive_convolution_measurable (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    Measurable (positiveConvolution f g) := by
  have hm : Measurable (fun p : ℝ × ℝ => f p.2*g (p.1-p.2)) :=
    (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))
  exact hm.lintegral_prod_right'

theorem positive_convolution_comm (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (T : ℝ) :
    positiveConvolution f g T=positiveConvolution g f T := by
  have hm : Measurable (fun u : ℝ => f u*g (T-u)) := hf.mul (hg.comp (measurable_const.sub measurable_id))
  have hh := (volume.measurePreserving_sub_left T).lintegral_comp hm
  simp only [sub_sub_cancel] at hh
  simpa only [positiveConvolution,mul_comm] using hh.symm

theorem positive_convolution_assoc (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (T : ℝ) :
    positiveConvolution (positiveConvolution f g) h T=positiveConvolution f (positiveConvolution g h) T := by
  have hfg (u : ℝ) : Measurable (fun v : ℝ => f v*g (u-v)) :=
    hf.mul (hg.comp (measurable_const.sub measurable_id))
  have hm : Measurable (fun p : ℝ × ℝ => (f p.2*g (p.1-p.2))*h (T-p.1)) :=
    ((hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))).mul
      (hh.comp (measurable_const.sub measurable_fst))
  have ht (v : ℝ) : (∫⁻ u,g (u-v)*h (T-u))=∫⁻ w,g w*h ((T-v)-w) := by
    have hj : Measurable (fun u : ℝ => g (u-v)*h (T-u)) :=
      (hg.comp (measurable_id.sub measurable_const)).mul (hh.comp (measurable_const.sub measurable_id))
    have he := (measurePreserving_add_right volume v).lintegral_comp hj
    simp only [add_sub_cancel_right] at he
    have har (w : ℝ) : T-(w+v)=(T-v)-w := by ring
    simpa only [har] using he.symm
  unfold positiveConvolution
  simp_rw [← lintegral_mul_const _ (hfg _)]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro v
  simp_rw [mul_assoc]
  have hj : Measurable (fun u : ℝ => g (u-v)*h (T-u)) :=
    (hg.comp (measurable_id.sub measurable_const)).mul (hh.comp (measurable_const.sub measurable_id))
  rw [lintegral_const_mul (f v) hj,ht]

theorem positive_convolution_add_right (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (T : ℝ) :
    positiveConvolution f (fun t => g t+h t) T=positiveConvolution f g T+positiveConvolution f h T := by
  unfold positiveConvolution
  simp only [mul_add]
  exact lintegral_add_left (hf.mul (hg.comp (measurable_const.sub measurable_id))) _

theorem positive_convolution_const_mul (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (c : ℝ≥0∞) (T : ℝ) :
    positiveConvolution f (fun t => c*g t) T=c*positiveConvolution f g T := by
  unfold positiveConvolution
  simp_rw [mul_left_comm (f _) c]
  exact lintegral_const_mul c (hf.mul (hg.comp (measurable_const.sub measurable_id)))

theorem positive_convolution_add_left (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hh : Measurable h) (T : ℝ) :
    positiveConvolution (fun t => f t+g t) h T=positiveConvolution f h T+positiveConvolution g h T := by
  unfold positiveConvolution
  simp only [add_mul]
  exact lintegral_add_left (hf.mul (hh.comp (measurable_const.sub measurable_id))) _

theorem positive_convolution_const_mul_left (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (c : ℝ≥0∞) (T : ℝ) :
    positiveConvolution (fun t => c*f t) g T=c*positiveConvolution f g T := by
  unfold positiveConvolution
  simp only [mul_assoc]
  exact lintegral_const_mul c (hf.mul (hg.comp (measurable_const.sub measurable_id)))

end
end FiniteCopyReactor
