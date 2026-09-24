import proofs.CompositionalMemory.CausalExponential

namespace CompositionalMemory
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

theorem renewalConv_scale_left {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) (T : ℝ) : renewalConv (fun t => c*f t) g T=c*renewalConv f g T := by
  unfold renewalConv
  simp_rw [mul_assoc]
  exact lintegral_const_mul _ (hf.mul (hg.comp (measurable_const.sub measurable_id)))

theorem renewalConv_scale_right {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) (T : ℝ) : renewalConv f (fun t => c*g t) T=c*renewalConv f g T := by
  unfold renewalConv
  have he (u : ℝ) : f u*(c*g (T-u))=c*(f u*g (T-u)) := by ring
  simp_rw [he]
  exact lintegral_const_mul _ (hf.mul (hg.comp (measurable_const.sub measurable_id)))

theorem renewalConv_mul_right {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) (T : ℝ) : renewalConv f (fun t => g t*c) T=renewalConv f g T*c := by
  simp_rw [mul_comm _ c]
  exact renewalConv_scale_right hf hg c T

/-- Resolving artificial self-loops preserves a complete nonnegative renewal solution. -/
theorem causal_renewal_self_loop (q lam : ℝ) (hql : lam ≤ q)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) (a : ℝ≥0∞) (T : ℝ) :
    causalExp lam T*a+renewalConv (causalExp lam) H T =
      causalExp q T*a+renewalConv (causalExp q)
        (fun t => H t+ENNReal.ofReal (q-lam)*(causalExp lam t*a+renewalConv (causalExp lam) H t)) T := by
  have hq := causalExp_measurable q
  have hl := causalExp_measurable lam
  have hcl := renewalConv_measurable hq hl
  have hhl := renewalConv_measurable hl hH
  have he : renewalConv (causalExp lam) H T = renewalConv (causalExp q) H T+
      ENNReal.ofReal (q-lam)*renewalConv (renewalConv (causalExp q) (causalExp lam)) H T := by
    calc
      _ = renewalConv (fun t => causalExp q t+ENNReal.ofReal (q-lam)*
          renewalConv (causalExp q) (causalExp lam) t) H T := by
        congr 1
        funext t
        exact causalExp_resolvent q lam hql t
      _ = _ := by
        rw [renewalConv_add_left hq hH,renewalConv_scale_left hcl hH]
  rw [renewalConv_add_right hq hH,
    renewalConv_scale_right hq ((hl.mul measurable_const).add hhl),
    renewalConv_add_right hq (hl.mul measurable_const),
    renewalConv_mul_right hq hl,
    renewalConv_assoc hq hl hH,he,causalExp_resolvent q lam hql T]
  ring

end
end CompositionalMemory
