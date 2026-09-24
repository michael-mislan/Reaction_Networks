import proofs.OscillatoryCores.AugmentedLinearCurve

namespace OscillatoryCores

noncomputable def stableVariationCurve (u v e : State) (w l a s : ℝ) : State :=
  centerCurve u v w s+a • (Real.exp (l*s) • e)

theorem stableVariationCurve_hasDerivAt (t : ℝ) (u v e : State) (w l a s : ℝ)
    (hu : normalizedLinear t u = -w • v) (hv : normalizedLinear t v=w • u)
    (he : normalizedLinear t e=l • e) :
    HasDerivAt (stableVariationCurve u v e w l a)
      (normalizedLinear t (stableVariationCurve u v e w l a s)) s := by
  have hl : HasDerivAt (fun s : ℝ => l*s) l s := by
    simpa using (hasDerivAt_id s).const_mul l
  convert (centerCurve_hasDerivAt t u v w s hu hv).add
    ((hl.exp.smul_const e).const_smul a) using 1
  simp only [stableVariationCurve,map_add,map_smul,he]
  module

theorem stableVariationCurve_zero (u v e : State) (w l a : ℝ) :
    stableVariationCurve u v e w l a 0=u+a • e := by
  simp [stableVariationCurve,centerCurve]

theorem stableVariationCurve_return (u v e : State) (w l a T : ℝ)
    (hT : w*T=2*Real.pi) :
    stableVariationCurve u v e w l a T-stableVariationCurve u v e w l a 0 =
      a • ((Real.exp (l*T)-1) • e) := by
  rw [stableVariationCurve_zero]
  simp only [stableVariationCurve,centerCurve,hT,
    Real.cos_two_pi,Real.sin_two_pi,one_smul,zero_smul,sub_zero]
  module

theorem stable_return_hasDerivAt (u v e : State) (w l T : ℝ)
    (hT : w*T=2*Real.pi) :
    HasDerivAt (fun a => stableVariationCurve u v e w l a T-stableVariationCurve u v e w l a 0)
      ((Real.exp (l*T)-1) • e) 0 := by
  have he : (fun a => stableVariationCurve u v e w l a T-stableVariationCurve u v e w l a 0) =
      (fun a => a • ((Real.exp (l*T)-1) • e)) :=
    funext (fun a => stableVariationCurve_return u v e w l a T hT)
  rw [he]
  simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((Real.exp (l*T)-1) • e)

theorem period_return_hasDerivAt (t : ℝ) (u v : State) (w T : ℝ)
    (hu : normalizedLinear t u = -w • v) (hv : normalizedLinear t v=w • u)
    (hT : w*T=2*Real.pi) :
    HasDerivAt (fun P => centerCurve u v w P-u) (-w • v) T := by
  have hd := (centerCurve_hasDerivAt t u v w T hu hv).sub_const u
  simpa only [centerCurve,hT,Real.cos_two_pi,Real.sin_two_pi,one_smul,zero_smul,sub_zero,hu] using hd

end OscillatoryCores
