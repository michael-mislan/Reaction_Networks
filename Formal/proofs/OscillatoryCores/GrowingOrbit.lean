import proofs.OscillatoryCores.LinearOrbit
import proofs.OscillatoryCores.MovingBranch
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OscillatoryCores

noncomputable def growingCurve (u v : State) (a b s : ℝ) : State :=
  Real.exp (a*s) • centerCurve u v b s

theorem growingCurve_hasDerivAt (t : ℝ) (u v : State) (a b s : ℝ)
    (hu : normalizedLinear t u = a • u - b • v)
    (hv : normalizedLinear t v = b • u + a • v) :
    HasDerivAt (growingCurve u v a b)
      (normalizedLinear t (growingCurve u v a b s)) s := by
  have ha : HasDerivAt (fun s : ℝ => a*s) a s := by
    simpa using (hasDerivAt_id s).const_mul a
  have hb : HasDerivAt (fun s : ℝ => b*s) b s := by
    simpa using (hasDerivAt_id s).const_mul b
  convert ha.exp.smul ((hb.cos.smul_const u).sub (hb.sin.smul_const v)) using 1
  simp only [growingCurve,centerCurve,map_smul,map_sub,hu,hv,Pi.sub_apply]
  module

/-- At a full revolution with zero growth, derivatives of the moving
eigenvectors cancel from the return defect. -/
theorem moving_return_hasDerivAt
    (a b : ℝ → ℝ) (u v : ℝ → State) (t T da db : ℝ) (du dv : State)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t)
    (ha0 : a t=0) (hbT : b t*T=2*Real.pi) :
    HasDerivAt (fun p => growingCurve (u p) (v p) (a p) (b p) T - u p)
      ((T*da) • u t - (T*db) • v t) t := by
  have hae := (ha.mul_const T).exp
  have hbc := (hb.mul_const T).cos
  have hbs := (hb.mul_const T).sin
  convert (hae.smul ((hbc.smul hu).sub (hbs.smul hv))).sub hu using 1
  change (T*da) • u t - (T*db) • v t =
    (Real.exp (a t*T) •
      ((Real.cos (b t*T) • du + (-Real.sin (b t*T)*(db*T)) • u t) -
       (Real.sin (b t*T) • dv + (Real.cos (b t*T)*(db*T)) • v t)) +
     (Real.exp (a t*T)*(da*T)) •
       (Real.cos (b t*T) • u t - Real.sin (b t*T) • v t)) - du
  simp only [ha0,zero_mul,Real.exp_zero,hbT,Real.cos_two_pi,Real.sin_two_pi,
    one_mul,zero_smul,one_smul,zero_add,sub_zero]
  module

end OscillatoryCores
