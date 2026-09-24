import proofs.OscillatoryCores.GrowingOrbit
import proofs.OscillatoryCores.LocalizedFlow

namespace OscillatoryCores

noncomputable def augmentedLinearCurve (t P : ℝ) (y : ℝ → State) (s : ℝ) : ShootingState :=
  (t,0,P,y (P*s))

theorem augmentedLinearCurve_hasDerivAt (t P : ℝ) (y : ℝ → State)
    (hy : ∀ s, HasDerivAt y (normalizedLinear t (y s)) s) (s : ℝ) :
    HasDerivAt (augmentedLinearCurve t P y)
      (augmentedField (augmentedLinearCurve t P y s)) s := by
  have hs : HasDerivAt (fun s : ℝ => P*s) P s := by
    simpa using (hasDerivAt_id s).const_mul P
  have hd := (hy (P*s)).scomp s hs
  have hh := (hasDerivAt_const s t).prodMk ((hasDerivAt_const s (0 : ℝ)).prodMk
    ((hasDerivAt_const s P).prodMk hd))
  simpa only [augmentedLinearCurve,augmentedField,amplitudeField_zero,Function.comp_def,
    smul_eq_mul] using hh

theorem augmentedLinearCurve_zero (t P : ℝ) (y : ℝ → State) :
    augmentedLinearCurve t P y 0=(t,0,P,y 0) := by simp [augmentedLinearCurve]

theorem augmentedLinearCurve_one (t P : ℝ) (y : ℝ → State) :
    augmentedLinearCurve t P y 1=(t,0,P,y P) := by simp [augmentedLinearCurve]

end OscillatoryCores
