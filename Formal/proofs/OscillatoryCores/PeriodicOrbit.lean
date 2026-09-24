import proofs.OscillatoryCores.AmplitudeOrbit
import proofs.OscillatoryCores.DeletionMinimality

namespace OscillatoryCores

open DUnstableCores
open scoped BigOperators

/-- The fixed p=400, q=375 source admits positive rates and an actual
nonconstant positive periodic mass-action trajectory. -/
theorem literal_positive_periodic_orbit :
    ∃ k : Fin 5 → ℝ, ∃ x : ℝ → State, ∃ P : ℝ,
      (∀ j, 0 < k j) ∧ 0 < P ∧ (∀ s i, 0 < x s i) ∧
      Solves k x ∧ Function.Periodic x P ∧ (∃ s, x s ≠ x 0) := by
  obtain ⟨t,r,P,y,ht,hr,hP,hper,hy,hpos,hvel⟩ := amplitude_periodic_orbit
  let x : ℝ → State := fun s i => equilibrium t i*(1+r*y (s/P) i)
  have hPn : P ≠ 0 := ne_of_gt hP
  have hxderiv (s : ℝ) (i : Fin 4) :
      HasDerivAt (fun s => x s i)
        (equilibrium t i*(r*amplitudeField t r (y (s/P)) i)) s := by
    have hs : HasDerivAt (fun s : ℝ => s/P) (1/P) s := by
      simpa using (hasDerivAt_id s).div_const P
    have hyd := ((hasDerivAt_pi.mp (hy (s/P))) i).comp s hs
    have hh := ((hyd.const_mul r).const_add 1).const_mul (equilibrium t i)
    convert hh using 1
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp
  have hnonconst : ∃ s, x s ≠ x 0 := by
    by_contra hn
    push Not at hn
    have hxconstant : x = fun _ => x 0 := funext hn
    apply hvel
    funext i
    have hh := hxderiv 0 i
    rw [hxconstant] at hh
    have hd := hh.unique (hasDerivAt_const (0 : ℝ) (x 0 i))
    simp only [zero_div] at hd
    have he : equilibrium t i ≠ 0 := ne_of_gt (equilibrium_pos ht i)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left he)).resolve_left (ne_of_gt hr)
  refine ⟨rates t,x,P,rates_pos ht,hP,?_,?_,?_,hnonconst⟩
  · intro s i
    exact mul_pos (equilibrium_pos ht i) (hpos (s/P) i)
  · intro s i
    have he := normalization_source ht (fun k => 1+r*y (s/P) k) i
    rw [← amplitudeField_source] at he
    convert hxderiv s i using 1
    exact he.symm
  · intro s
    have hs : (s+P)/P=s/P+1 := by field_simp
    funext i
    simp only [x,hs]
    rw [hper (s/P)]

end OscillatoryCores
