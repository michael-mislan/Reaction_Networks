import proofs.OscillatoryCores.ModeBasis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OscillatoryCores

noncomputable def shootingLinear (T w da db l m : ℝ) (u v e f : State) : State →L[ℝ] State :=
  (ContinuousLinearMap.toSpanSingleton ℝ ((T*da) • u-(T*db) • v)).comp (ContinuousLinearMap.proj 0) +
  (ContinuousLinearMap.toSpanSingleton ℝ (-w • v)).comp (ContinuousLinearMap.proj 1) +
  (ContinuousLinearMap.toSpanSingleton ℝ ((Real.exp (l*T)-1) • e)).comp (ContinuousLinearMap.proj 2) +
  (ContinuousLinearMap.toSpanSingleton ℝ ((Real.exp (m*T)-1) • f)).comp (ContinuousLinearMap.proj 3)

/-- Exact inverse criterion for the tested four-variable shooting border. -/
theorem shootingLinear_invertible (L : State →L[ℝ] State)
    {T w da db l m : ℝ} {u v e f : State}
    (hT : 0 < T) (hw : w ≠ 0) (hda : da ≠ 0) (hlm : l ≠ m)
    (hl : l < 0) (hm : m < 0) (hu : u ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hLu : L u = -w • v) (hLv : L v = w • u)
    (hLe : L e = l • e) (hLf : L f = m • f) :
    (shootingLinear T w da db l m u v e f).IsInvertible := by
  let D := shootingLinear T w da db l m u v e f
  have hlgap : Real.exp (l*T)-1 ≠ 0 := by
    have hlt : l*T < 0 := mul_neg_of_neg_of_pos hl hT
    have hh : Real.exp (l*T)<1 := Real.exp_lt_one_iff.mpr hlt
    linarith
  have hmgap : Real.exp (m*T)-1 ≠ 0 := by
    have hmt : m*T < 0 := mul_neg_of_neg_of_pos hm hT
    have hh : Real.exp (m*T)<1 := Real.exp_lt_one_iff.mpr hmt
    linarith
  have hker : ∀ x, D x=0 → x=0 := by
    intro x hx
    have hb : (x 0*(T*da)) • u+(-x 0*(T*db)-x 1*w) • v+
        (x 2*(Real.exp (l*T)-1)) • e+(x 3*(Real.exp (m*T)-1)) • f=0 := by
      calc
        _ = D x := by simp only [D,shootingLinear,ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
          ContinuousLinearMap.toSpanSingleton_apply]; module
        _ = 0 := hx
    obtain ⟨ha,hb,hc,hd⟩ := four_modes_independent L hw hlm hu he hf hLu hLv hLe hLf hb
    have hx0 : x 0=0 := (mul_eq_zero.mp ha).resolve_right (mul_ne_zero (ne_of_gt hT) hda)
    have hx1 : x 1=0 := by
      rw [hx0] at hb
      have hz : x 1*w=0 := by simpa using hb
      exact (mul_eq_zero.mp hz).resolve_right hw
    have hx2 : x 2=0 := (mul_eq_zero.mp hc).resolve_right hlgap
    have hx3 : x 3=0 := (mul_eq_zero.mp hd).resolve_right hmgap
    funext i
    fin_cases i <;> assumption
  have hinj : Function.Injective D := by
    intro x y hxy
    have hz : D (x-y)=0 := by rw [map_sub,hxy,sub_self]
    exact sub_eq_zero.mp (hker (x-y) hz)
  have hsurj : Function.Surjective D := LinearMap.injective_iff_surjective.mp hinj
  let E := LinearEquiv.ofBijective D.toLinearMap ⟨hinj,hsurj⟩
  exact ⟨E.toContinuousLinearEquiv,rfl⟩

end OscillatoryCores
