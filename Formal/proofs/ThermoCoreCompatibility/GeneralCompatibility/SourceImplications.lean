import proofs.ThermoCoreCompatibility.GeneralCompatibility.ClosedMargin
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ThermoCoreCompatibility.GeneralCompatibility

open MultiInterface

noncomputable def inverseUpper (w : Factors) (t : ℝ) : ℝ :=
  (Real.sqrt (w.a ^ 2 + 4 * w.b * (w.a + w.b) * t) - w.a) / (2 * w.b)

theorem inverseUpper_nonneg (w : Factors) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ inverseUpper w t := by
  have ha := w.a_pos
  have hb := w.b_pos
  have hd : 0 ≤ w.a ^ 2 + 4 * w.b * (w.a + w.b) * t := by positivity
  have hs := Real.sq_sqrt hd
  have hsa : w.a ≤ Real.sqrt (w.a ^ 2 + 4 * w.b * (w.a + w.b) * t) := by
    apply (sq_le_sq₀ ha.le (Real.sqrt_nonneg _)).mp
    rw [hs]
    exact le_add_of_nonneg_right (by positivity)
  unfold inverseUpper
  exact div_nonneg (sub_nonneg.mpr hsa) (by positivity)

theorem upper_inverseUpper (w : Factors) {t : ℝ} (ht : 0 ≤ t) :
    w.upper (inverseUpper w t) = t := by
  have hb : w.b ≠ 0 := ne_of_gt w.b_pos
  have hab : w.a + w.b ≠ 0 := ne_of_gt w.upper_den_pos
  have hd : 0 ≤ w.a ^ 2 + 4 * w.b * (w.a + w.b) * t := by
    have := w.a_pos
    have := w.b_pos
    positivity
  have hs := Real.sq_sqrt hd
  have hid (s : ℝ) : w.a * ((s-w.a)/(2*w.b)) +
      w.b * ((s-w.a)/(2*w.b))^2 = (s^2-w.a^2)/(4*w.b) := by
    field_simp [hb]
    ring
  unfold Factors.upper inverseUpper
  rw [hid, hs]
  field_simp [hb, hab]
  ring

theorem inverseUpper_le_iff (w : Factors) {t y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) :
    inverseUpper w t ≤ y ↔ t ≤ w.upper y := by
  have hi := inverseUpper_nonneg w ht
  constructor
  · intro h
    have hh := w.upper_strictMono.monotoneOn hi hy h
    simpa only [upper_inverseUpper w ht] using hh
  · intro h
    by_contra hn
    have hh := w.upper_strictMono hy hi (lt_of_not_ge hn)
    rw [upper_inverseUpper w ht] at hh
    exact (not_lt_of_ge h) hh

theorem inverseUpper_monotoneOn (w : Factors) :
    MonotoneOn (inverseUpper w) (Set.Ici 0) := by
  intro t ht u hu htu
  apply (inverseUpper_le_iff w ht (inverseUpper_nonneg w hu)).mpr
  simpa only [upper_inverseUpper w hu] using htu

theorem continuous_inverseUpper (w : Factors) : Continuous (inverseUpper w) := by
  unfold inverseUpper
  fun_prop

theorem boxed_margin_iff_implications {V E : Type*}
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ)
    (hlo : ∀ v, 0 ≤ lo v) {τ : ℝ} (hτ : 0 ≤ τ) (z : V → ℝ) :
    BoxedMargin src dst w lo hi τ z ↔
      (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
      ∀ e, (w e).lower (z (src e)) + τ ≤ z (dst e) ∧
        inverseUpper (w e) (z (dst e) + τ) ≤ z (src e) := by
  constructor
  · intro hz
    refine ⟨hz.1, fun e => ⟨(hz.2 e).1, ?_⟩⟩
    exact (inverseUpper_le_iff (w e)
      (add_nonneg ((hlo _).trans (hz.1 _).1) hτ)
      ((hlo _).trans (hz.1 _).1)).mpr (hz.2 e).2
  · intro hz
    refine ⟨hz.1, fun e => ⟨(hz.2 e).1, ?_⟩⟩
    exact (inverseUpper_le_iff (w e)
      (add_nonneg ((hlo _).trans (hz.1 _).1) hτ)
      ((hlo _).trans (hz.1 _).1)).mp (hz.2 e).2

end ThermoCoreCompatibility.GeneralCompatibility
