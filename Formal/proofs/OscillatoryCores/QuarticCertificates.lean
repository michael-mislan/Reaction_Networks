import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OscillatoryCores

noncomputable def a1 (t : ℝ) : ℝ := 386 / 125 + 201 * t
noncomputable def a2 (t : ℝ) : ℝ := (562 + 5297 * t) / 250
noncomputable def a3 (t : ℝ) : ℝ := (40 + 479 * t) / 250
noncomputable def a4 (t : ℝ) : ℝ := 6 * t / 25
noncomputable def crossingPolynomial (t : ℝ) : ℝ :=
  2825760 + 242612196 * t + 3570069381 * t ^ 2 - 4001047375 * t ^ 3
noncomputable def crossingSlope (t : ℝ) : ℝ :=
  242612196 + 7140138762 * t - 12003142125 * t ^ 2

theorem coefficients_pos {t : ℝ} (ht : 0 < t) :
    0 < a1 t ∧ 0 < a2 t ∧ 0 < a3 t ∧ 0 < a4 t := by
  dsimp [a1, a2, a3, a4]
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem delta3_identity (t : ℝ) :
    a1 t * a2 t * a3 t - (a3 t)^2 - (a1 t)^2 * a4 t =
      3 / 7812500 * crossingPolynomial t := by
  unfold a1 a2 a3 a4 crossingPolynomial
  ring

theorem crossing_endpoints :
    0 < crossingPolynomial (1/2) ∧ crossingPolynomial 1 < 0 := by
  norm_num [crossingPolynomial]

theorem crossing_exists :
    ∃ t : ℝ, 1/2 < t ∧ t < 1 ∧ crossingPolynomial t = 0 := by
  have hc : Continuous crossingPolynomial := by
    unfold crossingPolynomial
    fun_prop
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' (by norm_num : (1/2 : ℝ) ≤ 1)
    hc.continuousOn ⟨crossing_endpoints.2.le, crossing_endpoints.1.le⟩
  refine ⟨t, ?_, ?_, heq⟩
  · apply lt_of_le_of_ne ht.1
    intro h
    have := crossing_endpoints.1
    rw [h, heq] at this
    exact lt_irrefl _ this
  · apply lt_of_le_of_ne ht.2
    intro h
    have := crossing_endpoints.2
    rw [← h, heq] at this
    exact lt_irrefl _ this

theorem crossingSlope_negative {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) : crossingSlope t < 0 := by
  have hid : t * crossingSlope t - 3 * crossingPolynomial t =
      -(8477280 + 485224392 * t + 3570069381 * t^2) := by
    unfold crossingSlope crossingPolynomial
    ring
  rw [hz] at hid
  have hsq := sq_nonneg t
  have hprod : t * crossingSlope t < 0 := by nlinarith
  by_contra hn
  have hge := le_of_not_gt hn
  have := mul_nonneg ht.le hge
  linarith

theorem positive_crossing_unique {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hsz : crossingPolynomial s = 0) (htz : crossingPolynomial t = 0) : s = t := by
  have hid : s^3 * crossingPolynomial t - t^3 * crossingPolynomial s =
      (s-t) * (2825760 * (s^2+s*t+t^2) +
        242612196*s*t*(s+t) + 3570069381*s^2*t^2) := by
    unfold crossingPolynomial
    ring
  rw [hsz, htz] at hid
  simp only [mul_zero, sub_self] at hid
  have hp : 0 < 2825760 * (s^2+s*t+t^2) +
      242612196*s*t*(s+t) + 3570069381*s^2*t^2 := by positivity
  have he := (mul_eq_zero.mp hid.symm).resolve_right (ne_of_gt hp)
  linarith

/-- The exact coefficient condition factors the quartic at an imaginary pair.
This is an algebraic statement, not the periodic-orbit theorem. -/
theorem crossing_factorization {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) (z : ℝ) :
    z^4 + a1 t*z^3 + a2 t*z^2 + a3 t*z + a4 t =
      (z^2 + a3 t / a1 t) * (z^2 + a1 t*z + a1 t*a4 t/a3 t) := by
  have hp := coefficients_pos ht
  have h1 : a1 t ≠ 0 := ne_of_gt hp.1
  have h3 : a3 t ≠ 0 := ne_of_gt hp.2.2.1
  have hd := delta3_identity t
  rw [hz, mul_zero] at hd
  field_simp [h1, h3]
  linear_combination z^2 * hd

end OscillatoryCores
