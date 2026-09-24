import Mathlib

namespace TypeII3

def cyclicOmega (u1 u2 u3 v1 v2 v3 : ℝ) : ℝ :=
  u1 * u2 * u3 + u1 * u2 + u1 * u3 + u1 * v2 + u1 +
  u2 * u3 + u2 * v3 + u2 + u3 * v1 + u3 +
  v1 * v2 * v3 + v1 + v2 + v3

theorem cyclicOmega_pos
    {u1 u2 u3 v1 v2 v3 : ℝ}
    (hu1 : 0 < u1) (hu2 : 0 < u2) (hu3 : 0 < u3)
    (hv1 : 0 < v1) (hv2 : 0 < v2) (hv3 : 0 < v3) :
    0 < cyclicOmega u1 u2 u3 v1 v2 v3 := by
  unfold cyclicOmega
  positivity

theorem cyclic_three_eq_zero
    {u1 u2 u3 v1 v2 v3 s1 s2 s3 : ℝ}
    (hu1 : 0 < u1) (hu2 : 0 < u2) (hu3 : 0 < u3)
    (hv1 : 0 < v1) (hv2 : 0 < v2) (hv3 : 0 < v3)
    (h1 : s3 = (1 + u1) * s1 + v1 * s2)
    (h2 : s1 = (1 + u2) * s2 + v2 * s3)
    (h3 : s2 = (1 + u3) * s3 + v3 * s1) :
    s1 = 0 ∧ s2 = 0 ∧ s3 = 0 := by
  have hOmega : 0 < cyclicOmega u1 u2 u3 v1 v2 v3 :=
    cyclicOmega_pos hu1 hu2 hu3 hv1 hv2 hv3
  have hs1mul : cyclicOmega u1 u2 u3 v1 v2 v3 * s1 = 0 := by
    unfold cyclicOmega
    linear_combination
      -((1 + u2) * (1 + u3) + v2) * h1 +
      -(1 - v1 * (1 + u3)) * h2 +
      -(v1 * v2 + (1 + u2)) * h3
  have hs1 : s1 = 0 :=
    (mul_eq_zero.mp hs1mul).resolve_left (ne_of_gt hOmega)
  rw [hs1] at h2 h3
  rw [h3] at h2
  have hcoef : 0 < (1 + u2) * (1 + u3) + v2 := by positivity
  have hs3mul : ((1 + u2) * (1 + u3) + v2) * s3 = 0 := by
    linear_combination -h2
  have hs3 : s3 = 0 :=
    (mul_eq_zero.mp hs3mul).resolve_left (ne_of_gt hcoef)
  have hs2 : s2 = 0 := by simpa [hs3] using h3
  exact ⟨hs1, hs2, hs3⟩

end TypeII3
