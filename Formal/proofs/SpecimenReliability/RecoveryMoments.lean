import proofs.SpecimenReliability.Source

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

def corners (p r q : ℝ) : Fin 4 → ℝ := ![1-p-r+q,p-q,r-q,q]
def cornerX : Fin 4 → ℝ := ![0,1,0,1]
def cornerY : Fin 4 → ℝ := ![0,0,1,1]

def envelope (p r q a b : ℝ) (n : ℕ) : ℝ :=
  1-p-r+q + (p-q)*(1-a)^n + (r-q)*(1-b)^n + q*(1-a-b)^n

theorem corners_normalized (p r q : ℝ) : ∑ i, corners p r q i = 1 := by
  simp [corners, Fin.sum_univ_succ]; ring

theorem corners_nonneg (p r q : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r)
    (hqp : q ≤ p) (hl : p+r-1 ≤ q) : ∀ i, 0 ≤ corners p r q i := by
  intro i
  fin_cases i <;> simp [corners] <;> linarith

theorem corners_moments (p r q : ℝ) :
    (∑ i, corners p r q i * cornerX i) = p ∧
    (∑ i, corners p r q i * cornerY i) = r ∧
    (∑ i, corners p r q i * (cornerX i * cornerY i)) = q := by
  simp [corners, cornerX, cornerY, Fin.sum_univ_succ]

theorem envelope_attained (p r q a b : ℝ) (n : ℕ) :
    sourceRisk (corners p r q) cornerX cornerY a b n = envelope p r q a b n := by
  rw [source_law]
  simp [corners, cornerX, cornerY, Fin.sum_univ_succ, envelope]
  ring

theorem power_chord (u v t : ℝ) (n : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    ((1-t)*u+t*v)^n ≤ (1-t)*u^n+t*v^n := by
  have h := (convexOn_pow (𝕜 := ℝ) n).2 hu hv
    (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
  simpa only [smul_eq_mul] using h

theorem pointwise_envelope (a b x y : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    (1-a*x-b*y)^n ≤ envelope x y (x*y) a b n := by
  have hby := mul_le_mul_of_nonneg_left hy.2 hb
  have h0 : 0 ≤ 1-b*y := by nlinarith
  have h1 : 0 ≤ 1-a-b*y := by nlinarith
  have h := power_chord (1-b*y) (1-a-b*y) x n h0 h1 hx
  have e : (1-x)*(1-b*y)+x*(1-a-b*y) = 1-a*x-b*y := by ring
  rw [e] at h
  have hA := power_chord 1 (1-b) y n (by norm_num) (by linarith) hy
  have hB := power_chord (1-a) (1-a-b) y n (by linarith) (by linarith) hy
  have eA : (1-y)*1+y*(1-b) = 1-b*y := by ring
  have eB : (1-y)*(1-a)+y*(1-a-b) = 1-a-b*y := by ring
  rw [eA, one_pow] at hA
  rw [eB] at hB
  have hA' := mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hx.2)
  have hB' := mul_le_mul_of_nonneg_left hB hx.1
  calc
    _ ≤ (1-x)*(1-b*y)^n+x*(1-a-b*y)^n := h
    _ ≤ (1-x)*((1-y)*1+y*(1-b)^n) +
        x*((1-y)*(1-a)^n+y*(1-a-b)^n) := add_le_add hA' hB'
    _ = _ := by unfold envelope; ring

end
end SpecimenReliability
