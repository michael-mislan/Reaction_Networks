import proofs.CompositionalMemory.GenericMembraneMoments

namespace CompositionalMemory

noncomputable def membraneVectorJump {V : Type*} [AddCommGroup V] [Module ℝ V]
    (u b : V) (c m : ℝ) : V := (-1/(m+1)) • (u+c • b)

theorem membrane_vector_jump_norm {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u b : V) (c m U : ℝ) (hc : 0 ≤ c) (hm : 0 < m+1)
    (hu : ‖u‖ ≤ U) (hb : ‖b‖ ≤ 1) :
    ‖membraneVectorJump u b c m‖ ≤ (U+c)/(m+1) := by
  have hcoef : |(-1:ℝ)/(m+1)| = 1/(m+1) := by
    rw [abs_div,abs_of_pos hm]
    norm_num
  unfold membraneVectorJump
  rw [norm_smul,Real.norm_eq_abs,hcoef]
  have hcb : ‖c • b‖ ≤ c := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hc
  calc
    _ ≤ (1/(m+1))*(‖u‖+‖c • b‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1/(m+1))*(U+c) :=
      mul_le_mul_of_nonneg_left (add_le_add hu hcb) (by positivity)
    _ = _ := by ring

theorem membrane_vector_bilinear_bounds {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (y u b : V) (L r U c m : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hU : 0 ≤ U)
    (hc : 0 ≤ c) (hm : 0 < m+1)
    (hQ : ∀ v w, |Q v w| ≤ L*‖v‖*‖w‖)
    (hy : ‖y‖ ≤ r) (hu : ‖u‖ ≤ U) (hb : ‖b‖ ≤ 1) :
    |Q y (membraneVectorJump u b c m)| ≤ L*r*((U+c)/(m+1)) ∧
    |Q (membraneVectorJump u b c m) (membraneVectorJump u b c m)| ≤
      L*((U+c)/(m+1))^2 := by
  have hj := membrane_vector_jump_norm u b c m U hc hm hu hb
  have hd : 0 ≤ (U+c)/(m+1) := by positivity
  constructor
  · exact (hQ _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hy hL) hj (norm_nonneg _) (mul_nonneg hL hr))
  · have h := mul_le_mul (mul_le_mul_of_nonneg_left hj hL) hj
      (norm_nonneg _) (mul_nonneg hL hd)
    convert (hQ _ _).trans h using 1
    ring

theorem membrane_vector_count_identity {V : Type*}
    [AddCommGroup V] [Module ℝ V] (n b : V) (k m e : ℝ)
    (hm : 0 < m) :
    (k/(m+1)) • (n-e • b)-(k/m) • n =
      membraneVectorJump ((k/m) • n) b (k*e) m := by
  have hs : k/(m+1)-k/m = (-1/(m+1))*(k/m) := by
    field_simp
    ring
  calc
    _ = (k/(m+1)-k/m) • n + (-(k/(m+1)*e)) • b := by module
    _ = _ := by
      unfold membraneVectorJump
      rw [smul_add,smul_smul,smul_smul,hs]
      congr 1
      congr 1
      ring

end CompositionalMemory
