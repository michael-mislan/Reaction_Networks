import proofs.RandomViability.CollectiveStartup

namespace RandomViability
open Set
set_option maxHeartbeats 60000

/-- On one holding interval, the corrected coordinate is affine even though
the observed coordinate has jumps at interval boundaries. -/
theorem compensated_holding_comparison (x A d a b eta h : ℝ)
    (ha : 0 < a) (hh : 0 ≤ h) (hd : b-a*x ≤ d)
    (hnoise : ∀ s ∈ Icc 0 h,A-d*s ≤ eta) :
    ((x-A)-(b/a-eta))/Real.exp (a*h)+(b/a-eta) ≤ x-A+d*h := by
  have he : a*(b/a-eta) = b-a*eta := by field_simp
  suffices ht : (x-A+d*0-(b/a-eta))/Real.exp (a*h)+(b/a-eta) ≤ x-A+d*h by
    simpa only [mul_zero,add_zero] using ht
  apply scalar_startup_lower (fun s => x-A+d*s) (fun _ => d) a (b/a-eta) h hh
  · intro s _
    simpa only [mul_one] using (((hasDerivAt_id s).const_mul d).const_add (x-A))
  · intro s hs
    have hm := mul_le_mul_of_nonneg_left (hnoise s hs) ha.le
    nlinarith only [hd,hm,he]

theorem scalar_affine_recurrence_lower (y h : ℕ → ℝ) (a e : ℝ) (K : ℕ)
    (hstep : ∀ i < K,(y i-e)/Real.exp (a*h i)+e ≤ y (i+1)) :
    (y 0-e)/Real.exp (a*(∑ i : Fin K,h i))+e ≤ y K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hi := ih (fun i hi => hstep i (by omega))
    have he : Real.exp (a*(∑ i : Fin (K+1),h i)) =
        Real.exp (a*(∑ i : Fin K,h i))*Real.exp (a*h K) := by
      rw [Fin.sum_univ_castSucc]
      change Real.exp (a*((∑ i : Fin K,h i)+h K)) = _
      rw [mul_add,Real.exp_add]
    calc
      _ = (((y 0-e)/Real.exp (a*(∑ i : Fin K,h i))+e)-e)/Real.exp (a*h K)+e := by
        rw [he]
        field_simp
        ring
      _ ≤ (y K-e)/Real.exp (a*h K)+e := add_le_add
        (div_le_div_of_nonneg_right (sub_le_sub_right hi e) (Real.exp_pos _).le) le_rfl
      _ ≤ _ := hstep K (by omega)

/-- Finite-piecewise comparison with an explicit noise loss. Hypotheses are
stated for actual holding-interval compensation, not a differentiable count path. -/
theorem compensated_scalar_prefix_lower (x A d h : ℕ → ℝ) (a b eta : ℝ) (K : ℕ)
    (ha : 0 < a) (hA0 : A 0 = 0)
    (hh : ∀ i < K,0 ≤ h i)
    (hd : ∀ i < K,b-a*x i ≤ d i)
    (hnoise : ∀ i < K,∀ s ∈ Icc 0 (h i),A i-d i*s ≤ eta)
    (hjump : ∀ i < K,x (i+1)-A (i+1) = x i-A i+d i*h i)
    (hend : -eta ≤ A K) :
    (x 0-(b/a-eta))/Real.exp (a*(∑ i : Fin K,h i))+b/a-2*eta ≤ x K := by
  have hs : ∀ i < K,((x i-A i)-(b/a-eta))/Real.exp (a*h i)+(b/a-eta) ≤
      x (i+1)-A (i+1) := by
    intro i hi
    rw [hjump i hi]
    exact compensated_holding_comparison (x i) (A i) (d i) a b eta (h i)
      ha (hh i hi) (hd i hi) (hnoise i hi)
  have ht := scalar_affine_recurrence_lower (fun i => x i-A i) h a (b/a-eta) K hs
  simp only [hA0,sub_zero] at ht
  linarith only [ht,hend]

theorem compensated_scalar_prefix_floor (x A d h : ℕ → ℝ) (a b eta : ℝ) (K : ℕ)
    (ha : 0 < a) (hA0 : A 0 = 0) (hx0 : b/a-eta ≤ x 0)
    (hh : ∀ i < K,0 ≤ h i)
    (hd : ∀ i < K,b-a*x i ≤ d i)
    (hnoise : ∀ i < K,∀ s ∈ Icc 0 (h i),A i-d i*s ≤ eta)
    (hjump : ∀ i < K,x (i+1)-A (i+1) = x i-A i+d i*h i)
    (hend : -eta ≤ A K) : b/a-2*eta ≤ x K := by
  have ht := compensated_scalar_prefix_lower x A d h a b eta K ha hA0 hh hd hnoise hjump hend
  have he : 0 ≤ (x 0-(b/a-eta))/Real.exp (a*(∑ i : Fin K,h i)) :=
    div_nonneg (sub_nonneg.mpr hx0) (Real.exp_pos _).le
  linarith only [ht,he]

end RandomViability
