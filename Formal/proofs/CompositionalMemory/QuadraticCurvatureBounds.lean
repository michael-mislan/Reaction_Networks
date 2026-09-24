import proofs.CompositionalMemory.WhitenedMetricBounds

namespace CompositionalMemory

theorem distinct_pair_square_le {N : ℕ} (x : Fin N → ℝ) (a b : Fin N) (hab : a ≠ b) :
    x a^2+x b^2 ≤ vectorSquares x := by
  have hh := Finset.sum_le_univ_sum_of_nonneg (s := {a,b}) (fun j => sq_nonneg (x j))
  simpa only [Finset.sum_pair hab,vectorSquares] using hh

theorem distinct_pair_product_bound {N : ℕ} (x : Fin N → ℝ) (a b : Fin N) (hab : a ≠ b) :
    2*|x a*x b| ≤ vectorSquares x := by
  have h1 : 2*|x a*x b| ≤ x a^2+x b^2 := by
    rw [abs_mul]
    nlinarith only [sq_nonneg (|x a|-|x b|),sq_abs (x a),sq_abs (x b)]
  exact h1.trans (distinct_pair_square_le x a b hab)

theorem dot_bound_of_squares {N : ℕ} (u v : Fin N → ℝ) (R S : ℝ)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hu : vectorSquares u ≤ R^2) (hv : vectorSquares v ≤ S^2) :
    |∑ i,u i*v i| ≤ R*S := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hh := mul_le_mul hu hv (vectorSquares_nonneg v) (sq_nonneg R)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hR hS)).mp
  rw [sq_abs,mul_pow]
  exact hc.trans hh

theorem single_reaction_curvature_bound {N : ℕ} (x p : Fin N → ℝ) (a b : Fin N)
    (radius bound rate : ℝ) (hab : a ≠ b) (hr : 0 ≤ radius) (hb : 0 ≤ bound) (hk : 0 ≤ rate)
    (hx : vectorSquares x ≤ radius^2) (hp : vectorSquares p ≤ bound^2) :
    |2*rate*(∑ i,x i*p i)*x a*x b| ≤ rate*bound*radius*vectorSquares x := by
  have hd := dot_bound_of_squares x p radius bound hr hb hx hp
  have hxy := distinct_pair_product_bound x a b hab
  have h1 := mul_le_mul_of_nonneg_right hd (abs_nonneg (x a*x b))
  have h2 := mul_le_mul_of_nonneg_left hxy (mul_nonneg hr hb)
  have h3 : 2*|(∑ i,x i*p i)*(x a*x b)| ≤ radius*bound*vectorSquares x := by
    rw [abs_mul]
    nlinarith only [h1,h2]
  have h4 := mul_le_mul_of_nonneg_left h3 hk
  have he : 2*rate*(∑ i,x i*p i)*x a*x b=rate*(2*((∑ i,x i*p i)*(x a*x b))) := by ring
  rw [he,abs_mul,abs_of_nonneg hk,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith only [h4]

theorem young_force_bound {N : ℕ} (x force : Fin N → ℝ) :
    2*(∑ i,x i*force i) ≤ (1/100 : ℝ)*vectorSquares x+100*vectorSquares force := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (show 2*x i*force i ≤ (1/100 : ℝ)*x i^2+100*force i^2 by
      nlinarith only [sq_nonneg (x i/10-10*force i)]))
  simp only [vectorSquares,Finset.sum_add_distrib,← Finset.mul_sum] at hh ⊢
  simpa only [mul_assoc,← Finset.mul_sum] using hh

end CompositionalMemory
