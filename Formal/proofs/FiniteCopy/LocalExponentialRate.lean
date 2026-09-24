import proofs.FiniteCopy.JumpNoise

namespace FiniteCopy

noncomputable def localAlpha : ℝ := 1/1000000000000

theorem local_exponential_increment_bound (L Q q v : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hv1 : v ≤ 1/40000)
    (hL : L^2 ≤ 100000*v) (hQ : 0 ≤ Q) (hQ1 : Q ≤ 210) :
    Real.exp (localAlpha*(L+q*Q))-1 ≤
      localAlpha*L+localAlpha*q*210+2*localAlpha^2*100000*v+
        2*localAlpha^2*q^2*44100 := by
  have hLa : -2 ≤ L ∧ L ≤ 2 := by constructor <;> nlinarith
  have hqQ : 0 ≤ q*Q ∧ q*Q ≤ 210 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hQ]
  have ht : |localAlpha*(L+q*Q)| ≤ 1 := by
    apply abs_le.mpr
    unfold localAlpha
    constructor <;> linarith [hLa.1,hLa.2,hqQ.1,hqQ.2]
  have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  have hs : (L+q*Q)^2 ≤ 2*L^2+2*q^2*Q^2 := by nlinarith only [sq_nonneg (L-q*Q)]
  have hQQ : Q^2 ≤ 44100 := by nlinarith
  have hqQsq := mul_le_mul_of_nonneg_left hQQ (sq_nonneg q)
  have hfirst := mul_le_mul_of_nonneg_left hQ1 (mul_nonneg (by norm_num [localAlpha] : 0 ≤ localAlpha) hq)
  have hsecond := mul_le_mul_of_nonneg_left hs (sq_nonneg localAlpha)
  have hthird := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2*localAlpha^2)
  have hfourth := mul_le_mul_of_nonneg_left hqQsq (by positivity : 0 ≤ 2*localAlpha^2)
  nlinarith only [he,hfirst,hsecond,hthird,hfourth]

/-- Numerical constants deliberately favor a short exact proof over sharpness.
The hypotheses are finite sums and polynomial bounds, not probability laws. -/
theorem local_exponential_rate_bound (a L Q : Fin 13 → ℝ) (q v : ℝ)
    (ha : ∀ r, 0 ≤ a r) (hsum : ∑ r, a r ≤ 200000)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1/40000)
    (hL : ∀ r, (L r)^2 ≤ 100000*v)
    (hQ : ∀ r, 0 ≤ Q r ∧ Q r ≤ 210)
    (hdrift : ∑ r, a r*L r ≤ -(59/100)*v+10000*q) :
    ∑ r, a r*(Real.exp (localAlpha*(L r+q*Q r))-1) ≤
      localAlpha*(-(1/2)*v+100000000*q) := by
  let c := localAlpha*q*210+2*localAlpha^2*100000*v+2*localAlpha^2*q^2*44100
  have hc : 0 ≤ c := by dsimp [c,localAlpha]; positivity
  have hpoint (r) : a r*(Real.exp (localAlpha*(L r+q*Q r))-1) ≤
      localAlpha*(a r*L r)+a r*c := by
    have h := mul_le_mul_of_nonneg_left
      (local_exponential_increment_bound (L r) (Q r) q v hq hq1 hv1 (hL r) (hQ r).1 (hQ r).2) (ha r)
    dsimp [c]
    nlinarith only [h]
  have hsum1 := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hpoint r)
  have hid : (∑ r, (localAlpha*(a r*L r)+a r*c)) =
      localAlpha*(∑ r, a r*L r)+(∑ r, a r)*c := by
    rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
  rw [hid] at hsum1
  have hd := mul_le_mul_of_nonneg_left hdrift (by norm_num [localAlpha] : 0 ≤ localAlpha)
  have hh := mul_le_mul_of_nonneg_right hsum hc
  have hq2 : q^2 ≤ q := by nlinarith
  dsimp [c,localAlpha] at hsum1 hd hh ⊢
  nlinarith only [hsum1,hd,hh,hq2,hq,hv]

end FiniteCopy


