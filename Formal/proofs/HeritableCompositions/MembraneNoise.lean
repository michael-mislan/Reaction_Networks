import Mathlib

namespace HeritableCompositions

noncomputable def noiseAlpha : ℝ := 1/1000000000000

theorem membrane_exp_remainder (L Q q k : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hL : |L| ≤ 36) (hQ : 0 ≤ Q) (hQ1 : Q ≤ 211722) :
    Real.exp (noiseAlpha*k*(L+q*Q))-1 ≤
      noiseAlpha*k*L+noiseAlpha*k*q*Q+
        2*noiseAlpha^2*k^2*(L^2+q^2*Q^2) := by
  have hqQ : 0 ≤ q*Q ∧ q*Q ≤ 211722 := by
    constructor
    · positivity
    · calc q*Q ≤ 1*211722 := mul_le_mul hq1 hQ1 hQ (by norm_num)
           _ = 211722 := by ring
  have ht : |noiseAlpha*k*(L+q*Q)| ≤ 1 := by
    have hL' := abs_le.mp hL
    have hsum : |L+q*Q| ≤ 211758 := by
      apply abs_le.mpr
      constructor <;> linarith only [hL'.1,hL'.2,hqQ.1,hqQ.2]
    rw [abs_mul, abs_of_nonneg (by unfold noiseAlpha; positivity : 0 ≤ noiseAlpha*k)]
    have h := mul_le_mul hsum hk1 hk (by norm_num : (0:ℝ) ≤ 211758)
    unfold noiseAlpha
    nlinarith only [h]
  have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  have hs : (L+q*Q)^2 ≤ 2*(L^2+q^2*Q^2) := by
    nlinarith only [sq_nonneg (L-q*Q)]
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (noiseAlpha*k))
  nlinarith only [he,hh]

/-- All assumptions here are finite scalar intensity and jump bounds. No
probability estimate is an input. The literal factors are a=lambda*k,
b=lambda*k*q, c=lambda*k^2, d=lambda*k^2*q^2. -/
theorem membrane_polynomial_budget (γ N r L Q a b c d : ℝ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hN : 0 ≤ N) (ha0 : 0 ≤ a)
    (ha : a ≤ 4*γ*N) (hb : b ≤ 4*γ) (hc : c ≤ 4*γ*N) (hd : d ≤ 4*γ)
    (hL : |L| ≤ 14400*r) (hQ : 0 ≤ Q) (hQmax : Q ≤ 211722) :
    a*L+b*Q+2*noiseAlpha*c*L^2+2*noiseAlpha*d*Q^2 ≤
      N*r^2/4+8000000000*N*γ^2+1 := by
  have hr : 0 ≤ r := by linarith only [hL, abs_nonneg L]
  have hLs : L^2 ≤ 207360000*r^2 := by
    nlinarith only [hL, sq_abs L, abs_nonneg L, hr]
  have hQs : Q^2 ≤ (211722 : ℝ)^2 := by nlinarith only [hQ,hQmax]
  have h1 : a*L ≤ 57600*γ*N*r := by
    calc a*L ≤ a*|L| := mul_le_mul_of_nonneg_left (le_abs_self L) ha0
         _ ≤ (4*γ*N)*(14400*r) := mul_le_mul ha hL (abs_nonneg _) (by positivity)
         _ = _ := by ring
  have h2 : b*Q ≤ 4*γ*211722 := mul_le_mul hb hQmax hQ (by positivity)
  have h3 : 2*noiseAlpha*c*L^2 ≤ N*r^2/8 := by
    have hh := mul_le_mul hc hLs (sq_nonneg L) (by positivity : 0 ≤ 4*γ*N)
    have hm := mul_le_mul_of_nonneg_left hh (by norm_num [noiseAlpha] : 0 ≤ 2*noiseAlpha)
    have hg := mul_le_mul_of_nonneg_right hγmax (mul_nonneg hN (sq_nonneg r))
    unfold noiseAlpha at hm ⊢
    nlinarith only [hm,hg,mul_nonneg hN (sq_nonneg r)]
  have h4 : 2*noiseAlpha*d*Q^2 ≤ 8*noiseAlpha*γ*211722^2 := by
    have hh := mul_le_mul hd hQs (sq_nonneg Q) (by positivity : 0 ≤ 4*γ)
    have hm := mul_le_mul_of_nonneg_left hh (by norm_num [noiseAlpha] : 0 ≤ 2*noiseAlpha)
    nlinarith only [hm]
  have hconstant : 4*γ*211722+8*noiseAlpha*γ*211722^2 ≤ 1 := by
    unfold noiseAlpha
    linarith only [hγmax]
  have hyoung : 57600*γ*r ≤ r^2/8+8000000000*γ^2 := by
    nlinarith only [sq_nonneg (r-240000*γ),sq_nonneg γ,mul_nonneg hγ hr]
  have hny := mul_le_mul_of_nonneg_left hyoung hN
  nlinarith only [h1,h2,h3,h4,hconstant,hny]

theorem membrane_rate_factors (γ N m z : ℝ)
    (hγ : 0 ≤ γ) (hN : 0 ≤ N) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hz : 0 ≤ z) (hz4 : z ≤ 4) :
    let rate := γ*m*z
    let k := N/(m+1)
    let q := 1/(m+1)
    0 ≤ rate*k ∧ rate*k ≤ 4*γ*N ∧ rate*k*q ≤ 4*γ ∧
      rate*k^2 ≤ 4*γ*N ∧ rate*k^2*q^2 ≤ 4*γ := by
  dsimp only
  have hm0 : 0 ≤ m := by linarith only [hm]
  have hm1 : 0 < m+1 := by linarith only [hm]
  have hk0 : 0 ≤ N/(m+1) := div_nonneg hN hm1.le
  have hk1 : N/(m+1) ≤ 1 := (div_le_one hm1).mpr (by linarith only [hNm])
  have hq0 : 0 ≤ 1/(m+1) := by positivity
  have hq1 : 1/(m+1) ≤ 1 := (div_le_one hm1).mpr (by linarith only [hm])
  have hratio : m/(m+1) ≤ 1 := (div_le_one hm1).mpr (by linarith)
  have hratio2 : m*N/(m+1)^2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hm1)).mpr
    have hh := mul_le_mul_of_nonneg_left hNm hm0
    nlinarith only [hh,hm]
  have ha0 : 0 ≤ γ*m*z*(N/(m+1)) := by positivity
  have ha : γ*m*z*(N/(m+1)) ≤ 4*γ*N := by
    calc γ*m*z*(N/(m+1)) = γ*z*N*(m/(m+1)) := by ring
         _ ≤ γ*4*N*1 := by gcongr
         _ = _ := by ring
  have hb : γ*m*z*(N/(m+1))*(1/(m+1)) ≤ 4*γ := by
    calc γ*m*z*(N/(m+1))*(1/(m+1)) = γ*z*(m*N/(m+1)^2) := by field_simp
         _ ≤ γ*4*1 := by gcongr
         _ = _ := by ring
  have hc := mul_le_mul ha hk1 hk0 (by positivity : 0 ≤ 4*γ*N)
  have hd := mul_le_mul hb (mul_le_one₀ hk1 hq0 hq1)
    (mul_nonneg hk0 hq0) (by positivity : 0 ≤ 4*γ)
  refine ⟨ha0,ha,hb,?_,?_⟩
  · nlinarith only [hc]
  · nlinarith only [hd]

theorem membrane_source_exp_bound (γ N m z r L Q : ℝ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hN : 0 ≤ N) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hz : 0 ≤ z) (hz4 : z ≤ 4) (hr : r ≤ 1/400)
    (hL : |L| ≤ 14400*r) (hQ : 0 ≤ Q) (hQmax : Q ≤ 211722) :
    γ*m*z*(Real.exp (noiseAlpha*(N/(m+1))*(L+(1/(m+1))*Q))-1) ≤
      noiseAlpha*(N*r^2/4+8000000000*N*γ^2+1) := by
  let rate := γ*m*z
  let k := N/(m+1)
  let q := 1/(m+1)
  have hm0 : 0 ≤ m := by linarith only [hm]
  have hm1 : 0 < m+1 := by linarith only [hm]
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  have hk0 : 0 ≤ k := div_nonneg hN hm1.le
  have hk1 : k ≤ 1 := (div_le_one hm1).mpr (by linarith only [hNm])
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hm1).mpr (by linarith only [hm])
  have hL36 : |L| ≤ 36 := by linarith only [hL,hr]
  have he := mul_le_mul_of_nonneg_left
    (membrane_exp_remainder L Q q k hq0 hq1 hk0 hk1 hL36 hQ hQmax) hrate
  obtain ⟨ha0,ha,hb,hc,hd⟩ := membrane_rate_factors γ N m z hγ hN hm hNm hz hz4
  have hp := membrane_polynomial_budget γ N r L Q (rate*k) (rate*k*q)
    (rate*k^2) (rate*k^2*q^2) hγ hγmax hN ha0 ha hb hc hd hL hQ hQmax
  have hh := mul_le_mul_of_nonneg_left hp (by norm_num [noiseAlpha] : 0 ≤ noiseAlpha)
  change rate*(Real.exp (noiseAlpha*k*(L+q*Q))-1) ≤ _
  nlinarith only [he,hh]

end HeritableCompositions
