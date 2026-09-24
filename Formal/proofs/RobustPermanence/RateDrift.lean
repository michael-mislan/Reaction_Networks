import proofs.RobustPermanence.RateBox

namespace RobustPermanence

theorem quadratic_ceiling (L q C z : ℝ) (hq : 0 < q) (hC : L^2 ≤ 4*q*C) :
    L*z-q*z^2 ≤ C := by
  have hi : 4*q*(C-(L*z-q*z^2)) = (4*q*C-L^2)+(2*q*z-L)^2 := by ring
  have hh : 0 ≤ 4*q*(C-(L*z-q*z^2)) := by
    rw [hi]
    exact add_nonneg (sub_nonneg.2 hC) (sq_nonneg _)
  have hf := nonneg_of_mul_nonneg_right hh (by positivity : 0 < 4*q)
  linarith only [hf]

theorem rate_total_upper (r : AssemblyRates) (hr : RateBox r) (A B z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    rateA r A B z+rateB r A B z ≤ 3300001/100000-(9999/10000)*(A+B) := by
  rw [rate_total_identity]
  have hα := mul_le_mul_of_nonneg_right hr.alpha.1 hA
  have hβ : 9999/10000 ≤ r.beta-r.ef := by linarith [hr.beta.1,hr.ef.2]
  have hβB := mul_le_mul_of_nonneg_right hβ hB
  have her := mul_nonneg (by linarith [hr.er.1] : 0 ≤ r.er) (sq_nonneg A)
  linarith [hr.a.2,hr.b.2]

theorem rate_weighted_upper (r : AssemblyRates) (hr : RateBox r) (A B z H X : ℝ)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 0 ≤ B) (hz : 0 ≤ z) (hH : 0 ≤ H) (hX : 0 ≤ X) :
    rateZ r A B z H X+(7/4:ℝ)*rateH r z H ≤ 219/2-(2/7)*(z+(7/4)*H) := by
  rw [rate_weighted_identity]
  have hp := mul_le_mul hr.p.2 hA' hA (by norm_num : (0:ℝ) ≤ 1000001/1000000)
  have hq := mul_nonneg (mul_nonneg (by linarith [hr.q.1] : 0 ≤ r.q) hB) hz
  have hk := mul_nonneg (mul_nonneg (by linarith [hr.k.1] : 0 ≤ r.k) hz) hX
  have hu := mul_le_mul_of_nonneg_right hr.u.2 hz
  have hv := mul_le_mul_of_nonneg_right hr.v.1 (sq_nonneg z)
  have hc : (-3*r.h1+r.h2-7*r.d)/4 ≤ -(1/2:ℝ) := by
    linarith [hr.h1.1,hr.h2.2,hr.d.1]
  have hcH := mul_le_mul_of_nonneg_right hc hH
  have hquad := quadratic_ceiling ((3/4)*(16000001/1000000)+2/7)
    ((1/4)*(1999999/1000000)) (219/2-(1000001/1000000)*34) z (by norm_num) (by norm_num)
  nlinarith only [hp,hq,hk,hu,hv,hcH,hquad]

theorem rate_z_upper (r : AssemblyRates) (hr : RateBox r) (A B z H X : ℝ)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 0 ≤ B) (hz : 0 ≤ z) (hH : 0 ≤ H) (hX : 0 ≤ X)
    (hW : z+(7/4:ℝ)*H ≤ 384) :
    rateZ r A B z H X ≤ 1270-113*z := by
  have hp := mul_le_mul hr.p.2 hA' hA (by norm_num : (0:ℝ) ≤ 1000001/1000000)
  have hq := mul_nonneg (mul_nonneg (by linarith [hr.q.1] : 0 ≤ r.q) hB) hz
  have hk := mul_nonneg (mul_nonneg (by linarith [hr.k.1] : 0 ≤ r.k) hz) hX
  have hu := mul_le_mul_of_nonneg_right hr.u.1 hz
  have hv := mul_le_mul_of_nonneg_right hr.v.1 (sq_nonneg z)
  have hh := mul_le_mul_of_nonneg_right
    (show r.h1+2*r.h2 ≤ 3000003/1000000 by linarith [hr.h1.2,hr.h2.2]) hH
  have hquad := quadratic_ceiling (113-15999999/1000000-(3000003/1000000)*(4/7))
    (2*(1999999/1000000)) (1270-(1000001/1000000)*34-(3000003/1000000)*(1536/7)) z
    (by norm_num) (by norm_num)
  dsimp [rateZ]
  nlinarith only [hp,hq,hk,hu,hv,hh,hW,hquad]

theorem rate_B_lower (r : AssemblyRates) (hr : RateBox r) (A B z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hz : z ≤ 12) :
    269/10-(131/10)*B ≤ rateB r A B z := by
  have hp := mul_nonneg (by linarith [hr.p.1] : 0 ≤ r.p) hA
  have her := mul_nonneg (by linarith [hr.er.1] : 0 ≤ r.er) (sq_nonneg A)
  have hqz := mul_le_mul_of_nonneg_left hz (by linarith [hr.q.1] : 0 ≤ r.q)
  have hloss : r.q*z+r.beta+r.ef ≤ 131/10 := by linarith [hr.q.2,hr.beta.2,hr.ef.2]
  have hb := mul_le_mul_of_nonneg_right hloss hB
  dsimp [rateB]
  linarith [hr.b.1]

theorem rate_X_upper (r : AssemblyRates) (hr : RateBox r) (z X : ℝ)
    (hz : z ≤ 12) (hX : 0 ≤ X) : rateX r z X ≤ 139-12*X := by
  have hkz := mul_le_mul_of_nonneg_left hz (by linarith [hr.k.1] : 0 ≤ r.k)
  have hg : r.k*z-r.mu ≤ (1000001/1000000)*12-499999/1000000 := by
    linarith [hr.k.2,hr.mu.1]
  have hgX := mul_le_mul_of_nonneg_right hg hX
  have hrho := mul_le_mul_of_nonneg_right hr.rho.1 (sq_nonneg X)
  have hquad := quadratic_ceiling ((1000001/1000000)*12-499999/1000000+12)
    (999999/1000000) 139 X (by norm_num) (by norm_num)
  dsimp [rateX]
  nlinarith only [hgX,hrho,hquad]

theorem rate_A_lower (r : AssemblyRates) (hr : RateBox r) (A B z : ℝ)
    (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 0 ≤ B) (hz : 0 ≤ z) :
    5-3*A ≤ rateA r A B z := by
  have hq := mul_nonneg (mul_nonneg (by linarith [hr.q.1] : 0 ≤ r.q) hB) hz
  have hef := mul_nonneg (by linarith [hr.ef.1] : 0 ≤ r.ef) hB
  have hAA : A^2 ≤ 34*A := by nlinarith
  have her := mul_le_mul_of_nonneg_left hAA (by linarith [hr.er.1] : 0 ≤ r.er)
  have hcoef : r.p+r.alpha+68*r.er ≤ 3 := by linarith [hr.p.2,hr.alpha.2,hr.er.2]
  have hcoefA := mul_le_mul_of_nonneg_right hcoef hA
  dsimp [rateA]
  nlinarith [hr.a.1]

theorem rate_z_lower (r : AssemblyRates) (hr : RateBox r) (A B z H X : ℝ)
    (hA : 1 ≤ A) (hB : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hX : X ≤ 12) :
    9/10-111*z ≤ rateZ r A B z H X := by
  have hp := mul_le_mul_of_nonneg_left hA (by linarith [hr.p.1] : 0 ≤ r.p)
  have hqB := mul_le_mul_of_nonneg_left hB (by linarith [hr.q.1] : 0 ≤ r.q)
  have hqBz := mul_le_mul_of_nonneg_right hqB hz
  have hkX := mul_le_mul_of_nonneg_left hX (by linarith [hr.k.1] : 0 ≤ r.k)
  have hkXz := mul_le_mul_of_nonneg_right hkX hz
  have hzz : z^2 ≤ 12*z := by nlinarith
  have hv := mul_le_mul_of_nonneg_left hzz (by linarith [hr.v.1] : 0 ≤ r.v)
  have hsum : 34*r.q+r.u+24*r.v+12*r.k ≤ 111 := by
    linarith [hr.q.2,hr.u.2,hr.v.2,hr.k.2]
  have hsumz := mul_le_mul_of_nonneg_right hsum hz
  have hh := mul_nonneg (by linarith [hr.h1.1,hr.h2.1] : 0 ≤ r.h1+2*r.h2) hH
  dsimp [rateZ]
  nlinarith [hr.p.1]

theorem rate_H_lower (r : AssemblyRates) (hr : RateBox r) (z H : ℝ)
    (hz : 0 ≤ z) (hH : 0 ≤ H) : 15*z-3*H ≤ rateH r z H := by
  have hu := mul_le_mul_of_nonneg_right hr.u.1 hz
  have hv := mul_nonneg (by linarith [hr.v.1] : 0 ≤ r.v) (sq_nonneg z)
  have hh := mul_le_mul_of_nonneg_right
    (show r.h1+r.h2+r.d ≤ 3 by linarith [hr.h1.2,hr.h2.2,hr.d.2]) hH
  dsimp [rateH]
  nlinarith only [hu,hv,hh,hz]

end RobustPermanence
