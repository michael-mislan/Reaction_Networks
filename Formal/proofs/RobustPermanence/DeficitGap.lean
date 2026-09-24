import proofs.CoreCouplingGlobal.Response

namespace RobustPermanence
open CoreCouplingGlobal

noncomputable def dissipation (r F Z K : ℝ) : ℝ :=
  r^2/4 + F^2/1000 + Z^2/364 + K^2/4000

theorem dissipation_nonneg (r F Z K : ℝ) : 0 ≤ dissipation r F Z K := by
  unfold dissipation
  positivity

/-- A positive-coefficient expansion at the edge of the low-resource interval. -/
theorem low_resource_polynomial (z : ℝ) (hz : z ≤ 3/4) :
    0 ≤ (33-1089/50000-23/100 : ℝ)*(z+2)*20001-60*(1+z)*20001
      -(16*z+4*z^2)*(z+2)*20001+30000*(16*z+2*z^2)*(z+2) := by
  have ht : 0 ≤ 3/4-z := by linarith
  calc
    _ = 32094021/200000 + (3944380089/50000)*(3/4-z) +
        74967*(3/4-z)^2 + 20004*(3/4-z)^3 := by ring
    _ ≥ 0 := by positivity

/-- The literal response equations force a residual gap at low resource.
No response-surface invariance or interpolation assumption is used. -/
theorem low_resource_separation (e B z H : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 3/4) :
    23/100 ≤ |responseTotal e B-(1+z)*B-16*z-4*z^2+3*H| +
      |60-(2+z)*B| + (3/2)*|16*z+2*z^2-(20001/10000)*H| := by
  let F := 60-(2+z)*B
  let Z := responseTotal e B-(1+z)*B-16*z-4*z^2+3*H
  let K := 16*z+2*z^2-(20001/10000)*H
  obtain ⟨ha,ha'⟩ := response_bounds e B he he' hB hB'
  have ha2 : (responseA e B)^2 ≤ 1089 := by nlinarith
  have heaa := mul_le_mul he' ha2 (sq_nonneg (responseA e B)) (by norm_num : (0:ℝ) ≤ 1/50000)
  have hq := response_quadratic e B he he' hB hB'
  have heb := mul_nonneg he (by linarith : 0 ≤ B)
  have htotal : 0 ≤ responseTotal e B - 33 + 1089/50000 := by
    dsimp [responseTotal]
    nlinarith only [hq, heaa, heb]
  have hp := low_resource_polynomial z hz'
  have htot := mul_nonneg (by positivity : 0 ≤ (z+2)*20001) htotal
  have hF : 0 ≤ (1+z)*F+(z+2)*|F| := by
    have hh := mul_nonneg (by linarith : 0 ≤ 1+z) (by linarith [neg_abs_le F] : 0 ≤ F+|F|)
    nlinarith only [hh, abs_nonneg F]
  have hK : 0 ≤ (z+2)*((60003/2)*|K|-30000*K) := by
    apply mul_nonneg (by linarith)
    nlinarith only [le_abs_self K, abs_nonneg K]
  have hid :
      (z+2)*20001*(Z+|F|+(3/2)*|K|-23/100) =
      ((33-1089/50000-23/100)*(z+2)*20001-60*(1+z)*20001
       -(16*z+4*z^2)*(z+2)*20001+30000*(16*z+2*z^2)*(z+2)) +
      (z+2)*20001*(responseTotal e B-33+1089/50000) +
      20001*((1+z)*F+(z+2)*|F|) + (z+2)*((60003/2)*|K|-30000*K) := by
    dsimp [F,Z,K]
    ring
  have hh : 0 ≤ (z+2)*20001*(Z+|F|+(3/2)*|K|-23/100) := by
    rw [hid]
    linarith only [hp, htot, hF, hK]
  have hh' := (nonneg_of_mul_nonneg_right hh (by positivity : 0 < (z+2)*20001))
  change 23/100 ≤ |Z|+|F|+(3/2)*|K|
  linarith only [hh', le_abs_self Z]

theorem residual_gap (r F Z K : ℝ)
    (hsep : 23/100 ≤ |Z|+|F|+(3/2)*|K|) :
    529/103640000 ≤ dissipation r F Z K := by
  have hcs : (|Z|+|F|+(3/2)*|K|)^2 ≤
      10364*(Z^2/364+F^2/1000+K^2/4000) := by
    have h1 := sq_nonneg (1000*|Z|-364*|F|)
    have h2 := sq_nonneg (6000*|Z|-364*|K|)
    have h3 := sq_nonneg (6000*|F|-1000*|K|)
    nlinarith only [h1,h2,h3,sq_abs Z,sq_abs F,sq_abs K]
  have hs : (23/100:ℝ)^2 ≤ (|Z|+|F|+(3/2)*|K|)^2 := by
    nlinarith only [hsep]
  unfold dissipation
  nlinarith only [hcs,hs,sq_nonneg r]

theorem corrected_boundary_growth (z D : ℝ) (hz : 0 ≤ z) (hD : 0 ≤ D)
    (hgap : z ≤ 3/4 → 529/103640000 ≤ D) :
    1/4 ≤ z-1/2+150000*D := by
  by_cases hl : z ≤ 3/4
  · linarith [hgap hl]
  · linarith

end RobustPermanence
