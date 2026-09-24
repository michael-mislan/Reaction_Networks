import proofs.RobustPermanence.ConsumerDissipation

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC

/-- Uniform bounds for the four response-coordinate gradient components. -/
theorem response_gradient_bounds (e A B z H : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7) :
    |Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B| ≤ 140 ∧
    |(responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)/((z+1)*(z+2))| ≤ 1000 ∧
    |3*(responseLog (responsePhi H)-responseLog z)| ≤ 18 ∧
    |A+B-responseTotal e B| ≤ 67 ∧ |responseSlope e B| ≤ 1/500 := by
  obtain ⟨_,_,hc,hc'⟩ := response_coefficient_bounds e A B he he' hA hA' hB hB'
  obtain ⟨ha,ha'⟩ := response_bounds e B he he' hB hB'
  have htlo : 1 ≤ responseTotal e B := by dsimp [responseTotal]; linarith
  have hthi : responseTotal e B ≤ 67 := by dsimp [responseTotal]; linarith
  have hprod : 0 ≤ (1+z)*B := mul_nonneg (by linarith) (by linarith)
  have hprod' : (1+z)*B ≤ 442 := by
    have hh := mul_le_mul (by linarith : 1+z ≤ 13) hB' (by linarith : 0 ≤ B) (by norm_num : (0:ℝ) ≤ 13)
    linarith only [hh]
  have hz2 : z^2 ≤ 144 := by nlinarith
  have hZ : |responseTotal e B-(1+z)*B-16*z-4*z^2+3*H| ≤ 2000 := by
    apply abs_le.2
    constructor <;> nlinarith only [htlo,hthi,hprod,hprod',hz,hz',hz2,hH,hH',sq_nonneg z]
  have hw : 2 ≤ (z+1)*(z+2) := by nlinarith
  obtain ⟨m,hm,hm',hmeq⟩ := fork_gradient_secant B (responseSlope e B) z hB hB' hz hz' hc hc'
  have hF : |60-(2+z)*B| ≤ 536 := by
    have hh := mul_le_mul (by linarith : 2+z ≤ 14) hB' (by linarith : 0 ≤ B) (by norm_num : (0:ℝ) ≤ 14)
    have hl := mul_nonneg (by linarith : 0 ≤ 2+z) (by linarith : 0 ≤ B)
    apply abs_le.2
    constructor <;> linarith only [hh,hl]
  have hgrad : Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B =
      -m*(60-(2+z)*B) := by dsimp [responsePIntegrand]; linarith only [hmeq]
  obtain ⟨hp,hp'⟩ := responsePhi_bounds H hH hH'
  obtain ⟨n,hn,hn',hne⟩ := responseLog_secant z (responsePhi H) hz hz' hp hp'
  have hdelta : |responsePhi H-z| ≤ 12 := abs_le.2 ⟨by linarith,by linarith⟩
  refine ⟨?_,?_,?_,?_,abs_le.2 ⟨hc,hc'⟩⟩
  · rw [hgrad,abs_mul,abs_neg,abs_of_nonneg (by linarith : 0 ≤ m)]
    have hh := mul_le_mul hm' hF (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 13/50)
    linarith only [hh]
  · rw [abs_div,abs_of_nonneg (by linarith : 0 ≤ (z+1)*(z+2))]
    apply (div_le_iff₀ (by linarith : 0 < (z+1)*(z+2))).2
    linarith only [hZ,hw]
  · rw [hne,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3),abs_of_nonneg (by linarith : 0 ≤ n)]
    have hh := mul_le_mul hn' hdelta (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)
    linarith only [hh]
  · apply abs_le.2
    constructor <;> linarith

theorem potential_direction_bound (e A B z H a' b' z' H' : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7)
    (ha : |a'| ≤ 384) (hb : |b'| ≤ 384) (hzz : |z'| ≤ 384) (hh : |H'| ≤ 384) :
    |(Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B)*b'
      -(responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)/((z+1)*(z+2))*z'
      +3*(responseLog (responsePhi H)-responseLog z)*H'
      +(A+B-responseTotal e B)*(a'+b'-responseSlope e B*b')| ≤ 1000000 := by
  obtain ⟨hgB,hgz,hgH,hr,hc⟩ := response_gradient_bounds e A B z H he he' hA hA' hB hB' hz hz' hH hH'
  have hcB : |responseSlope e B*b'| ≤ 384/500 := by
    rw [abs_mul]
    calc
      _ ≤ (1/500:ℝ)*384 := mul_le_mul hc hb (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hdr : |a'+b'-responseSlope e B*b'| ≤ 1200 := by
    have h1 := abs_sub (a'+b') (responseSlope e B*b')
    have h2 := abs_add_le a' b'
    linarith only [h1,h2,ha,hb,hcB]
  have h1 := mul_le_mul hgB hb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 140)
  have h2 := mul_le_mul hgz hzz (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1000)
  have h3 := mul_le_mul hgH hh (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 18)
  have h4 := mul_le_mul hr hdr (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 67)
  rw [← abs_mul] at h1 h2 h3 h4
  calc
    _ ≤ |(Real.log (z+2)-responseSlope e B*responseLog z+responsePIntegrand e B)*b'| +
        |(responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)/((z+1)*(z+2))*z'| +
        |3*(responseLog (responsePhi H)-responseLog z)*H'| +
        |(A+B-responseTotal e B)*(a'+b'-responseSlope e B*b')| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ 1000000 := by linarith only [h1,h2,h3,h4]

end RobustPermanence
