import proofs.OverlappingSiphonInvasion.ResidentInvasion

noncomputable section
namespace OverlappingSiphonInvasion

theorem negative_covector_iff (A B C D : ℝ) (hB : 0 < B) (hC : 0 < C) :
    (∃ r : ℝ, 0 < r ∧ A+r*C < 0 ∧ B+r*D < 0) ↔
      A < 0 ∧ D < 0 ∧ B*C < A*D := by
  constructor
  · rintro ⟨r,hr,h1,h2⟩
    have hA : A < 0 := by nlinarith [mul_pos hr hC]
    have hD : D < 0 := by
      by_contra hh
      have hd := le_of_not_gt hh
      nlinarith [mul_nonneg hr.le hd]
    refine ⟨hA,hD,?_⟩
    have hh1 := mul_neg_of_neg_of_pos h1 (neg_pos.mpr hD)
    have hh2 := mul_neg_of_neg_of_pos h2 hC
    nlinarith only [hh1,hh2]
  · rintro ⟨hA,hD,hdet⟩
    have hinterval : B/(-D) < (-A)/C := by
      apply (div_lt_div_iff₀ (neg_pos.mpr hD) hC).mpr
      nlinarith only [hdet]
    obtain ⟨r,hrl,hru⟩ := exists_between hinterval
    have hr := (div_pos hB (neg_pos.mpr hD)).trans hrl
    have hh1 := (lt_div_iff₀ hC).mp hru
    have hh2 := (div_lt_iff₀ (neg_pos.mpr hD)).mp hrl
    exact ⟨r,hr,by linarith,by nlinarith only [hh2]⟩

theorem resident_lyapunov_identity (g h d x y : ℝ) :
    2*(d*(h+d)*x+g*d*y)*(-g*x-h*y)+
      2*(g*d*x+(h*(h+d)+g^2)*y)*(d*x) =
        -2*g*h*d*(x^2+y^2) := by ring

theorem resident_lyapunov_det (g h d : ℝ) :
    d*(h+d)*(h*(h+d)+g^2)-(g*d)^2 = d*h*((h+d)^2+g^2) := by ring

theorem splitting_forbidden_zero (n f v : ℝ) (hn : n = 0)
    (he : n = f-v) (hf : 0 ≤ f) (hv : v ≤ 0) : f = 0 ∧ v = 0 := by
  constructor <;> linarith

theorem witness_threshold_det (β : ℝ) :
    (residentBlock1 (witness β) (1/2) (7/2)).det = 51/400-7*β/20 := by
  simp [residentBlock1,witness,Matrix.det_fin_two]
  ring

/-- Resident coordinates and positive covector bounds certify the entire
independent one-percent box about the invading witness. -/
def OnePercentBox (p : Rates) : Prop :=
  ∀ i, (99/100 : ℝ)*rateVector (witness 1) i ≤ rateVector p i ∧
    rateVector p i ≤ (101/100 : ℝ)*rateVector (witness 1) i

set_option maxHeartbeats 800000 in
theorem one_percent_mutual_invasion (p : Rates) (hb : OnePercentBox p) :
    PositiveRates p ∧ p.mu1/p.alpha1 < p.recruitment/p.mu0 ∧
      p.mu2/p.alpha2 < p.recruitment/p.mu0 ∧
      (5601/101000 : ℝ) ≤
        p.alpha2*(p.mu1/p.alpha1)+(2*p.gamma1+p.gamma2)*
          ((p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1)-p.mu2 ∧
      (5601/101000 : ℝ) ≤
        (p.beta2/2+p.alpha3)*(p.mu1/p.alpha1)+p.eta1*
          ((p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1)-p.mu3 ∧
      (8701/25250 : ℝ) ≤
        p.alpha1*(p.mu2/p.alpha2)+p.gamma2*
          ((p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2)-p.mu1 ∧
      (8701/25250 : ℝ) ≤
        (p.beta1+p.alpha3)*(p.mu2/p.alpha2)+p.eta2*
          ((p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2)-p.mu3 := by
  have hΛ : (99/100 : ℝ)*4 ≤ p.recruitment ∧ p.recruitment ≤ (101/100 : ℝ)*4 := hb 0
  have hα1 : (99/100 : ℝ)*2 ≤ p.alpha1 ∧ p.alpha1 ≤ (101/100 : ℝ)*2 := hb 1
  have hα2 : (99/100 : ℝ)*1 ≤ p.alpha2 ∧ p.alpha2 ≤ (101/100 : ℝ)*1 := hb 2
  have hα3 : (99/100 : ℝ)*1 ≤ p.alpha3 ∧ p.alpha3 ≤ (101/100 : ℝ)*1 := hb 3
  have hη1 : (99/100 : ℝ)*(1/10) ≤ p.eta1 ∧ p.eta1 ≤ (101/100 : ℝ)*(1/10) := hb 4
  have hη2 : (99/100 : ℝ)*(1/10) ≤ p.eta2 ∧ p.eta2 ≤ (101/100 : ℝ)*(1/10) := hb 5
  have hγ1 : (99/100 : ℝ)*(1/10) ≤ p.gamma1 ∧ p.gamma1 ≤ (101/100 : ℝ)*(1/10) := hb 6
  have hγ2 : (99/100 : ℝ)*(1/10) ≤ p.gamma2 ∧ p.gamma2 ≤ (101/100 : ℝ)*(1/10) := hb 7
  have hβ1 : (99/100 : ℝ)*(1/10) ≤ p.beta1 ∧ p.beta1 ≤ (101/100 : ℝ)*(1/10) := hb 8
  have hβ2 : (99/100 : ℝ)*1 ≤ p.beta2 ∧ p.beta2 ≤ (101/100 : ℝ)*1 := hb 9
  have hμ0 : (99/100 : ℝ)*1 ≤ p.mu0 ∧ p.mu0 ≤ (101/100 : ℝ)*1 := hb 10
  have hμ1 : (99/100 : ℝ)*1 ≤ p.mu1 ∧ p.mu1 ≤ (101/100 : ℝ)*1 := hb 11
  have hμ2 : (99/100 : ℝ)*1 ≤ p.mu2 ∧ p.mu2 ≤ (101/100 : ℝ)*1 := hb 12
  have hμ3 : (99/100 : ℝ)*1 ≤ p.mu3 ∧ p.mu3 ≤ (101/100 : ℝ)*1 := hb 13
  norm_num [rateVector,witness] at hΛ hα1 hα2 hα3 hη1 hη2 hγ1 hγ2 hβ1 hβ2 hμ0 hμ1 hμ2 hμ3
  have hpos : PositiveRates p := by
    intro i
    fin_cases i <;> norm_num [rateVector] <;> linarith
  have ha1 : 0 < p.alpha1 := by linarith
  have ha2 : 0 < p.alpha2 := by linarith
  have hm0 : 0 < p.mu0 := by linarith
  have hm1 : 0 < p.mu1 := by linarith
  have hm2 : 0 < p.mu2 := by linarith
  have hs1 : (99/202 : ℝ) ≤ p.mu1/p.alpha1 := by
    apply (le_div_iff₀ ha1).mpr
    linarith
  have hs2 : (99/101 : ℝ) ≤ p.mu2/p.alpha2 := by
    apply (le_div_iff₀ ha2).mpr
    linarith
  have hu1eq : (p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1 =
      p.recruitment/p.mu1-p.mu0/p.alpha1 := by field_simp
  have hu2eq : (p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2 =
      p.recruitment/p.mu2-p.mu0/p.alpha2 := by field_simp
  have hu1 : (68207/19998 : ℝ) ≤ (p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1 := by
    have hl : (396/101 : ℝ) ≤ p.recruitment/p.mu1 := (le_div_iff₀ hm1).mpr (by linarith)
    have hh : p.mu0/p.alpha1 ≤ (101/198 : ℝ) := (div_le_iff₀ ha1).mpr (by linarith)
    rw [hu1eq]
    linarith
  have hu2 : (29003/9999 : ℝ) ≤ (p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2 := by
    have hl : (396/101 : ℝ) ≤ p.recruitment/p.mu2 := (le_div_iff₀ hm2).mpr (by linarith)
    have hh : p.mu0/p.alpha2 ≤ (101/99 : ℝ) := (div_le_iff₀ ha2).mpr (by linarith)
    rw [hu2eq]
    linarith
  have he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0 := by
    apply (lt_div_iff₀ hm0).mpr
    have hh := (le_div_iff₀ hm1).mp hu1
    nlinarith only [hh,mul_pos hm1 (by norm_num : (0:ℝ) < 68207/19998)]
  have he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0 := by
    apply (lt_div_iff₀ hm0).mpr
    have hh := (le_div_iff₀ hm2).mp hu2
    nlinarith only [hh,mul_pos hm2 (by norm_num : (0:ℝ) < 29003/9999)]
  have mult (a b al bl : ℝ) (ha : al ≤ a) (hb' : bl ≤ b)
      (hal : 0 ≤ al) (hbl : 0 ≤ bl) : al*bl ≤ a*b :=
    mul_le_mul ha hb' hbl (hal.trans ha)
  refine ⟨hpos,he1,he2,?_,?_,?_,?_⟩
  · have h1 := mult _ _ (99/100) (99/202) hα2.1 hs1 (by norm_num) (by norm_num)
    have h2 := mult _ _ (297/1000) (68207/19998) (by linarith : (297/1000:ℝ) ≤ 2*p.gamma1+p.gamma2) hu1 (by norm_num) (by norm_num)
    linarith only [h1,h2,hμ2.2]
  · have h1 := mult _ _ (297/200) (99/202) (by linarith : (297/200:ℝ) ≤ p.beta2/2+p.alpha3) hs1 (by norm_num) (by norm_num)
    have h2 := mult _ _ (99/1000) (68207/19998) hη1.1 hu1 (by norm_num) (by norm_num)
    linarith only [h1,h2,hμ3.2]
  · have h1 := mult _ _ (99/50) (99/101) hα1.1 hs2 (by norm_num) (by norm_num)
    have h2 := mult _ _ (99/1000) (29003/9999) hγ2.1 hu2 (by norm_num) (by norm_num)
    linarith only [h1,h2,hμ1.2]
  · have h1 := mult _ _ (1089/1000) (99/101) (by linarith : (1089/1000:ℝ) ≤ p.beta1+p.alpha3) hs2 (by norm_num) (by norm_num)
    have h2 := mult _ _ (99/1000) (29003/9999) hη2.1 hu2 (by norm_num) (by norm_num)
    linarith only [h1,h2,hμ3.2]

end OverlappingSiphonInvasion
