import proofs.InheritedCellAssay.ThreePGFCertificate

namespace InheritedCellAssay.PositiveScalar
open ScalarCount

/-- A deliberately loose rational box suffices; the source must prove this box. -/
theorem box_small (m p : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 13/25)
    (hp : 20/27 ≤ p) (hp1 : p ≤ 1) :
    (64/21)*(1-7*(1-m*p/(p+1))+14*(1-3*m*p/(p+3))-
      8*(1-7*m*p/(p+7))) < 1/20 := by
  have hp0 : 0 ≤ p := by linarith
  have h1 : p+1 ≠ 0 := by positivity
  have h3 : p+3 ≠ 0 := by positivity
  have h7 : p+7 ≠ 0 := by positivity
  have he : (64/21)*(1-7*(1-m*p/(p+1))+14*(1-3*m*p/(p+3))-
      8*(1-7*m*p/(p+7))) = 64*m*p*(1-p)^2/((p+1)*(p+3)*(p+7)) := by
    field_simp [h1,h3,h7]
    ring
  rw [he]
  have hs : (1-p)^2 ≤ (7/27 : ℝ)^2 := by nlinarith
  have hmp : m*p ≤ 13/25 := (mul_le_of_le_one_right hm hp1).trans hm1
  have hn : 64*m*p*(1-p)^2 ≤ 64*(13/25 : ℝ)*(7/27)^2 := by
    calc
      _ = 64*(m*p)*(1-p)^2 := by ring
      _ ≤ 64*(13/25 : ℝ)*(7/27)^2 := by gcongr
  have hd : (5/3 : ℝ)*(11/3)*(23/3) ≤ (p+1)*(p+3)*(p+7) := by
    gcongr <;> linarith
  apply (div_lt_iff₀ (by positivity : 0 < (p+1)*(p+3)*(p+7))).mpr
  nlinarith

theorem coverage_of_box (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hn : HasSum w 1)
    (m p : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 13/25) (hp : 20/27 ≤ p) (hp1 : p ≤ 1)
    (ha : HasSum (fun n => w n*(1/2)^n) (1-m*p/(p+1)))
    (hb : HasSum (fun n => w n*(1/4)^n) (1-3*m*p/(p+3)))
    (hc : HasSum (fun n => w n*(1/8)^n) (1-7*m*p/(p+7))) :
    19/20 < w 0+w 1+w 2 := by
  have h := coverage_from_three_pgf w hw hn _ _ _ ha hb hc
  have hs := box_small m p hm hm1 hp hp1
  linarith

theorem relaxed_box_small (m p : ℝ) (_hm : 0 ≤ m) (hm1 : m ≤ 11/20)
    (hp : 5/7 ≤ p) (hp1 : p ≤ 1) :
    (64/21)*(1-7*(1-m*p/(p+1))+14*(1-3*m*p/(p+3))-
      8*(1-7*m*p/(p+7))) < 1/20 := by
  have hp0 : 0 ≤ p := by linarith
  have h1 : p+1 ≠ 0 := by positivity
  have h3 : p+3 ≠ 0 := by positivity
  have h7 : p+7 ≠ 0 := by positivity
  have he : (64/21)*(1-7*(1-m*p/(p+1))+14*(1-3*m*p/(p+3))-
      8*(1-7*m*p/(p+7))) = 64*m*p*(1-p)^2/((p+1)*(p+3)*(p+7)) := by
    field_simp [h1,h3,h7]
    ring
  rw [he]
  have hb : 0 ≤ -p^2+(9/7)*p-4/49 := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hs : p*(1-p)^2 ≤ 20/343 := by
    nlinarith [mul_nonneg (show 0 ≤ p-5/7 by linarith) hb]
  have hn : 64*m*p*(1-p)^2 ≤ 64*(11/20 : ℝ)*(20/343) := by
    calc
      _ = 64*m*(p*(1-p)^2) := by ring
      _ ≤ 64*(11/20 : ℝ)*(20/343) := by gcongr
  have hd : (12/7 : ℝ)*(26/7)*(54/7) ≤ (p+1)*(p+3)*(p+7) := by
    gcongr <;> linarith
  apply (div_lt_iff₀ (by positivity : 0 < (p+1)*(p+3)*(p+7))).mpr
  nlinarith

theorem coverage_of_relaxed_box (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hn : HasSum w 1)
    (m p : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 11/20) (hp : 5/7 ≤ p) (hp1 : p ≤ 1)
    (ha : HasSum (fun n => w n*(1/2)^n) (1-m*p/(p+1)))
    (hb : HasSum (fun n => w n*(1/4)^n) (1-3*m*p/(p+3)))
    (hc : HasSum (fun n => w n*(1/8)^n) (1-7*m*p/(p+7))) :
    19/20 < w 0+w 1+w 2 := by
  have h := coverage_from_three_pgf w hw hn _ _ _ ha hb hc
  have hs := relaxed_box_small m p hm hm1 hp hp1
  linarith

end InheritedCellAssay.PositiveScalar
