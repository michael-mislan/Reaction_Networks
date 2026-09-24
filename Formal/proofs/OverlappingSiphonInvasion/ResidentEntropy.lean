import proofs.OverlappingSiphonInvasion.ResidentStrictification

noncomputable section
namespace OverlappingSiphonInvasion

def scalarEntropy (e z : ℝ) : ℝ := z-e-e*Real.log (z/e)

theorem scalarEntropy_nonneg (e z : ℝ) (he : 0 < e) (hz : 0 < z) :
    0 ≤ scalarEntropy e z := by
  have hm := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hz he)) he.le
  have hid : e*(z/e-1) = z-e := by field_simp
  rw [hid] at hm
  dsimp [scalarEntropy]
  linarith

theorem scalarEntropy_derivative (e : ℝ) (z : ℝ → ℝ) (v t : ℝ)
    (he : 0 < e) (hz : 0 < z t) (hd : HasDerivAt z v t) :
    HasDerivAt (fun t => scalarEntropy e (z t)) ((1-e/z t)*v) t := by
  have hlog := (hd.div_const e).log (div_ne_zero (ne_of_gt hz) (ne_of_gt he))
  convert (hd.sub_const e).sub (hlog.const_mul e) using 1
  field_simp

def residentEntropy (se ue ε s u : ℝ) : ℝ :=
  scalarEntropy se s+scalarEntropy ue u+ε*(s-se)*(u-ue)

theorem residentEntropy_lower (se ue ε M s u : ℝ)
    (hse : 0 < se) (hue : 0 < ue) (hε : 0 ≤ ε)
    (hs : 0 < s) (hu : 0 < u) (hsM : s ≤ M) (huM : u ≤ M) :
    -ε*M*(ue+se) ≤ residentEntropy se ue ε s u := by
  have hH1 := scalarEntropy_nonneg se s hse hs
  have hH2 := scalarEntropy_nonneg ue u hue hu
  have h1 := mul_le_mul_of_nonneg_right hsM hue.le
  have h2 := mul_le_mul_of_nonneg_left huM hse.le
  have hcross : -M*(ue+se) ≤ (s-se)*(u-ue) := by
    nlinarith [mul_nonneg hs.le hu.le,mul_nonneg hse.le hue.le]
  have hm := mul_le_mul_of_nonneg_left hcross hε
  dsimp [residentEntropy]
  nlinarith only [hH1,hH2,hm]

theorem residentEntropy_derivative (se ue α μ₀ ε : ℝ) (s u : ℝ → ℝ) (t : ℝ)
    (hse : 0 < se) (hue : 0 < ue) (hs : 0 < s t) (hu : 0 < u t)
    (hds : HasDerivAt s (-(μ₀+α*ue)*(s t-se)-α*s t*(u t-ue)) t)
    (hdu : HasDerivAt u (α*u t*(s t-se)) t) :
    HasDerivAt (fun t => residentEntropy se ue ε (s t) (u t))
      (-((μ₀+α*ue)/s t-ε*α*u t)*(s t-se)^2-
        ε*(μ₀+α*ue)*(s t-se)*(u t-ue)-ε*α*s t*(u t-ue)^2) t := by
  have hdH := (scalarEntropy_derivative se s _ t hse hs hds).add
    (scalarEntropy_derivative ue u _ t hue hu hdu)
  have hdCross := (((hds.sub_const se).const_mul ε).mul (hdu.sub_const ue))
  convert hdH.add hdCross using 1
  rw [resident_entropy_identity _ _ _ _ _ _ (ne_of_gt hs) (ne_of_gt hu)]
  ring

end OverlappingSiphonInvasion
