import proofs.OverlappingSiphonInvasion.BoundaryBounds
import proofs.OverlappingSiphonInvasion.NormalizedSource

noncomputable section
namespace OverlappingSiphonInvasion

/-- A weighted siphon floor forces the private constituent directly. -/
theorem private_mass_forcing (α β γ η μ s a b c R l m r : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (hr : 0 < r) (hl : 0 ≤ l) (hs : l ≤ s) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbR : b ≤ R) (hcR : c ≤ R) (hm : m ≤ a+r*c) :
    β*l*m/r-(μ+(γ+η)*R+β*l/r)*a ≤ a*(α*s-γ*b-η*c-μ)+β*s*c := by
  have hs0 := hl.trans hs
  have hbs := sub_nonneg.mpr hbR
  have hcs := sub_nonneg.mpr hcR
  have hsl := sub_nonneg.mpr hs
  have hum := sub_nonneg.mpr hm
  have hh : 0 ≤ α*s*a+γ*a*(R-b)+η*a*(R-c)+β*(s-l)*c+β*l/r*(a+r*c-m) := by positivity
  rw [← sub_nonneg]
  convert hh using 1
  field_simp
  ring

theorem product_to_mass_floors (ru rv rj R δ : ℝ) (k : ℕ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (hR : 0 < R)
    (x : State) (hx : x ∈ populationBox R)
    (hP : δ ≤ massU ru x*massV rv x*massJ rj x^k) :
    δ/(((1+rv)*R)*(((2+rj)*R)^k)) ≤ massU ru x ∧
    δ/(((1+ru)*R)*(((2+rj)*R)^k)) ≤ massV rv x := by
  have ha := hx.1 1
  have hb := hx.1 2
  have hc := hx.1 3
  have haR := populationBox_coordinate_le R x hx 1
  have hbR := populationBox_coordinate_le R x hx 2
  have hcR := populationBox_coordinate_le R x hx 3
  have hU0 : 0 ≤ massU ru x := by dsimp [massU]; positivity
  have hV0 : 0 ≤ massV rv x := by dsimp [massV]; positivity
  have hJ0 : 0 ≤ massJ rj x := by dsimp [massJ]; positivity
  have hU : massU ru x ≤ (1+ru)*R := by
    dsimp [massU]
    nlinarith [mul_nonneg hru.le (sub_nonneg.mpr hcR)]
  have hV : massV rv x ≤ (1+rv)*R := by
    dsimp [massV]
    nlinarith [mul_nonneg hrv.le (sub_nonneg.mpr hcR)]
  have hJ : massJ rj x ≤ (2+rj)*R := by
    dsimp [massJ]
    nlinarith [mul_nonneg hrj.le (sub_nonneg.mpr hcR)]
  have hJk := pow_le_pow_left₀ hJ0 hJ k
  have hJpos : 0 < ((2+rj)*R)^k := by positivity
  constructor
  · apply (div_le_iff₀ (mul_pos (by positivity : 0 < (1+rv)*R) hJpos)).mpr
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hV hU0) hJk
      (pow_nonneg hJ0 k) (by positivity : 0 ≤ massU ru x*((1+rv)*R))
    exact hP.trans (by simpa only [mul_assoc] using hh)
  · apply (div_le_iff₀ (mul_pos (by positivity : 0 < (1+ru)*R) hJpos)).mpr
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right hU hV0) hJk
      (pow_nonneg hJ0 k) (by positivity : 0 ≤ ((1+ru)*R)*massV rv x)
    exact hP.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hh)

end OverlappingSiphonInvasion
