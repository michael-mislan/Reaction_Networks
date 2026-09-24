import proofs.AssayInformation.CrossingDensity
import proofs.AssayInformation.SignCertificates

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace AssayInformation
open DiagnosticWindows
open scoped BigOperators

def rateExponent : Fin 5 → ℕ := ![5,404,603,602,401]
def signedCoefficient (p : ℝ) (i : Fin 5) : ℝ :=
  jumpRate i*(p*loadingCoeff i-5*modes5 i 0)
def densityPolynomial (p x : ℝ) : ℝ :=
  ∑ i, signedCoefficient p i*x^(rateExponent i-5)

theorem jumpRate_exponent (i : Fin 5) : jumpRate i = (rateExponent i:ℝ)/500 := by
  fin_cases i <;> norm_num [jumpRate,eigen5,rateExponent]

theorem exp_rate_power (n : ℕ) (t : ℝ) :
    Real.exp (-((n:ℝ)/500)*t) = (Real.exp (-t/500))^n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem signedDensity_polynomial (t : ℝ) :
    loadedDensity t-5*blankDensity t =
      (Real.exp (-t/500))^5*densityPolynomial (Real.exp (-4)) (Real.exp (-t/500)) := by
  unfold loadedDensity blankDensity suffixDensity densityMode densityPolynomial signedCoefficient
  simp_rw [jumpRate_exponent,exp_rate_power]
  norm_num [rateExponent,Fin.sum_univ_succ]
  ring

def lowerCoeff : Fin 5 → ℝ := ![-lowerA,-lowerD,-lowerG,lowerE,lowerB]
def upperCoeff : Fin 5 → ℝ := ![-upperA,-upperD,-upperG,upperE,upperB]

theorem coefficient_bounds (i : Fin 5) :
    lowerCoeff i ≤ signedCoefficient (Real.exp (-4)) i ∧
    signedCoefficient (Real.exp (-4)) i ≤ upperCoeff i := by
  have he := rescue_exp_5
  fin_cases i <;>
    norm_num [lowerCoeff,upperCoeff,signedCoefficient,jumpRate,eigen5,loadingCoeff,
      modes5,Fin.sum_univ_succ,loadIndex,Nat.factorial,lowerA,lowerB,lowerD,lowerE,lowerG,
      upperA,upperB,upperD,upperE,upperG] <;> constructor <;> linarith [he.1,he.2]

theorem densityPolynomial_bounds (x : ℝ) (hx : 0 ≤ x) :
    signedPoly lowerA lowerB lowerD lowerE lowerG x ≤ densityPolynomial (Real.exp (-4)) x ∧
    densityPolynomial (Real.exp (-4)) x ≤ signedPoly upperA upperB upperD upperE upperG x := by
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (coefficient_bounds i).1 (pow_nonneg hx (rateExponent i-5)))
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (coefficient_bounds i).2 (pow_nonneg hx (rateExponent i-5)))
  have hle : (∑ i, lowerCoeff i*x^(rateExponent i-5)) =
      signedPoly lowerA lowerB lowerD lowerE lowerG x := by
    norm_num [lowerCoeff,rateExponent,Fin.sum_univ_succ,signedPoly,grouped]; ring
  have hue : (∑ i, upperCoeff i*x^(rateExponent i-5)) =
      signedPoly upperA upperB upperD upperE upperG x := by
    norm_num [upperCoeff,rateExponent,Fin.sum_univ_succ,signedPoly,grouped]; ring
  rw [hle] at hl
  rw [hue] at hu
  exact ⟨hl,hu⟩

theorem early_density_order (t : ℝ) (ht : t ∈ Set.Icc 0 4) :
    5*blankDensity t ≤ loadedDensity t := by
  let x := Real.exp (-t/500)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
  have hxL : 124/125 ≤ x := by
    have h := Real.add_one_le_exp (-t/500)
    dsimp [x]
    linarith [ht.2]
  have hp := (lower_poly_positive x ⟨hxL,hx1⟩).trans_le (densityPolynomial_bounds x hx0).1
  have hd := signedDensity_polynomial t
  have hm := mul_nonneg (pow_nonneg hx0 5) hp.le
  change 0 ≤ (Real.exp (-t/500))^5*densityPolynomial (Real.exp (-4)) (Real.exp (-t/500)) at hm
  linarith

theorem late_density_order (t : ℝ) (ht : 5 ≤ t) :
    loadedDensity t ≤ 5*blankDensity t := by
  let x := Real.exp (-t/500)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hxU : x ≤ 9901/10000 := by
    have h := Real.add_one_le_exp (t/500)
    have hp := Real.exp_pos (t/500)
    have hi : Real.exp (-t/500)*Real.exp (t/500)=1 := by
      rw [← Real.exp_add]
      have hz : -t/500+t/500=0 := by ring
      rw [hz,Real.exp_zero]
    dsimp [x]
    nlinarith [Real.exp_pos (-t/500)]
  have hp := (densityPolynomial_bounds x hx0).2.trans_lt (upper_poly_negative x ⟨hx0,hxU⟩)
  have hd := signedDensity_polynomial t
  have hm := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0 5) hp.le
  change (Real.exp (-t/500))^5*densityPolynomial (Real.exp (-4)) (Real.exp (-t/500)) ≤ 0 at hm
  linarith

end AssayInformation
