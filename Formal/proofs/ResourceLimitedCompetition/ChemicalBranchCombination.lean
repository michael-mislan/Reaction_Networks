import proofs.ResourceLimitedCompetition.ChemicalTailScalar

namespace ResourceLimitedCompetition

theorem exponential_product_add (a b c : ℝ) (h : a+b=c) :
    Real.exp a*Real.exp b=Real.exp c := by rw [← Real.exp_add,h]

theorem chemical_branch_combination (N : ℕ) (M t pO pD pP : ℝ)
    (hO : Real.exp (16*chemicalScale N)*pO ≤
      7*M*Real.exp (4*chemicalScale N)+t*(8*M*(chemicalScale N/672)*Real.exp (chemicalScale N/2)))
    (hD : Real.exp (2*chemicalScale N)*pD ≤
      M*Real.exp (4*chemicalScale N-(N : ℝ)/1000000000000000)+
        t*(8*M*(chemicalScale N/672)*Real.exp (chemicalScale N/2)))
    (hP : pP ≤ 24*M*Real.exp (-(N : ℝ)*(1/1000000)^2/35)) :
    pO+pD+pP ≤ chemicalRawError N M t := by
  let u := chemicalScale N
  have hcancel (a p : ℝ) : Real.exp (-a)*(Real.exp a*p)=p := by
    rw [← mul_assoc,← Real.exp_add]
    simp
  have h1 := mul_le_mul_of_nonneg_left hO (Real.exp_pos (-(16*u))).le
  have h2 := mul_le_mul_of_nonneg_left hD (Real.exp_pos (-(2*u))).le
  change Real.exp (-(16*u))*(Real.exp (16*u)*pO) ≤ _ at h1
  change Real.exp (-(2*u))*(Real.exp (2*u)*pD) ≤ _ at h2
  rw [hcancel] at h1 h2
  have heO1 := exponential_product_add (-(16*u)) (4*u) (-12*u) (by ring)
  have heO2 := exponential_product_add (-(16*u)) (u/2) (-(31/2)*u) (by ring)
  have heD1 := exponential_product_add (-(2*u)) (4*u-(N : ℝ)/1000000000000000)
    (2*u-(N : ℝ)/1000000000000000) (by ring)
  have heD2 := exponential_product_add (-(2*u)) (u/2) (-(3/2)*u) (by ring)
  have ho : Real.exp (-(16*u))*(7*M*Real.exp (4*u)+t*(8*M*(u/672)*Real.exp (u/2))) =
      7*M*Real.exp (-12*u)+(M*t/84)*u*Real.exp (-(31/2)*u) := by
    calc
      _ = 7*M*(Real.exp (-(16*u))*Real.exp (4*u))+
          (M*t/84)*u*(Real.exp (-(16*u))*Real.exp (u/2)) := by ring
      _ = _ := by rw [heO1,heO2]
  have hd : Real.exp (-(2*u))*(M*Real.exp (4*u-(N : ℝ)/1000000000000000)+
      t*(8*M*(u/672)*Real.exp (u/2))) =
      M*Real.exp (2*u-(N : ℝ)/1000000000000000)+(M*t/84)*u*Real.exp (-(3/2)*u) := by
    calc
      _ = M*(Real.exp (-(2*u))*Real.exp (4*u-(N : ℝ)/1000000000000000))+
          (M*t/84)*u*(Real.exp (-(2*u))*Real.exp (u/2)) := by ring
      _ = _ := by rw [heD1,heD2]
  change pO ≤ Real.exp (-(16*u))*(7*M*Real.exp (4*u)+t*(8*M*(u/672)*Real.exp (u/2))) at h1
  change pD ≤ Real.exp (-(2*u))*(M*Real.exp (4*u-(N : ℝ)/1000000000000000)+
    t*(8*M*(u/672)*Real.exp (u/2))) at h2
  rw [ho] at h1
  rw [hd] at h2
  change pO+pD+pP ≤ 7*M*Real.exp (-12*u)+(M*t/84)*u*Real.exp (-(31/2)*u)+
    M*Real.exp (2*u-(N : ℝ)/1000000000000000)+(M*t/84)*u*Real.exp (-(3/2)*u)+
      24*M*Real.exp (-(N : ℝ)*(1/1000000)^2/35)
  linarith only [h1,h2,hP]

end ResourceLimitedCompetition
