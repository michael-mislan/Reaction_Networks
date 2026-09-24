import proofs.OverlappingSiphonInvasion.GeneralExistence

noncomputable section
namespace OverlappingSiphonInvasion

abbrev LiftState := State × State
def privateA (p : Rates) (x : State) : ℝ := p.alpha1*x 0-p.gamma1*x 2-p.eta1*x 3-p.mu1
def privateB (p : Rates) (x : State) : ℝ := p.alpha2*x 0-p.gamma2*x 1-p.eta2*x 3-p.mu2
def sharedC (p : Rates) (x : State) : ℝ := p.eta1*x 1+p.eta2*x 2+p.alpha3*x 0-p.mu3
def massU (r : ℝ) (x : State) : ℝ := x 1+r*x 3
def massV (r : ℝ) (x : State) : ℝ := x 2+r*x 3
def massJ (r : ℝ) (x : State) : ℝ := x 1+x 2+r*x 3

def normalHU (p : Rates) (r : ℝ) (x : State) (θ : ℝ) : ℝ :=
  (privateA p x+r*(p.gamma1+p.gamma2)*x 2)*θ+
    ((p.beta1*x 0+r*sharedC p x)/r)*(1-θ)
def normalHV (p : Rates) (r : ℝ) (x : State) (φ : ℝ) : ℝ :=
  (privateB p x+r*(p.gamma1+p.gamma2)*x 1)*φ+
    ((p.beta2*x 0+r*sharedC p x)/r)*(1-φ)
def normalHJ (p : Rates) (r : ℝ) (x : State) (ξ ζ : ℝ) : ℝ :=
  privateA p x*ξ+(privateB p x+r*(p.gamma1+p.gamma2)*x 1)*ζ+
    (((p.beta1+p.beta2)*x 0+r*sharedC p x)/r)*(1-ξ-ζ)

def normalizedField (p : Rates) (ru rv rj : ℝ) (z : LiftState) : LiftState :=
  (field p z.1,
    ![privateA p z.1*z.2 0+p.beta1*z.1 0/ru*(1-z.2 0)-z.2 0*normalHU p ru z.1 (z.2 0),
      privateB p z.1*z.2 1+p.beta2*z.1 0/rv*(1-z.2 1)-z.2 1*normalHV p rv z.1 (z.2 1),
      privateA p z.1*z.2 2+p.beta1*z.1 0/rj*(1-z.2 2-z.2 3)-
        z.2 2*normalHJ p rj z.1 (z.2 2) (z.2 3),
      privateB p z.1*z.2 3+p.beta2*z.1 0/rj*(1-z.2 2-z.2 3)-
        z.2 3*normalHJ p rj z.1 (z.2 2) (z.2 3)])

def normalizedEmbedding (ru rv rj : ℝ) (x : State) : LiftState :=
  (x,![x 1/massU ru x,x 2/massV rv x,x 1/massJ rj x,x 2/massJ rj x])

private theorem weighted_two_identity (a c r m n : ℝ)
    (hr : r ≠ 0) (hz : a+r*c ≠ 0) :
    (m*(a/(a+r*c))+(n/r)*(1-a/(a+r*c)))*(a+r*c) = m*a+n*c := by
  field_simp
  ring

private theorem weighted_three_identity (a b c r m n q : ℝ)
    (hr : r ≠ 0) (hz : a+b+r*c ≠ 0) :
    (m*(a/(a+b+r*c))+n*(b/(a+b+r*c))+
      (q/r)*(1-a/(a+b+r*c)-b/(a+b+r*c)))*(a+b+r*c) = m*a+n*b+q*c := by
  field_simp
  ring

theorem massU_field (p : Rates) (r : ℝ) (x : State) :
    field p x 1+r*field p x 3 =
      (privateA p x+r*(p.gamma1+p.gamma2)*x 2)*x 1+
        (p.beta1*x 0+r*sharedC p x)*x 3 := by
  simp [field,privateA,sharedC]
  ring

theorem massV_field (p : Rates) (r : ℝ) (x : State) :
    field p x 2+r*field p x 3 =
      (privateB p x+r*(p.gamma1+p.gamma2)*x 1)*x 2+
        (p.beta2*x 0+r*sharedC p x)*x 3 := by
  simp [field,privateB,sharedC]
  ring

theorem massJ_field (p : Rates) (r : ℝ) (x : State) :
    field p x 1+field p x 2+r*field p x 3 =
      privateA p x*x 1+(privateB p x+r*(p.gamma1+p.gamma2)*x 1)*x 2+
        ((p.beta1+p.beta2)*x 0+r*sharedC p x)*x 3 := by
  simp [field,privateA,privateB,sharedC]
  ring

theorem normalHU_physical (p : Rates) (r : ℝ) (x : State)
    (hr : r ≠ 0) (hU : massU r x ≠ 0) :
    normalHU p r x (x 1/massU r x)*massU r x = field p x 1+r*field p x 3 := by
  rw [massU_field]
  exact weighted_two_identity _ _ _ _ _ hr hU

theorem normalHV_physical (p : Rates) (r : ℝ) (x : State)
    (hr : r ≠ 0) (hV : massV r x ≠ 0) :
    normalHV p r x (x 2/massV r x)*massV r x = field p x 2+r*field p x 3 := by
  rw [massV_field]
  exact weighted_two_identity _ _ _ _ _ hr hV

theorem normalHJ_physical (p : Rates) (r : ℝ) (x : State)
    (hr : r ≠ 0) (hJ : massJ r x ≠ 0) :
    normalHJ p r x (x 1/massJ r x) (x 2/massJ r x)*massJ r x =
      field p x 1+field p x 2+r*field p x 3 := by
  rw [massJ_field]
  exact weighted_three_identity _ _ _ _ _ _ _ hr hJ

/-- No concentration denominator occurs in the extended vector field. -/
theorem normalizedField_contDiff (p : Rates) (ru rv rj : ℝ) :
    ContDiff ℝ 1 (normalizedField p ru rv rj) := by
  apply ContDiff.prodMk
  · exact (field_contDiff p).comp contDiff_fst
  · apply contDiff_pi.2
    intro i
    fin_cases i <;> simp [normalHU,normalHV,normalHJ,privateA,privateB,sharedC] <;>
      fun_prop

private theorem quotient_flux_derivative (a z : ℝ → ℝ) (t av zv n h : ℝ)
    (ha : HasDerivAt a av t) (hz : HasDerivAt z zv t) (hz0 : z t ≠ 0)
    (hn : n*z t = av) (hh : h*z t = zv) :
    HasDerivAt (fun τ => a τ/z τ) (n-(a t/z t)*h) t := by
  convert ha.div hz hz0 using 1
  rw [← hn,← hh]
  field_simp

/-- The eight-dimensional polynomial field is the actual derivative of the
normalized source trajectory wherever the three missing masses are nonzero. -/
theorem normalizedEmbedding_derivative (p : Rates) (ru rv rj : ℝ) (X : ℝ → State) (t : ℝ)
    (hru : ru ≠ 0) (hrv : rv ≠ 0) (hrj : rj ≠ 0)
    (hU : massU ru (X t) ≠ 0) (hV : massV rv (X t) ≠ 0) (hJ : massJ rj (X t) ≠ 0)
    (hd : HasDerivAt X (field p (X t)) t) :
    HasDerivAt (fun τ => normalizedEmbedding ru rv rj (X τ))
      (normalizedField p ru rv rj (normalizedEmbedding ru rv rj (X t))) t := by
  have hc := hasDerivAt_pi.1 hd
  have hUd := (hc 1).add ((hc 3).const_mul ru)
  have hVd := (hc 2).add ((hc 3).const_mul rv)
  have hJd := ((hc 1).add (hc 2)).add ((hc 3).const_mul rj)
  have hfa : privateA p (X t)*X t 1+(p.beta1*X t 0)*X t 3 = field p (X t) 1 := by
    simp [field,privateA]
    ring
  have hfb : privateB p (X t)*X t 2+(p.beta2*X t 0)*X t 3 = field p (X t) 2 := by
    simp [field,privateB]
    ring
  have hnU := weighted_two_identity (X t 1) (X t 3) ru
    (privateA p (X t)) (p.beta1*X t 0) hru hU
  rw [hfa] at hnU
  have hnV := weighted_two_identity (X t 2) (X t 3) rv
    (privateB p (X t)) (p.beta2*X t 0) hrv hV
  rw [hfb] at hnV
  have hnJa := weighted_three_identity (X t 1) (X t 2) (X t 3) rj
    (privateA p (X t)) 0 (p.beta1*X t 0) hrj hJ
  simp only [zero_mul,add_zero] at hnJa
  rw [hfa] at hnJa
  have hnJb := weighted_three_identity (X t 1) (X t 2) (X t 3) rj
    0 (privateB p (X t)) (p.beta2*X t 0) hrj hJ
  simp only [zero_mul,zero_add] at hnJb
  rw [hfb] at hnJb
  have hd0 := quotient_flux_derivative _ _ _ _ _ _ _ (hc 1) hUd hU hnU
    (normalHU_physical p ru (X t) hru hU)
  have hd1 := quotient_flux_derivative _ _ _ _ _ _ _ (hc 2) hVd hV hnV
    (normalHV_physical p rv (X t) hrv hV)
  have hd2 := quotient_flux_derivative _ _ _ _ _ _ _ (hc 1) hJd hJ hnJa
    (normalHJ_physical p rj (X t) hrj hJ)
  have hd3 := quotient_flux_derivative _ _ _ _ _ _ _ (hc 2) hJd hJ hnJb
    (normalHJ_physical p rj (X t) hrj hJ)
  apply HasDerivAt.prodMk hd
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · exact hd0
  · exact hd1
  · exact hd2
  · exact hd3

end OverlappingSiphonInvasion
