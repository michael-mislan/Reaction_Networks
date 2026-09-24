import proofs.CoreCouplingGlobal.ResponseEnergy

namespace CoreCouplingGlobal

/-- Linear residuals in displacement coordinates (b,zeta,eta,r). -/
def linearFork (B z b ζ : ℝ) : ℝ := -(2+z)*b-B*ζ
def linearZ (B z c b ζ η : ℝ) : ℝ := (c-1-z)*b-(B+16+8*z)*ζ+3*η
noncomputable def linearH (z ζ η : ℝ) : ℝ := (16+4*z)*ζ-(20001/10000)*η

/-- Candidate quadratic potential in the response displacement coordinates. -/
noncomputable def responseQuadratic (B z m w n b ζ η r : ℝ) : ℝ :=
  m*(2+z)*b^2/2+m*B*b*ζ+(B+16+8*z)*ζ^2/(2*w)-3*ζ*η/w+
    n*(20001/10000)*η^2/2+r^2/2

theorem responseQuadratic_hasDerivAt (B z m w n : ℝ) (hw : w ≠ 0)
    (b ζ η r : ℝ → ℝ) (t db dz dH dr : ℝ)
    (hb : HasDerivAt b db t) (hz : HasDerivAt ζ dz t)
    (hH : HasDerivAt η dH t) (hr : HasDerivAt r dr t) :
    HasDerivAt (fun s => responseQuadratic B z m w n (b s) (ζ s) (η s) (r s))
      ((m*(2+z)*b t+m*B*ζ t)*db+
        (m*B*b t+(B+16+8*z)*ζ t/w-3*η t/w)*dz+
        (-3*ζ t/w+n*(20001/10000)*η t)*dH+r t*dr) t := by
  have hv := ((((((hb.pow 2).const_mul (m*(2+z))).div_const 2).add
    ((hb.const_mul (m*B)).mul hz)).add
    (((hz.pow 2).const_mul (B+16+8*z)).div_const (2*w))).sub
    (((hz.mul hH).const_mul 3).div_const w)).add
    (((hH.pow 2).const_mul (n*(20001/10000))).div_const 2)
  have hv' := hv.add ((hr.pow 2).div_const 2)
  convert hv' using 1
  · funext s
    dsimp [responseQuadratic]
    ring
  · norm_num
    field_simp
    ring

/-- The directional derivative of the quadratic candidate along the linear
response field has exactly the previously certified dissipation expression. -/
theorem responseQuadratic_directional_identity (B z a c m w n b ζ η r : ℝ)
    (hw : w ≠ 0) (hcross : m*B*w = 1+z-c) (hH : n*(16+4*z)*w = 3) :
    let F := linearFork B z b ζ
    let Z := linearZ B z c b ζ η
    let K := linearH z ζ η
    (m*(2+z)*b+m*B*ζ)*(F+a*r)+
      (m*B*b+(B+16+8*z)*ζ/w-3*η/w)*(Z+r)+
      (-3*ζ/w+n*(20001/10000)*η)*K+r*(-a*(1+c)*r-c*F) =
      -m*F^2-Z^2/w-n*K^2-a*(1+c)*r^2-(a*m+c)*r*F-r*Z/w := by
  dsimp only
  have h₁ : m*(2+z)*b+m*B*ζ = -m*linearFork B z b ζ := by unfold linearFork; ring
  have h₂ : m*B*b+(B+16+8*z)*ζ/w-3*η/w = -linearZ B z c b ζ η/w := by
    unfold linearZ
    field_simp
    linear_combination b*hcross
  have h₃ : -3*ζ/w+n*(20001/10000)*η = -n*linearH z ζ η := by
    unfold linearH
    field_simp
    linear_combination 10000*ζ*hH
  rw [h₁,h₂,h₃]
  ring

theorem responseQuadratic_directional_bound (B z a c m w n b ζ η r : ℝ)
    (ha : 99/100 ≤ a) (ha' : a ≤ 101/100)
    (hc : -(1/500) ≤ c) (hc' : c ≤ 1/500)
    (hm : 1/500 ≤ m) (hm' : m ≤ 13/50)
    (hw : 2 ≤ w) (hw' : w ≤ 182) (hn : 1/4000 ≤ n)
    (hcross : m*B*w = 1+z-c) (hH : n*(16+4*z)*w = 3) :
    let F := linearFork B z b ζ
    let Z := linearZ B z c b ζ η
    let K := linearH z ζ η
    (m*(2+z)*b+m*B*ζ)*(F+a*r)+
      (m*B*b+(B+16+8*z)*ζ/w-3*η/w)*(Z+r)+
      (-3*ζ/w+n*(20001/10000)*η)*K+r*(-a*(1+c)*r-c*F) ≤
      -r^2/4-F^2/1000-Z^2/364-K^2/4000 := by
  dsimp only
  rw [responseQuadratic_directional_identity B z a c m w n b ζ η r (by linarith) hcross hH]
  exact response_energy_dissipation a c m w r (linearFork B z b ζ)
    (linearZ B z c b ζ η) (linearH z ζ η) n ha ha' hc hc' hm hm' hw hw' hn

end CoreCouplingGlobal
