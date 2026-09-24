import proofs.CoreCouplingCAC.Source

namespace DisguisedToricAssemblies
open CoreCouplingCAC

noncomputable def massBound (p : Rates) (x : State) : ℝ :=
  (p.e+3/2)*x.A+(2*p.e+1)*x.B+x.z+3/2*x.H
noncomputable def massDrift (p : Rates) (x : State) : ℝ :=
  (p.e+3/2)*fA p x.A x.B x.z+(2*p.e+1)*fB p x.A x.B x.z+
    fZ p x.A x.B x.z x.H+3/2*fH p x.z x.H
noncomputable def absorbingConstant (p : Rates) : ℝ :=
  (p.e+3/2)*p.a+(2*p.e+1)*p.b+(p.u+2)^2/(8*p.v)

theorem massDrift_identity (p : Rates) (x : State) :
    massDrift p x = (p.e+3/2)*p.a+(2*p.e+1)*p.b-x.A-x.B-
      (p.e+1/2)*x.B*x.z-2*p.e*x.A^2+p.u/2*x.z-p.v/2*x.z^2-3*p.d/2*x.H := by
  unfold massDrift fA fB fZ fH
  ring

theorem square_dissipation (u v z : ℝ) (hv : 0 < v) :
    u/2*z-v/2*z^2 ≤ (u+2)^2/(8*v)-z := by
  have hi : (u+2)^2/(8*v)-z-(u/2*z-v/2*z^2) = (2*v*z-u-2)^2/(8*v) := by
    field_simp
    ring
  have hn : 0 ≤ (2*v*z-u-2)^2/(8*v) := by positivity
  linarith

/-- Algebraic comparison bound; rho can be the minimum of the four positive bounds. -/
theorem massDrift_coercive (p : Rates) (x : State) (hp : p.Positive)
    (hA : 0 ≤ x.A) (hB : 0 ≤ x.B) (hz : 0 ≤ x.z) (hH : 0 ≤ x.H)
    (rho : ℝ) (hrA : rho*(p.e+3/2) ≤ 1) (hrB : rho*(2*p.e+1) ≤ 1)
    (hrz : rho ≤ 1) (hrH : rho ≤ p.d) :
    massDrift p x ≤ absorbingConstant p-rho*massBound p x := by
  have he := hp.2.2.2.2.1
  have hs := square_dissipation p.u p.v x.z hp.2.2.2.1
  have hn1 : 0 ≤ (p.e+1/2)*x.B*x.z := by positivity
  have hn2 : 0 ≤ 2*p.e*x.A^2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hrA hA
  have h2 := mul_le_mul_of_nonneg_right hrB hB
  have h3 := mul_le_mul_of_nonneg_right hrz hz
  have h4 := mul_le_mul_of_nonneg_right hrH hH
  rw [massDrift_identity]
  unfold absorbingConstant massBound
  nlinarith only [hs,hn1,hn2,h1,h2,h3,h4]

theorem scalar_lower_bounds (p : Rates) (x : State) (hp : p.Positive)
    (M : ℝ) (hA : 0 ≤ x.A) (hB : 0 ≤ x.B) (hz : 0 ≤ x.z) (hH : 0 ≤ x.H)
    (hAM : x.A ≤ M) (hBM : x.B ≤ M) (hzM : x.z ≤ M) :
    p.a-(2+2*p.e*M)*x.A ≤ fA p x.A x.B x.z ∧
    p.b-(1+p.e+M)*x.B ≤ fB p x.A x.B x.z ∧
    x.A-(M+p.u+2*p.v*M)*x.z ≤ fZ p x.A x.B x.z x.H ∧
    p.u*x.z-(2+p.d)*x.H ≤ fH p x.z x.H := by
  have he := hp.2.2.2.2.1.le
  have hv := hp.2.2.2.1.le
  have hAA : 0 ≤ p.e*x.A*(M-x.A) := by positivity
  have hBZ : 0 ≤ x.B*x.z := by positivity
  have heB : 0 ≤ p.e*x.B := by positivity
  have heAA : 0 ≤ p.e*x.A^2 := by positivity
  have hMB : 0 ≤ (M-x.z)*x.B := by positivity
  have hZB : 0 ≤ (M-x.B)*x.z := by positivity
  have hZZ : 0 ≤ p.v*x.z*(M-x.z) := by positivity
  have hvZZ : 0 ≤ p.v*x.z^2 := by positivity
  unfold fA fB fZ fH
  constructor
  · nlinarith only [hAA,hBZ,heB]
  constructor
  · nlinarith only [hA,heAA,hMB]
  constructor
  · nlinarith only [hZB,hZZ,hH]
  · nlinarith only [hvZZ]

end DisguisedToricAssemblies
