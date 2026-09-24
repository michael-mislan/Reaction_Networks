import proofs.CoreCouplingCAC.Source

namespace CoreCouplingCAC

noncomputable def reducedB (p : Rates) (z : ℝ) : ℝ := (p.a+2*p.b)/(z+2)
noncomputable def reducedK (p : Rates) (z : ℝ) : ℝ :=
  (p.v*(1+2*p.d)*z^2-p.u*(1-p.d)*z)/(2+p.d)
noncomputable def reducedA (p : Rates) (z : ℝ) : ℝ := z*reducedB p z+reducedK p z
noncomputable def reducedH (p : Rates) (z : ℝ) : ℝ := (p.u*z+p.v*z^2)/(2+p.d)
noncomputable def lift (p : Rates) (z : ℝ) : State :=
  ⟨reducedA p z, reducedB p z, z, reducedH p z⟩
noncomputable def residual (p : Rates) (z : ℝ) : ℝ :=
  p.b-(1+p.e)*reducedB p z+reducedK p z+p.e*(reducedA p z)^2

theorem lift_residual (p : Rates) (z : ℝ) (hz : z+2 ≠ 0) (hd : 2+p.d ≠ 0) :
    fA p (lift p z).A (lift p z).B z = -2*residual p z ∧
    fB p (lift p z).A (lift p z).B z = residual p z ∧
    fZ p (lift p z).A (lift p z).B z (lift p z).H = 0 ∧
    fH p z (lift p z).H = 0 := by
  dsimp [fA,fB,fZ,fH,lift,residual,reducedA,reducedB,reducedK,reducedH]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  · field_simp
    ring

theorem lift_stationary (p : Rates) (z : ℝ) (hz : z+2 ≠ 0) (hd : 2+p.d ≠ 0)
    (h : residual p z = 0) : Stationary p (lift p z) := by
  have he := lift_residual p z hz hd
  simpa [Stationary, lift, h] using he

theorem stationary_reconstruction (p : Rates) (x : State)
    (hz : x.z+2 ≠ 0) (hd : 2+p.d ≠ 0) (h : Stationary p x) :
    x = lift p x.z := by
  rcases h with ⟨ha,hb,hz',hh⟩
  dsimp [fA] at ha
  dsimp [fB] at hb
  dsimp [fZ] at hz'
  dsimp [fH] at hh
  have hH : x.H = reducedH p x.z := by
    apply (eq_div_iff hd).2
    dsimp [reducedH]
    linarith
  have hK : x.A-x.B*x.z = reducedK p x.z := by
    dsimp [reducedK]
    apply (eq_div_iff hd).2
    linear_combination (2+p.d)*hz'+3*hh
  have hB : x.B = reducedB p x.z := by
    dsimp [reducedB]
    apply (eq_div_iff hz).2
    linarith
  have hA : x.A = reducedA p x.z := by
    dsimp [reducedA]
    rw [← hB, ← hK]
    ring
  cases x
  simp_all [lift]

end CoreCouplingCAC
