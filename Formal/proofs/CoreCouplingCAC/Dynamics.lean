import proofs.CoreCouplingCAC.Source

namespace CoreCouplingCAC

noncomputable def transform (x : State) : Fin 4 → ℝ := ![x.A+x.B,-x.B,x.z,x.H]
noncomputable def untransform (t : Fin 4 → ℝ) : State := ⟨t 0+t 1,-t 1,t 2,t 3⟩

theorem untransform_transform (x : State) : untransform (transform x) = x := by
  cases x
  simp [untransform,transform]

noncomputable def dynamics (p : Rates) (t : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![p.a+p.b-t 0-p.e*(t 1+(t 0+t 1)^2),
    -p.b-t 0-(2+t 2+p.e)*t 1-p.e*(t 0+t 1)^2,
    t 0+(1+t 2)*t 1-p.u*t 2-2*p.v*(t 2)^2+3*t 3,
    p.u*t 2+p.v*(t 2)^2-(2+p.d)*t 3]

noncomputable def jacobian (p : Rates) (t : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![-1-2*p.e*(t 0+t 1),-p.e*(1+2*(t 0+t 1)),0,0],
    ![-1-2*p.e*(t 0+t 1),-2-t 2-p.e-2*p.e*(t 0+t 1),-t 1,0],
    ![1,1+t 2,t 1-p.u-4*p.v*t 2,3],
    ![0,0,p.u+2*p.v*t 2,-2-p.d]]

theorem dynamics_source (p : Rates) (x : State) :
    dynamics p (transform x) =
      ![fA p x.A x.B x.z+fB p x.A x.B x.z,-fB p x.A x.B x.z,
        fZ p x.A x.B x.z x.H,fH p x.z x.H] := by
  funext i
  fin_cases i <;> simp [dynamics,transform,fA,fB,fZ,fH] <;> ring

/-- The full nonlinear difference is exactly the midpoint Jacobian times the
state difference, since the source vector field is quadratic. -/
theorem midpoint_secant (p : Rates) (x y : Fin 4 → ℝ) (i : Fin 4) :
    dynamics p x i-dynamics p y i =
      ∑ j : Fin 4, jacobian p (fun k => (x k+y k)/2) i j*(x j-y j) := by
  fin_cases i <;> simp [dynamics,jacobian,Fin.sum_univ_succ] <;> ring

theorem stationary_transformed (p : Rates) (x : State) (h : Stationary p x) :
    dynamics p (transform x) = 0 := by
  rw [dynamics_source]
  rcases h with ⟨hA,hB,hz,hH⟩
  simp [hA,hB,hz,hH]

end CoreCouplingCAC
