import Mathlib

namespace CommonPhysicalRealization
noncomputable section

def productiveDrift (r d : ℝ) : Fin 4 → ℝ :=
  let x : ℝ := 1/10000
  let c1 := (3/5)*x
  let c2 := (3/10)*x
  let z := (6/25)*x
  let j1 := 20*(x-c1)
  let j2 := 20*(c1-c2)
  let j3 := 20*(c2-z/10)
  let j4 := r*(z-x*x)
  ![(1/500000000)*(1-x/10)-j1+2*j4-d*(x-1/8000000000)-x,
    j1-j2-c1,j2-j3-c2,j3-j4-z]

theorem productive_margin (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : d ≤ 1/25) (i : Fin 4) :
    (![381100249/50000000000000,7/50000,9/500000,2421/100000000] : Fin 4 → ℝ) i ≤
      productiveDrift r d i := by
  fin_cases i <;> norm_num [productiveDrift] <;> linarith

theorem productive_positive (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : d ≤ 1/25) (i : Fin 4) : 0 < productiveDrift r d i := by
  have h := productive_margin r d hr hr' hd i
  fin_cases i <;> norm_num at h ⊢ <;> linarith

/-- A genuine failure of this fixed-state certificate, outside the admitted box. -/
theorem productive_boundary_failure : productiveDrift 19 (1/5) 0 < 0 := by
  norm_num [productiveDrift]

end
end CommonPhysicalRealization
