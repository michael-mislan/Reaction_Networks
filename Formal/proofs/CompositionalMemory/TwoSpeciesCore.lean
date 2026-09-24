import Mathlib

namespace CompositionalMemory

abbrev TwoPoint := Fin 2 → ℝ

def twoCenter (b : Bool) : TwoPoint := if b then ![3,54] else ![1,6]

noncomputable def twoField (u : TwoPoint) : TwoPoint :=
  ![6+2*u 1-6*(u 0)^2-u 0*u 1/6-11*u 0,6*(u 0)^2-u 1]

noncomputable def twoJacobian (b : Bool) (y : TwoPoint) : TwoPoint :=
  if b then ![-56*y 0+(3/2)*y 1,36*y 0-y 1]
  else ![-24*y 0+(11/6)*y 1,12*y 0-y 1]

noncomputable def twoRemainder (y : TwoPoint) : TwoPoint :=
  ![-6*(y 0)^2-y 0*y 1/6,6*(y 0)^2]

def twoBilinear (b : Bool) (y z : TwoPoint) : ℝ :=
  if b then 1732*y 0*z 0+2690*(y 0*z 1+y 1*z 0)+4187*y 1*z 1
  else 5292*y 0*z 0+10434*(y 0*z 1+y 1*z 0)+20929*y 1*z 1

def twoQ (b : Bool) : TwoPoint →ₗ[ℝ] TwoPoint →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (twoBilinear b)
    (by intro x y z; cases b <;> simp [twoBilinear] <;> ring)
    (by intro c y z; cases b <;> simp [twoBilinear] <;> ring)
    (by intro x y z; cases b <;> simp [twoBilinear] <;> ring)
    (by intro c y z; cases b <;> simp [twoBilinear] <;> ring)

theorem twoQ_apply (b : Bool) (y z : TwoPoint) : twoQ b y z=twoBilinear b y z := rfl

theorem twoQ_symm (b : Bool) (y z : TwoPoint) : twoQ b y z=twoQ b z y := by
  cases b <;> simp only [twoQ_apply,twoBilinear,Bool.false_eq_true,if_false,if_true] <;> ring

theorem two_center_stationary (b : Bool) : twoField (twoCenter b)=0 := by
  funext i
  fin_cases i <;> cases b <;> norm_num [twoField,twoCenter]

theorem two_field_expansion (b : Bool) (y : TwoPoint) :
    twoField (twoCenter b+y)=twoJacobian b y+twoRemainder y := by
  funext i
  fin_cases i <;> cases b <;> simp [twoField,twoCenter,twoJacobian,twoRemainder] <;> ring

theorem two_linear_lyapunov (b : Bool) (y : TwoPoint) :
    2*twoQ b y (twoJacobian b y)=-(if b then 304 else 3600)*((y 0)^2+(y 1)^2) := by
  cases b <;> simp [twoQ_apply,twoBilinear,twoJacobian] <;> ring

theorem two_quadratic_coercivity (b : Bool) (y : TwoPoint) :
    (y 0)^2+(y 1)^2 ≤ twoQ b y y := by
  cases b
  · simp only [twoQ_apply,twoBilinear,Bool.false_eq_true,if_false]
    nlinarith only [sq_nonneg (5291*y 0+10434*y 1),sq_nonneg (y 1)]
  · simp only [twoQ_apply,twoBilinear,if_true]
    nlinarith only [sq_nonneg (1731*y 0+2690*y 1),sq_nonneg (y 1)]

end CompositionalMemory
