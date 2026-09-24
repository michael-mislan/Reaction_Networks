import Mathlib

namespace TinyProgrammableChemicalFactory

theorem correction_total (r j g h : ℝ) :
    g*h*(r-j)*(r-j-1)*j+g*h*j*(j-1)*(r-j)=g*h*j*(r-j)*(r-2) := by ring

theorem embedded_down_probability (r j g h : ℝ)
    (hg : g≠0) (hh : h≠0) (hj : j≠0) (hrj : r-j≠0) (hr : r-2≠0) :
    (g*h*(r-j)*(r-j-1)*j)/(g*h*j*(r-j)*(r-2))=(r-j-1)/(r-2) := by
  field_simp

def fuelValue (r : ℕ) : ℕ → ℕ → ℚ
  | 0,j => if j=0 then 1 else 0
  | L+1,j => if j=0 then 1 else if r≤j then 0 else
      ((r-j-1 : ℕ) : ℚ)/(r-2 : ℕ)*fuelValue r L (j-1)+
      ((j-1 : ℕ) : ℚ)/(r-2 : ℕ)*fuelValue r L (j+1)

theorem two_fuel_eight_two : fuelValue 10 2 2=7/8 := by
  norm_num [fuelValue]

theorem finite_fuel_boundary (r L : ℕ) : fuelValue r L 0=1 := by
  cases L <;> simp [fuelValue]

end TinyProgrammableChemicalFactory
