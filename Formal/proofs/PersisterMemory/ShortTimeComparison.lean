import proofs.PersisterMemory.ControlSource

namespace PersisterMemory
open Source
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

def linearPGF (e : ℚ) (f : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  molecular e f i - (death i+1/10)*f i

def pairBilinear (x y : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![x 0*y 0, (x 0*y 1+x 1*y 0)/2,
    (x 0*y 2+x 2*y 0+2*x 1*y 1)/4,
    (x 0*y 3+x 3*y 0)/2,
    (x 0*y 4+x 4*y 0+x 1*y 3+x 3*y 1)/4,
    (x 0*y 5+x 5*y 0+2*x 3*y 3)/4]

def coeffTwo (e : ℚ) (i : Fin 6) : ℚ := linearPGF e death i/2
def coeffThree (e : ℚ) (i : Fin 6) : ℚ :=
  (linearPGF e (coeffTwo e) i + daughterPair death i/10)/3
def coeffFour (e : ℚ) (i : Fin 6) : ℚ :=
  (linearPGF e (coeffThree e) i + pairBilinear death (coeffTwo e) i/5)/4

theorem rr_fourth_coefficient (e : ℚ) :
    coeffFour e 2 = -16087/8000000 - (29/480000)*e - (29/40000)*e^2 := by
  norm_num [coeffFour, coeffThree, coeffTwo, linearPGF, molecular,
    daughterPair, pairBilinear, death]
  ring

theorem rr_lower_coefficients_agree :
    coeffTwo (3/10) 2 = coeffTwo (1/100) 2 ∧
    coeffThree (3/10) 2 = coeffThree (1/100) 2 := by
  norm_num [coeffThree, coeffTwo, linearPGF, molecular, daughterPair, death]

theorem rr_negative_difference :
    coeffFour (3/10) 2 - coeffFour (1/100) 2 = -49619/600000000 := by
  rw [rr_fourth_coefficient, rr_fourth_coefficient]
  norm_num

end PersisterMemory
