import proofs.TinyProgrammableChemicalFactory.Source

namespace TinyProgrammableChemicalFactory

theorem reaction_conserves (z : Counts) (r : Channel) (h : enabled z r) :
    coreMass (update z r)=coreMass z ∧ fuelMass (update z r)=fuelMass z := by
  have h0:=h 0; have h1:=h 1; have h2:=h 2; have h3:=h 3
  have h4:=h 4; have h5:=h 5; have h6:=h 6
  fin_cases r <;>
    simp [reactants, products, update, coreMass, fuelMass, Matrix.cons_val] at * <;> omega

theorem repair_result (z : Counts) (hx : 2≤z 0) (hy : z 1=1) (hh : z 5=1) :
    update z 10 = ![z 0+1,0,z 2,z 3,z 4,0,z 6+1] := by
  funext i
  fin_cases i <;> simp [update,reactants,products,hy,hh]
  omega

theorem repair_enabled (z : Counts) (hx : 2≤z 0) (hy : z 1=1) (hh : z 5=1) :
    enabled z 10 := by
  intro i
  fin_cases i <;> simp [reactants,hy,hh,hx]

theorem refill_food_bill (n f p a b : ℕ) (hm : n+f+p=80)
    (hab : a+b=n+f) : (80-a)+(80-b)=80+p := by omega

end TinyProgrammableChemicalFactory
