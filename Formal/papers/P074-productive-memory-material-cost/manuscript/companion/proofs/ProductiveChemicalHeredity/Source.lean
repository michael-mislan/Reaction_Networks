import Mathlib

namespace ProductiveChemicalHeredity

abbrev Counts := Fin 7 → ℕ
abbrev Channel := Fin 4

def reactants (r : Channel) : Counts :=
  ![![65,8,155,1,0,0,0], ![186,38,0,0,1,4,0],
    ![8,65,155,1,0,0,0], ![38,186,0,0,1,0,4]] r

def products (r : Channel) : Counts :=
  ![![186,38,0,0,1,4,0], ![65,8,155,1,0,0,0],
    ![38,186,0,0,1,0,4], ![8,65,155,1,0,0,0]] r

def enabled (z : Counts) (r : Channel) : Prop := ∀ i, reactants r i ≤ z i
def update (z : Counts) (r : Channel) : Counts := fun i => z i-reactants r i+products r i
def coreMass (z : Counts) := z 0+z 1+z 2+z 5+z 6
def fuelMass (z : Counts) := z 3+z 4
def newborn (x y : ℕ) : Counts := ![x,y,414-x-y,1,0,0,0]
def grown (x y : ℕ) : Counts := ![x+121,y+30,414-x-y-155,0,1,4,0]
def corridor (x y : ℕ) : Prop := 65≤x ∧ x≤195 ∧ 8≤y ∧ y≤64

theorem reaction_conserves (z : Counts) (r : Channel) (h : enabled z r) :
    coreMass (update z r)=coreMass z ∧ fuelMass (update z r)=fuelMass z := by
  have h0:=h 0; have h1:=h 1; have h2:=h 2; have h3:=h 3
  have h4:=h 4; have h5:=h 5; have h6:=h 6
  fin_cases r <;>
    simp [reactants, products, update, coreMass, fuelMass, Matrix.cons_val] at * <;> omega

theorem newborn_only_forward (x y : ℕ) (h : corridor x y) (r : Channel) :
    enabled (newborn x y) r ↔ r=0 := by
  rcases h with ⟨hx,hX,hy,hY⟩
  constructor
  · intro he
    fin_cases r
    · rfl
    all_goals
      exfalso
      have h1:=he 1; have h5:=he 5; have h6:=he 6
      simp [reactants,newborn,Matrix.cons_val] at * <;> omega
  · intro hr
    subst r
    intro i
    fin_cases i <;> simp [reactants,newborn,Matrix.cons_val] <;> omega

theorem grown_only_reverse (x y : ℕ) (h : corridor x y) (r : Channel) :
    enabled (grown x y) r ↔ r=1 := by
  rcases h with ⟨hx,hX,hy,hY⟩
  constructor
  · intro he
    fin_cases r
    · have hh:=he 3
      simp [reactants,grown,Matrix.cons_val] at hh
    · rfl
    · have hh:=he 3
      simp [reactants,grown,Matrix.cons_val] at hh
    · have hh:=he 6
      simp [reactants,grown,Matrix.cons_val] at hh
  · intro hr
    subst r
    intro i
    fin_cases i <;> simp [reactants,grown,Matrix.cons_val] <;> omega

theorem forward_result (x y : ℕ) (h : corridor x y) :
    update (newborn x y) 0=grown x y := by
  rcases h with ⟨hx,hX,hy,hY⟩
  funext i
  fin_cases i <;> simp [update,reactants,products,newborn,grown] <;> omega

theorem reverse_result (x y : ℕ) (h : corridor x y) :
    update (grown x y) 1=newborn x y := by
  rcases h with ⟨hx,hX,hy,hY⟩
  funext i
  fin_cases i <;> simp [update,reactants,products,newborn,grown] <;> omega

theorem exact_closed_pair (x y : ℕ) (h : corridor x y) (z : Counts)
    (hz : z=newborn x y ∨ z=grown x y) (r : Channel) (he : enabled z r) :
    update z r=newborn x y ∨ update z r=grown x y := by
  rcases hz with hz | hz
  · subst z
    have hr := (newborn_only_forward x y h r).mp he
    subst r
    exact Or.inr (forward_result x y h)
  · subst z
    have hr := (grown_only_reverse x y h r).mp he
    subst r
    exact Or.inl (reverse_result x y h)

theorem persistent_ratio (x y : ℕ) (h : corridor x y) :
    0<y ∧ y<x ∧ 65*(x+y)≤129*x := by
  rcases h with ⟨hx,hX,hy,hY⟩
  omega

theorem canonical_preparation : corridor 121 30 ∧
    coreMass (newborn 121 30)=414 ∧ fuelMass (newborn 121 30)=1 := by
  unfold corridor
  decide

theorem refill_identity (a b : ℕ) (hab : a+b=410) :
    (414-a)+(414-b)=418 := by omega

theorem finite_supply_ledger :
    (415+420*10 : ℕ)=4615 ∧ (40+10+10*415+415 : ℕ)=4615 := by norm_num

end ProductiveChemicalHeredity
