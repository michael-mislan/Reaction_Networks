import proofs.RAF1519.Reservoir.Scalar

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

def features (x c : Fin 6 → ℝ) (k : Fin 9) : ℝ :=
  match k.val with
  | 0 => (x 0+c 0)/2
  | 1 => c 1
  | 2 => x 2
  | 3 => (x 2+c 2)/2
  | 4 => (x 5+c 5)/2
  | 5 => c 4*x 5
  | 6 => c 4*c 2
  | 7 => x 2*x 5
  | _ => 1

def secant (m : Fin 9 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => match i.val,j.val with
  | 0,0 => -2-(4/100000)*m 0
  | 0,1 => m 2+2/100000
  | 0,2 => m 1
  | 1,0 => 1+(2/100000)*m 0
  | 1,1 => -m 2-1-1/100000
  | 1,2 => -m 1
  | 2,0 => 1
  | 2,1 => -m 2
  | 2,2 => -m 1-16-8*m 3-m 5
  | 2,3 => 3
  | 2,4 => -m 7
  | 2,5 => -m 6
  | 3,2 => 16+4*m 3
  | 3,3 => -20001/10000
  | 4,2 => -m 5
  | 4,4 => -1/20-m 7
  | 4,5 => -m 6
  | 5,2 => m 5
  | 5,4 => m 7
  | 5,5 => m 6-1/2-2*m 4
  | _,_ => 0

private theorem sum_six (v : Fin 6 → ℝ) : (∑ j, v j) = v 0+v 1+v 2+v 3+v 4+v 5 := by
  simp [Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 10000 in
private theorem field_secant_0 (x c : Fin 6 → ℝ) :
    field x 0-field c 0 = ∑ j, secant (features x c) 0 j*(x j-c j) := by
  rw [sum_six]
  change (6-2*x 0+x 1*x 2+2*(1/100000)*(x 1-(x 0)^2))-
    (6-2*c 0+c 1*c 2+2*(1/100000)*(c 1-(c 0)^2)) =
    (-2-(4/100000)*((x 0+c 0)/2))*(x 0-c 0)+
    (x 2+2/100000)*(x 1-c 1)+c 1*(x 2-c 2)+0*(x 3-c 3)+0*(x 4-c 4)+0*(x 5-c 5)
  ring

set_option maxHeartbeats 10000 in
private theorem field_secant_1 (x c : Fin 6 → ℝ) :
    field x 1-field c 1 = ∑ j, secant (features x c) 1 j*(x j-c j) := by
  rw [sum_six]
  change (27+x 0-(x 2+1)*x 1-(1/100000)*(x 1-(x 0)^2))-
    (27+c 0-(c 2+1)*c 1-(1/100000)*(c 1-(c 0)^2)) =
    (1+(2/100000)*((x 0+c 0)/2))*(x 0-c 0)+
    (-x 2-1-1/100000)*(x 1-c 1)+(-c 1)*(x 2-c 2)+0*(x 3-c 3)+0*(x 4-c 4)+0*(x 5-c 5)
  ring

set_option maxHeartbeats 10000 in
private theorem field_secant_2 (x c : Fin 6 → ℝ) :
    field x 2-field c 2 = ∑ j, secant (features x c) 2 j*(x j-c j) := by
  rw [sum_six]
  change (x 0-x 1*x 2-16*x 2+3*x 3-4*(x 2)^2-x 4*x 2*x 5)-
    (c 0-c 1*c 2-16*c 2+3*c 3-4*(c 2)^2-c 4*c 2*c 5) =
    1*(x 0-c 0)+(-x 2)*(x 1-c 1)+
    (-c 1-16-8*((x 2+c 2)/2)-c 4*x 5)*(x 2-c 2)+3*(x 3-c 3)+
    (-(x 2*x 5))*(x 4-c 4)+(-(c 4*c 2))*(x 5-c 5)
  ring

set_option maxHeartbeats 10000 in
private theorem field_secant_3 (x c : Fin 6 → ℝ) :
    field x 3-field c 3 = ∑ j, secant (features x c) 3 j*(x j-c j) := by
  rw [sum_six]
  change (16*x 2+2*(x 2)^2-(20001/10000)*x 3)-
    (16*c 2+2*(c 2)^2-(20001/10000)*c 3) =
    0*(x 0-c 0)+0*(x 1-c 1)+(16+4*((x 2+c 2)/2))*(x 2-c 2)+
    (-20001/10000)*(x 3-c 3)+0*(x 4-c 4)+0*(x 5-c 5)
  ring

set_option maxHeartbeats 10000 in
private theorem field_secant_4 (x c : Fin 6 → ℝ) :
    field x 4-field c 4 = ∑ j, secant (features x c) 4 j*(x j-c j) := by
  rw [sum_six]
  change ((1/20)*(1-x 4)-x 4*x 2*x 5)-((1/20)*(1-c 4)-c 4*c 2*c 5) =
    0*(x 0-c 0)+0*(x 1-c 1)+(-(c 4*x 5))*(x 2-c 2)+0*(x 3-c 3)+
    (-1/20-x 2*x 5)*(x 4-c 4)+(-(c 4*c 2))*(x 5-c 5)
  ring

set_option maxHeartbeats 10000 in
private theorem field_secant_5 (x c : Fin 6 → ℝ) :
    field x 5-field c 5 = ∑ j, secant (features x c) 5 j*(x j-c j) := by
  rw [sum_six]
  change (x 5*(x 4*x 2-1/2-x 5))-(c 5*(c 4*c 2-1/2-c 5)) =
    0*(x 0-c 0)+0*(x 1-c 1)+(c 4*x 5)*(x 2-c 2)+0*(x 3-c 3)+
    (x 2*x 5)*(x 4-c 4)+(c 4*c 2-1/2-2*((x 5+c 5)/2))*(x 5-c 5)
  ring

theorem field_secant (x c : Fin 6 → ℝ) (i : Fin 6) :
    field x i-field c i = ∑ j, secant (features x c) i j*(x j-c j) := by
  fin_cases i
  · exact field_secant_0 x c
  · exact field_secant_1 x c
  · exact field_secant_2 x c
  · exact field_secant_3 x c
  · exact field_secant_4 x c
  · exact field_secant_5 x c

theorem field_contDiff : ContDiff ℝ 1 field := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [field] <;> fun_prop

def featureLower (l : Fin 6 → ℝ) : Fin 9 → ℝ :=
  ![l 0,l 1,l 2,l 2,l 5,l 4*l 5,l 4*l 2,l 2*l 5,1]
def featureUpper (u : Fin 6 → ℝ) : Fin 9 → ℝ :=
  ![u 0,u 1,u 2,u 2,u 5,u 4*u 5,u 4*u 2,u 2*u 5,1]

theorem nonnegative_product_bounds (l₁ u₁ l₂ u₂ a b : ℝ)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (ha : l₁ ≤ a ∧ a ≤ u₁) (hb : l₂ ≤ b ∧ b ≤ u₂) :
    l₁*l₂ ≤ a*b ∧ a*b ≤ u₁*u₂ := by
  exact ⟨mul_le_mul ha.1 hb.1 hl₂ (hl₁.trans ha.1),
    mul_le_mul ha.2 hb.2 (hl₂.trans hb.1) ((hl₁.trans ha.1).trans ha.2)⟩

theorem features_bounds (l u x c : Fin 6 → ℝ) (hl : ∀ i, 0 ≤ l i)
    (hx : ∀ i, l i ≤ x i ∧ x i ≤ u i) (hc : ∀ i, l i ≤ c i ∧ c i ≤ u i) :
    ∀ k, featureLower l k ≤ features x c k ∧ features x c k ≤ featureUpper u k := by
  intro k
  fin_cases k
  · change l 0 ≤ (x 0+c 0)/2 ∧ (x 0+c 0)/2 ≤ u 0
    constructor <;> linarith [(hx 0).1,(hx 0).2,(hc 0).1,(hc 0).2]
  · exact hc 1
  · exact hx 2
  · change l 2 ≤ (x 2+c 2)/2 ∧ (x 2+c 2)/2 ≤ u 2
    constructor <;> linarith [(hx 2).1,(hx 2).2,(hc 2).1,(hc 2).2]
  · change l 5 ≤ (x 5+c 5)/2 ∧ (x 5+c 5)/2 ≤ u 5
    constructor <;> linarith [(hx 5).1,(hx 5).2,(hc 5).1,(hc 5).2]
  · exact nonnegative_product_bounds _ _ _ _ _ _ (hl 4) (hl 5) (hc 4) (hx 5)
  · exact nonnegative_product_bounds _ _ _ _ _ _ (hl 4) (hl 2) (hc 4) (hc 2)
  · exact nonnegative_product_bounds _ _ _ _ _ _ (hl 2) (hl 5) (hx 2) (hx 5)
  · exact ⟨le_rfl,le_rfl⟩

end
end RAF1519.Reservoir
