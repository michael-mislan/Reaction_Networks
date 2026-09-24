import proofs.CommonPhysicalRealization.ExporterThermochemistry

namespace ProductiveRecovery
noncomputable section
open scoped BigOperators

abbrev State := Fin 6 → ℝ
def Nonneg (c : State) : Prop := ∀ i, 0 ≤ c i
def A (c : State) : ℝ := c 0 + c 2 + 2*c 3 + 2*c 4 + 2*c 5
def B (c : State) : ℝ := c 1 + c 2 + c 3 + 2*c 4 + 2*c 5
def Y (c : State) : ℝ := c 2 + (9/8)*c 3 + (7/5)*c 4 + (9/5)*c 5
def inventory (c : State) : ℝ := c 2 + c 3 + c 4 + 2*c 5
def flux (r d : ℝ) (c : State) : Fin 6 → ℝ :=
  ![(1/500000000)*c 0*c 1-(1/5000000000)*c 2,
    20*c 2*c 0-20*c 3, 20*c 3*c 1-20*c 4,
    20*c 4-2*c 5, r*(c 5-c 2^2),
    d*c 2-d*(1/8000000000)*c 0*c 1]
def field (r d : ℝ) (c : State) : State :=
  let j := flux r d c
  ![1-c 0-j 0-j 1+j 5, 1-c 1-j 0-j 2+j 5,
    -c 2+j 0-j 1+2*j 4-j 5, -c 3+j 1-j 2,
    -c 4+j 2-j 3, -c 5+j 3-j 4]

/-- Concentration monomials at unit F/P activities. -/
def leftMonomial (c : State) : Fin 6 → ℝ :=
  ![c 0*c 1, c 2*c 0, c 3*c 1, c 4, c 5, c 2]
def rightMonomial (c : State) : Fin 6 → ℝ :=
  ![c 2, c 3, c 4, c 5, c 2^2, c 0*c 1]

theorem flux_coefficients (r d : ℝ) (c : State) (j : Fin 6) :
    flux r d c j =
      CommonPhysicalRealization.forwardCoefficient r d j * leftMonomial c j -
      CommonPhysicalRealization.reverseCoefficient r d j * rightMonomial c j := by
  fin_cases j <;>
    norm_num [flux, leftMonomial, rightMonomial,
      CommonPhysicalRealization.forwardCoefficient,
      CommonPhysicalRealization.reverseCoefficient] <;> ring

theorem material_A (r d : ℝ) (c : State) : A (field r d c) = 1-A c := by
  simp [A, field]; ring
theorem material_B (r d : ℝ) (c : State) : B (field r d c) = 1-B c := by
  simp [B, field]; ring
theorem inventory_drift (r d : ℝ) (c : State) :
    inventory (field r d c) = flux r d c 0 + flux r d c 3 -
      flux r d c 5 - inventory c := by
  simp [inventory, field]; ring
theorem weighted_drift (r d : ℝ) (c : State) :
    Y (field r d c) = ((1/500000000)+d*(1/8000000000))*c 0*c 1 +
      ((5/2)*c 0-1-d-(1/5000000000))*c 2 +
      ((11/2)*c 1-(29/8))*c 3 + (11/10)*c 4 +
      (r/5-13/5)*c 5 - (r/5)*c 2^2 := by
  simp [Y, field, flux]; ring

theorem material_to_food (c : State) (hc : Nonneg c) :
    A c-c 0 ≤ (16/9)*Y c ∧ B c-c 1 ≤ (10/7)*Y c ∧ c 2 ≤ Y c := by
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  dsimp [A,B,Y]
  constructor
  · linarith
  constructor <;> linarith

theorem inventory_lower (c : State) (hc : Nonneg c) : (5/7)*Y c ≤ inventory c := by
  have h2 := hc 2
  have h3 := hc 3
  have h5 := hc 5
  dsimp [Y,inventory]
  linarith

end
end ProductiveRecovery
