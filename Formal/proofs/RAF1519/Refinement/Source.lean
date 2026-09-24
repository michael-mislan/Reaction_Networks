import proofs.ProductiveRecovery.Source

/-! Literal seven-species refinement of the existing exporter. -/
namespace RAF1519.Refinement
noncomputable section
abbrev State := Fin 7 → ℝ
def free (c : State) : ProductiveRecovery.State := ![c 0,c 1,c 2,c 3,c 4,c 5]
def firstFlux (d beta theta : ℝ) (c : State) : ℝ :=
  d*(1+beta)*c 2-d*beta/theta*c 6
def secondFlux (d beta theta : ℝ) (c : State) : ℝ :=
  d/theta*c 6-d*(1/8000000000)*(1+beta)/beta*c 0*c 1
def field (r d beta theta : ℝ) (c : State) : State :=
  let j := ProductiveRecovery.flux r d (free c)
  let a := firstFlux d beta theta c
  let b := secondFlux d beta theta c
  ![1-c 0-j 0-j 1+b,1-c 1-j 0-j 2+b,
    -c 2+j 0-j 1+2*j 4-a,-c 3+j 1-j 2,
    -c 4+j 2-j 3,-c 5+j 3-j 4,a-b-c 6]
def materialA (c : State) : ℝ := ProductiveRecovery.A (free c)+c 6
def materialB (c : State) : ℝ := ProductiveRecovery.B (free c)+c 6
def stock (c : State) : ℝ := ProductiveRecovery.Y (free c)
def service (d beta theta : ℝ) (c : State) : ℝ :=
  d*(1+beta)*c 2+d*beta/theta*c 6
def forcing (beta : ℝ) (c : State) : ℝ := c 2+(1/8000000000)/beta*c 0*c 1
def defect (d beta theta : ℝ) (c : State) : ℝ :=
  d*(forcing beta c-c 6/theta)

theorem material_A (r d beta theta : ℝ) (c : State) :
    materialA (field r d beta theta c) = 1-materialA c := by
  simp [materialA,ProductiveRecovery.A,free,field]; ring
theorem material_B (r d beta theta : ℝ) (c : State) :
    materialB (field r d beta theta c) = 1-materialB c := by
  simp [materialB,ProductiveRecovery.B,free,field]; ring

theorem intermediate_filter (r d beta theta : ℝ) (c : State) (hb : beta ≠ 0) :
    field r d beta theta c 6 = d*(1+beta)*forcing beta c -
      (1+d*(1+beta)/theta)*c 6 := by
  simp [field,firstFlux,secondFlux,forcing]
  field_simp; ring

theorem free_field (r d beta theta : ℝ) (c : State) (hb : beta ≠ 0) :
    free (field r d beta theta c) = ProductiveRecovery.field r d (free c) -
      ![defect d beta theta c,defect d beta theta c,beta*defect d beta theta c,0,0,0] := by
  funext i
  fin_cases i <;>
    simp [free,field,ProductiveRecovery.field,ProductiveRecovery.flux,
      firstFlux,secondFlux,defect,forcing] <;> field_simp <;> ring

theorem gross_service_identity (r d beta theta : ℝ) (c : State)
    (hb : beta ≠ 0) (hb1 : 1+beta ≠ 0) :
    service d beta theta c = d*(1+2*beta)*c 2+d*(1/8000000000)*c 0*c 1 -
      beta/(1+beta)*(field r d beta theta c 6+c 6) := by
  simp [service,field,firstFlux,secondFlux]
  field_simp; ring
end
end RAF1519.Refinement
