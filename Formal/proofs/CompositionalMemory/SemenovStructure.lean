import Mathlib

namespace CompositionalMemory.Semenov

/-- Active species S,C,P,E,D,U,V,I. Inactive capture/hydrolysis products
are outside this kinetic subsystem. This is the measured-model reaction list. -/
def stoich : Fin 11 → Fin 8 → Int :=
  ![![0,1,0,-1,-1,1,0,0],![0,-1,0,1,1,-1,0,0],
    ![0,1,-1,0,-1,0,1,0],![0,-1,1,0,1,0,-1,0],
    ![0,0,1,-1,0,1,-1,0],![0,0,-1,1,0,-1,1,0],
    ![-1,-1,1,1,0,0,0,0],![-1,0,0,1,0,0,0,0],
    ![0,-1,0,0,0,0,0,-1],![0,0,-1,0,0,0,0,-1],
    ![0,0,0,-1,0,0,0,-1]]

def charge : Fin 8 → Int := ![1,1,1,1,0,0,0,-1]
def disulfide : Fin 8 → Int := ![0,0,0,0,1,1,1,0]

theorem chemical_charge_preserved (r : Fin 11) :
    (∑ j,charge j*stoich r j)=0 := by
  fin_cases r <;> norm_num [charge,stoich,Fin.sum_univ_succ]

theorem chemical_disulfide_preserved (r : Fin 11) :
    (∑ j,disulfide j*stoich r j)=0 := by
  fin_cases r <;> norm_num [disulfide,stoich,Fin.sum_univ_succ]

/-- Only inflow can increase the total active molecule count. This supplies
the source-specific finite-resource/nonexplosion route for the CSTR model. -/
theorem chemical_active_count_nonincreasing (r : Fin 11) :
    (∑ j,stoich r j) ≤ 0 := by
  fin_cases r <;> norm_num [stoich,Fin.sum_univ_succ]

/-- Fast chemical reactions contribute no quadratic variation to either
linear coordinate. This cancellation is exact at the jump level. -/
theorem chemical_charge_noise_zero (a : Fin 11 → ℝ) :
    (∑ r,a r*((∑ j,charge j*stoich r j : Int) : ℝ)^2)=0 := by
  simp [chemical_charge_preserved]

theorem chemical_disulfide_noise_zero (a : Fin 11 → ℝ) :
    (∑ r,a r*((∑ j,disulfide j*stoich r j : Int) : ℝ)^2)=0 := by
  simp [chemical_disulfide_preserved]

def feed (S0 D0 I0 : ℝ) (j : Fin 8) : ℝ :=
  if j.val=0 then S0 else if j.val=4 then D0 else if j.val=7 then I0 else 0
def chargeValue (n : Fin 8 → ℝ) : ℝ := n 0+n 1+n 2+n 3-n 7
def disulfideValue (n : Fin 8 → ℝ) : ℝ := n 4+n 5+n 6

/-- Drift of the signed count coordinate, with all CSTR feed/outflow channels. -/
theorem charge_flow_drift (n : Fin 8 → ℝ) (Ω SV S0 D0 I0 : ℝ) :
    (∑ j,(charge j : ℝ)*SV*(Ω*feed S0 D0 I0 j-n j))=
      SV*(Ω*(S0-I0)-chargeValue n) := by
  norm_num [charge,feed,chargeValue,Fin.sum_univ_succ,Fin.succ]
  ring_nf
  rfl

theorem disulfide_flow_drift (n : Fin 8 → ℝ) (Ω SV S0 D0 I0 : ℝ) :
    (∑ j,(disulfide j : ℝ)*SV*(Ω*feed S0 D0 I0 j-n j))=
      SV*(Ω*D0-disulfideValue n) := by
  norm_num [disulfide,feed,disulfideValue,Fin.sum_univ_succ,Fin.succ]
  ring_nf
  rfl

/-- Only the listed flow events contribute to this coordinate's jump noise. -/
theorem charge_flow_noise (n : Fin 8 → ℝ) (Ω SV S0 D0 I0 : ℝ) :
    (∑ j,(charge j : ℝ)^2*SV*(Ω*feed S0 D0 I0 j+n j))=
      SV*(Ω*(S0+I0)+n 0+n 1+n 2+n 3+n 7) := by
  norm_num [charge,feed,Fin.sum_univ_succ,Fin.succ]
  ring_nf
  rfl

theorem disulfide_flow_noise (n : Fin 8 → ℝ) (Ω SV S0 D0 I0 : ℝ) :
    (∑ j,(disulfide j : ℝ)^2*SV*(Ω*feed S0 D0 I0 j+n j))=
      SV*(Ω*D0+disulfideValue n) := by
  norm_num [disulfide,feed,disulfideValue,Fin.sum_univ_succ,Fin.succ]
  ring_nf
  rfl

theorem refill_preserves_planes (z : Fin 8 → ℝ) (S0 D0 I0 : ℝ)
    (hZ : chargeValue z=S0-I0) (hD : disulfideValue z=D0) :
    chargeValue (fun j => (z j+feed S0 D0 I0 j)/2)=S0-I0 ∧
      disulfideValue (fun j => (z j+feed S0 D0 I0 j)/2)=D0 := by
  norm_num [chargeValue,disulfideValue,feed] at hZ hD ⊢
  constructor <;> linarith

end CompositionalMemory.Semenov
