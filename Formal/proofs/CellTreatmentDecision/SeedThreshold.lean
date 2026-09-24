import proofs.CellTreatmentDecision.FiniteSource

namespace CellTreatmentDecision

noncomputable section

def seedA (c : ℝ) : ℝ := 1684141/335544320 + (428807/251658240)*c
def seedB : ℝ := 6767/1310720
def threshold : ℝ := 144633/1715228

theorem threshold_identity (c : ℝ) :
    seedA c - seedB = (428807/251658240)*(c-threshold) := by
  unfold seedA seedB threshold
  ring

theorem seed_signs :
    seedA (-(1/5)) - seedB = -(2438393/5033164800:ℝ) ∧
    seedA (1/5) - seedB = (992063/5033164800:ℝ) := by
  norm_num [seedA, seedB]

theorem ranking (c : ℝ) : seedB < seedA c ↔ threshold < c := by
  have h := threshold_identity c
  constructor <;> intro hc <;> nlinarith

theorem fibre_endpoints (c : ℝ) (lo : -(1/4:ℝ) ≤ c) (hi : c ≤ 1/4) :
    -(142087/503316480:ℝ) ≤ seedB-seedA c ∧
    seedB-seedA c ≤ (7/12288:ℝ) := by
  unfold seedA seedB
  constructor <;> linarith

end
end CellTreatmentDecision
