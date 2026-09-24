import proofs.ProductiveRecovery.Source

namespace RAF1314
noncomputable section
open ProductiveRecovery
abbrev Phases := Fin 4 → ℝ

def reconstruct (a b : ℝ) (v : Phases) : State :=
  ![a-v 0-2*v 1-2*v 2-2*v 3, b-v 0-v 1-2*v 2-2*v 3,
    v 0,v 1,v 2,v 3]

theorem reconstructed_material (a b : ℝ) (v : Phases) :
    A (reconstruct a b v)=a ∧ B (reconstruct a b v)=b := by
  simp [A,B,reconstruct]
  constructor <;> ring

theorem material_reconstruction (c : State) :
    reconstruct (A c) (B c) ![c 2,c 3,c 4,c 5] = c := by
  ext s
  fin_cases s <;> simp [reconstruct,A,B] <;> ring

/-- Literal freezing residual; it is not a bound on random trajectories. -/
theorem freezing_residual (r d a b : ℝ) (v : Phases) :
    field r d (reconstruct (1+a) (1+b) v) 2 - field r d (reconstruct 1 1 v) 2 =
      ((1/500000000)+d*(1/8000000000))*
        ((reconstruct 1 1 v) 0*b+(reconstruct 1 1 v) 1*a+a*b)-20*v 0*a ∧
    field r d (reconstruct (1+a) (1+b) v) 3 - field r d (reconstruct 1 1 v) 3 =
      20*v 0*a-20*v 1*b ∧
    field r d (reconstruct (1+a) (1+b) v) 4 - field r d (reconstruct 1 1 v) 4 =
      20*v 1*b ∧
    field r d (reconstruct (1+a) (1+b) v) 5 - field r d (reconstruct 1 1 v) 5 = 0 := by
  simp [field,flux,reconstruct]
  constructor
  · ring
  constructor
  · ring
  ring

private theorem vector_six_last (a b c d e f : ℝ) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def witnessA : State := ![87/100,9/10,1/25,3/100,1/100,1/200]
def witnessB : State := ![4361/5000,4491/5000,1/25,13/500,59/5000,61/10000]

theorem summary_witness_nonneg : Nonneg witnessA ∧ Nonneg witnessB := by
  constructor <;> intro s <;> fin_cases s <;> norm_num [witnessA,witnessB]

theorem summary_witness :
    A witnessA = 1 ∧ A witnessB = 1 ∧ B witnessA = 1 ∧ B witnessB = 1 ∧
    Y witnessA = Y witnessB ∧ inventory witnessA = inventory witnessB ∧
    witnessA 2 = witnessB 2 ∧
    field 20 (3/100) witnessB 2 - field 20 (3/100) witnessA 2 =
      -(755199999983567647/20000000000000000000) := by
  norm_num [witnessA,witnessB,A,B,Y,inventory,field,flux, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', vector_six_last]

end
end RAF1314
