import proofs.CoreCriticalSiphon.Face

noncomputable section
namespace OverlappingSiphonInvasion
open CoreCriticalSiphon

abbrev State := Fin 4 → ℝ

structure Rates where
  recruitment : ℝ
  alpha1 : ℝ
  alpha2 : ℝ
  alpha3 : ℝ
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  beta1 : ℝ
  beta2 : ℝ
  mu0 : ℝ
  mu1 : ℝ
  mu2 : ℝ
  mu3 : ℝ

def rateVector (p : Rates) : Fin 14 → ℝ :=
  ![p.recruitment, p.alpha1, p.alpha2, p.alpha3, p.eta1, p.eta2,
    p.gamma1, p.gamma2, p.beta1, p.beta2, p.mu0, p.mu1, p.mu2, p.mu3]

def PositiveRates (p : Rates) : Prop := ∀ r, 0 < rateVector p r

abbrev source : SourceCRN where
  Species := Fin 4
  Reaction := Fin 14
  reactant := ![![0,0,0,0], ![1,1,0,0], ![1,0,1,0], ![1,0,0,1],
    ![0,1,0,1], ![0,0,1,1], ![0,1,1,0], ![0,1,1,0],
    ![1,0,0,1], ![1,0,0,1], ![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]]
  product := ![![1,0,0,0], ![0,2,0,0], ![0,0,2,0], ![0,0,0,2],
    ![0,0,0,2], ![0,0,0,2], ![0,0,1,1], ![0,1,0,1],
    ![0,1,0,1], ![0,0,1,1], ![0,0,0,0], ![0,0,0,0], ![0,0,0,0], ![0,0,0,0]]
  catalyst := fun _ _ => false

def field (p : Rates) (x : State) : State :=
  ![p.recruitment - x 0 * (p.mu0 + p.alpha1*x 1 + p.alpha2*x 2 +
      (p.alpha3+p.beta1+p.beta2)*x 3),
    x 1*(p.alpha1*x 0-p.gamma1*x 2-p.eta1*x 3-p.mu1)+p.beta1*x 0*x 3,
    x 2*(p.alpha2*x 0-p.gamma2*x 1-p.eta2*x 3-p.mu2)+p.beta2*x 0*x 3,
    (p.gamma1+p.gamma2)*x 1*x 2+x 3*(p.eta1*x 1+p.eta2*x 2+p.alpha3*x 0-p.mu3)]

set_option maxHeartbeats 1000000 in
theorem source_field (p : Rates) (x : State) :
    source.massAction (rateVector p) x = field p x := by
  funext i
  change (∑ r : Fin 14, rateVector p r *
    (∏ j : Fin 4, x j ^ source.reactant r j) *
    ((source.product r i : ℝ) - source.reactant r i)) = field p x i
  fin_cases i <;>
    simp [rateVector, field, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

theorem total_field (p : Rates) (x : State) :
    (field p x) 0 + (field p x) 1 + (field p x) 2 + (field p x) 3 =
    p.recruitment - p.mu0*x 0 - p.mu1*x 1 - p.mu2*x 2 - p.mu3*x 3 := by
  simp [field]
  ring

def siphonA : Finset (Fin 4) := {1,3}
def siphonB : Finset (Fin 4) := {2,3}

theorem source_siphonA : IsSiphon source siphonA := by
  unfold IsSiphon Produces Consumes
  decide
theorem source_siphonB : IsSiphon source siphonB := by
  unfold IsSiphon Produces Consumes
  decide
theorem shared_not_siphon : ¬ IsSiphon source {(3 : Fin 4)} := by
  unfold IsSiphon Produces Consumes
  decide

theorem source_siphons (S : Finset (Fin 4)) :
    IsSiphon source S ↔ S = ∅ ∨ S = siphonA ∨ S = siphonB ∨ S = {1,2,3} := by
  revert S
  unfold IsSiphon Produces Consumes
  decide

/-- The witness used in the guide; changing beta2 preserves reaction support
whenever beta2 is positive. -/
def witness (beta2 : ℝ) : Rates :=
  ⟨4,2,1,1,1/10,1/10,1/10,1/10,1/10,beta2,1,1,1,1⟩

theorem witness_positive (b : ℝ) (hb : 0 < b) : PositiveRates (witness b) := by
  intro r
  fin_cases r <;> norm_num [rateVector, witness, Matrix.cons_val_succ]
  exact hb

def resident1 : State := ![1/2,7/2,0,0]
def resident2 : State := ![1,0,3,0]

theorem witness_resident1 (b : ℝ) : field (witness b) resident1 = 0 := by
  ext i
  fin_cases i <;> norm_num [field, witness, resident1, Matrix.cons_val_two, Matrix.cons_val_three]

theorem witness_resident2 (b : ℝ) : field (witness b) resident2 = 0 := by
  ext i
  fin_cases i <;> norm_num [field, witness, resident2, Matrix.cons_val_two, Matrix.cons_val_three]

end OverlappingSiphonInvasion
