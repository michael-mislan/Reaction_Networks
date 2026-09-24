import proofs.RAF1519.Refinement.CountMaterialDynamics
import proofs.RAF1519.Refinement.FlowBounds

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability

def materialNode {n : ℕ} (b : Bool) (V : ℝ) (N : MolecularState n) (i : Fin n) : ℝ :=
  weightedCoordinate (materialWeight b) (concentration V (fun s => N (i,s)))

def materialSafe {n : ℕ} (V : ℝ) (N : MolecularState n) : Prop :=
  ∀ b i, |materialNode b V N i-1| ≤ 1/10

/-- An absorbing history stop, rather than an instantaneous state test. -/
def materialExit {n : ℕ} (V : ℝ) (l : ℕ)
    (h : Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) : Prop :=
  ∃ i, ¬materialSafe V (h i).1

theorem materialSafe_coordinate {n : ℕ} (V : ℝ) (hV : 0 < V) (N : MolecularState n)
    (h : materialSafe V N) : N ∈ countCorridor V := by
  intro p
  have ha := (abs_le.mp (h false p.1)).2
  have hb := (abs_le.mp (h true p.1)).2
  change weightedCoordinate weightA (concentration V (fun s => N (p.1,s)))-1 ≤ _ at ha
  change weightedCoordinate weightB (concentration V (fun s => N (p.1,s)))-1 ≤ _ at hb
  rw [← materialA_weighted] at ha
  rw [← materialB_weighted] at hb
  exact coordinate_bound (concentration V (fun s => N (p.1,s)))
    (fun s => div_nonneg (Nat.cast_nonneg _) hV.le) (by linarith) (by linarith) p.2

theorem materialExit_measurable {n : ℕ} (V : ℝ) (l : ℕ) :
    MeasurableSet {h : Finset.Iic l → JumpState (MolecularState n) (CountChannel n) | materialExit V l h} := by
  unfold materialExit
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  exact (Set.to_countable {N : MolecularState n | ¬materialSafe V N}).measurableSet.preimage
    (measurable_pi_apply i).fst

theorem material_unstopped {n : ℕ} (V : ℝ) (hV : 0 < V)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (j : ℕ)
    (hj : prefixElapsed j (Preorder.frestrictLe j z) < 4)
    (hs : ∀ i ≤ j, materialSafe V (z i).1) :
    ¬coordinateStop (countCorridor V) 4 (materialExit V) j (Preorder.frestrictLe j z) := by
  simp only [coordinateStop,not_or,not_not]
  refine ⟨?_,?_,not_le.mpr hj⟩
  · rintro ⟨i,hi⟩
    apply hi
    simpa only [Preorder.frestrictLe_apply] using hs i (Finset.mem_Iic.mp i.property)
  · simpa only [Preorder.frestrictLe_apply] using materialSafe_coordinate V hV (z j).1 (hs j le_rfl)

end
end RAF1519.Refinement
