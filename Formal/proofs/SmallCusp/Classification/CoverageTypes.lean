import proofs.SmallCusp.Classification.LightCoverageTypes
import proofs.SmallCusp.Cusp.PositiveCuspLayer
import proofs.SmallCusp.Obstruction.ConicDeterminantLayer
import proofs.SmallCusp.Obstruction.CircuitFoldLayer
import proofs.SmallCusp.Obstruction.CubicResidualLayer

namespace SmallCusp

def outcomeSize : CuspOutcome → ℕ
  | .cusp => bimolecularCuspClasses.length
  | .determinant => conicDeterminantLayerRecords.length
  | .fold => circuitFoldLayerRecords.length
  | .cubic => cubicResidualLayerRecords.length

theorem cuspOutcome_exhaustive (outcome : CuspOutcome) :
    outcome = .cusp ∨ outcome = .determinant ∨
      outcome = .fold ∨ outcome = .cubic := by
  cases outcome <;> simp

theorem cuspOutcome_pairwise_exclusive :
    CuspOutcome.cusp ≠ .determinant ∧
    CuspOutcome.cusp ≠ .fold ∧
    CuspOutcome.cusp ≠ .cubic ∧
    CuspOutcome.determinant ≠ .fold ∧
    CuspOutcome.determinant ≠ .cubic ∧
    CuspOutcome.fold ≠ .cubic := by
  decide

theorem bimolecularMechanismClass_partition_count :
    bimolecularCuspClasses.length +
      conicDeterminantLayerRecords.length +
      circuitFoldLayerRecords.length +
      cubicResidualLayerRecords.length = 9999 := by
  rw [bimolecularCuspClasses_length,
    conicDeterminantLayerRecords_length,
    circuitFoldLayerRecords_length,
    cubicResidualLayerRecords_length]

def bimolecularCuspClassArray : Array CodedBimolNetwork :=
  bimolecularCuspClasses.toArray

def conicDeterminantLayerArray : Array RationalConicRecord :=
  conicDeterminantLayerRecords.toArray

def circuitFoldLayerArray : Array CircuitFoldLayerRecord :=
  circuitFoldLayerRecords.toArray

def cubicResidualLayerArray : Array CubicResidualRecord :=
  cubicResidualLayerRecords.toArray

def SourceCoverageRecord.mechanismTarget (R : SourceCoverageRecord) :
    CodedBimolNetwork :=
  match R.outcome with
  | .cusp => (bimolecularCuspClassArray[R.targetIndex]?).getD positiveCusp0
  | .determinant =>
      ((conicDeterminantLayerArray[R.targetIndex]?).map
        (fun x : RationalConicRecord => x.network)).getD positiveCusp0
  | .fold =>
      ((circuitFoldLayerArray[R.targetIndex]?).map
        (fun x : CircuitFoldLayerRecord => x.network)).getD positiveCusp0
  | .cubic =>
      ((cubicResidualLayerArray[R.targetIndex]?).map
        (fun x : CubicResidualRecord => x.network)).getD positiveCusp0

def SourceCoverageRecord.TargetConsistent (R : SourceCoverageRecord) : Prop :=
  R.targetIndex < outcomeSize R.outcome ∧
    ∀ r, R.targetNetwork.reaction r = R.mechanismTarget.reaction r

instance sourceCoverageRecord_targetConsistent_decidable (R : SourceCoverageRecord) :
    Decidable R.TargetConsistent := by
  unfold SourceCoverageRecord.TargetConsistent
  infer_instance

def SourceCoverageRecord.Valid (R : SourceCoverageRecord) : Prop :=
  R.Docked ∧ R.TargetConsistent

instance sourceCoverageRecord_valid_decidable (R : SourceCoverageRecord) :
    Decidable R.Valid := by
  unfold SourceCoverageRecord.Valid SourceCoverageRecord.TargetConsistent
  infer_instance

theorem SourceCoverageRecord.targetNetwork_eq_mechanismTarget
    (R : SourceCoverageRecord) (hR : R.TargetConsistent) :
    R.targetNetwork = R.mechanismTarget := by
  cases hleft : R.targetNetwork with
  | mk leftReaction leftNoSelf leftInjective =>
    cases hright : R.mechanismTarget with
    | mk rightReaction rightNoSelf rightInjective =>
      congr
      funext r
      have hr := hR.2 r
      simpa [hleft, hright] using hr

theorem SourceCoverageRecord.target_admits (R : SourceCoverageRecord)
    (hR : R.Valid) (h : R.outcome = .cusp) :
    AdmitsTransverseCusp R.targetNetwork.toNetwork := by
  rw [R.targetNetwork_eq_mechanismTarget hR.2]
  rcases R with ⟨sourceIndices, targetIndices, matching,
    outcome, targetIndex, swapTarget⟩
  cases outcome
  · have hbound : targetIndex < bimolecularCuspClasses.length := hR.2.1
    rw [show SourceCoverageRecord.mechanismTarget
        ⟨sourceIndices, targetIndices, matching,
          .cusp, targetIndex, swapTarget⟩ =
          bimolecularCuspClasses.get ⟨targetIndex, hbound⟩ by
      simp [SourceCoverageRecord.mechanismTarget,
        bimolecularCuspClassArray, hbound]]
    exact bimolecularCuspClass_admits (List.get_mem _ _)
  all_goals simp at h

theorem SourceCoverageRecord.target_excludes (R : SourceCoverageRecord)
    (hR : R.Valid) (h : R.outcome ≠ .cusp) :
    ¬ AdmitsTransverseCusp R.targetNetwork.toNetwork := by
  rw [R.targetNetwork_eq_mechanismTarget hR.2]
  rcases R with ⟨sourceIndices, targetIndices, matching,
    outcome, targetIndex, swapTarget⟩
  cases outcome
  · exact False.elim (h rfl)
  · have hbound : targetIndex < conicDeterminantLayerRecords.length := hR.2.1
    rw [show SourceCoverageRecord.mechanismTarget
        ⟨sourceIndices, targetIndices, matching,
          .determinant, targetIndex, swapTarget⟩ =
          (conicDeterminantLayerRecords.get ⟨targetIndex, hbound⟩).network by
      simp [SourceCoverageRecord.mechanismTarget,
        conicDeterminantLayerArray, hbound]]
    apply isConicDeterminantLayerNetwork_excludes_cusp
    exact ⟨conicDeterminantLayerRecords.get ⟨targetIndex, hbound⟩,
      List.get_mem _ _, rfl⟩
  · have hbound : targetIndex < circuitFoldLayerRecords.length := hR.2.1
    rw [show SourceCoverageRecord.mechanismTarget
        ⟨sourceIndices, targetIndices, matching,
          .fold, targetIndex, swapTarget⟩ =
          (circuitFoldLayerRecords.get ⟨targetIndex, hbound⟩).network by
      simp [SourceCoverageRecord.mechanismTarget,
        circuitFoldLayerArray, hbound]]
    apply isCircuitFoldLayerNetwork_excludes_cusp
    exact ⟨circuitFoldLayerRecords.get ⟨targetIndex, hbound⟩,
      List.get_mem _ _, rfl⟩
  · have hbound : targetIndex < cubicResidualLayerRecords.length := hR.2.1
    rw [show SourceCoverageRecord.mechanismTarget
        ⟨sourceIndices, targetIndices, matching,
          .cubic, targetIndex, swapTarget⟩ =
          (cubicResidualLayerRecords.get ⟨targetIndex, hbound⟩).network by
      simp [SourceCoverageRecord.mechanismTarget,
        cubicResidualLayerArray, hbound]]
    apply isCubicResidualLayerNetwork_excludes_cusp
    exact ⟨cubicResidualLayerRecords.get ⟨targetIndex, hbound⟩,
      List.get_mem _ _, rfl⟩

theorem SourceCoverageRecord.cusp_iff_target (R : SourceCoverageRecord)
    (hR : R.Valid) :
    AdmitsTransverseCusp R.sourceNetwork.toNetwork ↔
      AdmitsTransverseCusp R.targetNetwork.toNetwork := by
  have horient := codedSimplyEquivalent_admitsTransverseCusp_iff
    (R.docked_implies_codedSimplyEquivalent hR.1)
  by_cases hs : R.swapTarget
  · simp only [SourceCoverageRecord.orientedTargetCode, hs, if_true] at horient
    exact horient.trans (swapCodedNetwork_admitsTransverseCusp_iff R.targetNetwork)
  · simpa [SourceCoverageRecord.orientedTargetCode, hs] using horient

theorem SourceCoverageRecord.classifies (R : SourceCoverageRecord)
    (hR : R.Valid) :
    AdmitsTransverseCusp R.sourceNetwork.toNetwork ↔ R.outcome = .cusp := by
  rw [R.cusp_iff_target hR]
  cases ho : R.outcome
  · simp only [iff_true]
    exact R.target_admits hR ho
  · simp only [reduceCtorEq, iff_false]
    exact R.target_excludes hR (by simp [ho])
  · simp only [reduceCtorEq, iff_false]
    exact R.target_excludes hR (by simp [ho])
  · simp only [reduceCtorEq, iff_false]
    exact R.target_excludes hR (by simp [ho])

end SmallCusp
