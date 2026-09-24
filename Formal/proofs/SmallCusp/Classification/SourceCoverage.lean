import proofs.SmallCusp.Classification.CoverageTypes
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation
import proofs.SmallCusp.Classification.SourceCoverageSources

namespace SmallCusp

theorem sourceCoverageRecords_docked :
    sourceCoverageRecords.all (fun R => decide R.Docked) = true := by
  simp [sourceCoverageRecords, sourceCoverageValidation00_valid]

theorem sourceCoverageRecords_targetConsistent :
    sourceCoverageRecords.all (fun R => decide R.TargetConsistent) = true := by
  simpa [sourceCoverageRecords] using
    sourceCoverageValidation00_targetConsistent

theorem sourceCoverageRecords_valid :
    sourceCoverageRecords.all (fun R => decide R.Valid) = true := by
  have hd : ∀ R ∈ sourceCoverageRecords, R.Docked := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using
      sourceCoverageRecords_docked
  have ht : ∀ R ∈ sourceCoverageRecords, R.TargetConsistent := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using
      sourceCoverageRecords_targetConsistent
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro R hR
  exact ⟨hd R hR, ht R hR⟩

theorem sourceCoverageRecords_length : sourceCoverageRecords.length = 30051 := by
  simpa [sourceCoverageRecords] using sourceCoverageValidation00_length

end SmallCusp
