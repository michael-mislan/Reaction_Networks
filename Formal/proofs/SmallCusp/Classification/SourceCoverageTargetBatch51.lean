import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch51_eq_targetSlices :
    sourceCoverageBatch51 = sourceCoverageTargetSlice51A ++
      sourceCoverageTargetSlice51B := by
  rfl

theorem sourceCoverageBatch51_targetConsistent :
    sourceCoverageBatch51.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch51_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice51A_targetConsistent,
    sourceCoverageTargetSlice51B_targetConsistent]
theorem sourceCoverageBatch51_length :
    sourceCoverageBatch51.length = 500 := by
  rw [sourceCoverageBatch51_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice51A_length,
    sourceCoverageTargetSlice51B_length]

end SmallCusp
