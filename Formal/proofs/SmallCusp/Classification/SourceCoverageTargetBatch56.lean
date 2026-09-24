import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch56_eq_targetSlices :
    sourceCoverageBatch56 = sourceCoverageTargetSlice56A ++
      sourceCoverageTargetSlice56B := by
  rfl

theorem sourceCoverageBatch56_targetConsistent :
    sourceCoverageBatch56.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch56_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice56A_targetConsistent,
    sourceCoverageTargetSlice56B_targetConsistent]
theorem sourceCoverageBatch56_length :
    sourceCoverageBatch56.length = 500 := by
  rw [sourceCoverageBatch56_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice56A_length,
    sourceCoverageTargetSlice56B_length]

end SmallCusp
