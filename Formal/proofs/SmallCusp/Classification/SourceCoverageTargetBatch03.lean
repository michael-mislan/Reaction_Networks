import proofs.SmallCusp.Classification.SourceCoverageTargetValidation03A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation03B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch03_eq_targetSlices :
    sourceCoverageBatch03 = sourceCoverageTargetSlice03A ++
      sourceCoverageTargetSlice03B := by
  rfl

theorem sourceCoverageBatch03_targetConsistent :
    sourceCoverageBatch03.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch03_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice03A_targetConsistent,
    sourceCoverageTargetSlice03B_targetConsistent]
theorem sourceCoverageBatch03_length :
    sourceCoverageBatch03.length = 500 := by
  rw [sourceCoverageBatch03_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice03A_length,
    sourceCoverageTargetSlice03B_length]

end SmallCusp
