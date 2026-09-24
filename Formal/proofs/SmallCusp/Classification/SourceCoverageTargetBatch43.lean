import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch43_eq_targetSlices :
    sourceCoverageBatch43 = sourceCoverageTargetSlice43A ++
      sourceCoverageTargetSlice43B := by
  rfl

theorem sourceCoverageBatch43_targetConsistent :
    sourceCoverageBatch43.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch43_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice43A_targetConsistent,
    sourceCoverageTargetSlice43B_targetConsistent]
theorem sourceCoverageBatch43_length :
    sourceCoverageBatch43.length = 500 := by
  rw [sourceCoverageBatch43_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice43A_length,
    sourceCoverageTargetSlice43B_length]

end SmallCusp
