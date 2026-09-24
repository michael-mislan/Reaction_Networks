import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch41_eq_targetSlices :
    sourceCoverageBatch41 = sourceCoverageTargetSlice41A ++
      sourceCoverageTargetSlice41B := by
  rfl

theorem sourceCoverageBatch41_targetConsistent :
    sourceCoverageBatch41.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch41_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice41A_targetConsistent,
    sourceCoverageTargetSlice41B_targetConsistent]
theorem sourceCoverageBatch41_length :
    sourceCoverageBatch41.length = 500 := by
  rw [sourceCoverageBatch41_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice41A_length,
    sourceCoverageTargetSlice41B_length]

end SmallCusp
