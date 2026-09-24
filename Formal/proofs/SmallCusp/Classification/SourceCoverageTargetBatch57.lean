import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch57_eq_targetSlices :
    sourceCoverageBatch57 = sourceCoverageTargetSlice57A ++
      sourceCoverageTargetSlice57B := by
  rfl

theorem sourceCoverageBatch57_targetConsistent :
    sourceCoverageBatch57.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch57_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice57A_targetConsistent,
    sourceCoverageTargetSlice57B_targetConsistent]
theorem sourceCoverageBatch57_length :
    sourceCoverageBatch57.length = 500 := by
  rw [sourceCoverageBatch57_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice57A_length,
    sourceCoverageTargetSlice57B_length]

end SmallCusp
