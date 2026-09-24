import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch58_eq_targetSlices :
    sourceCoverageBatch58 = sourceCoverageTargetSlice58A ++
      sourceCoverageTargetSlice58B := by
  rfl

theorem sourceCoverageBatch58_targetConsistent :
    sourceCoverageBatch58.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch58_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice58A_targetConsistent,
    sourceCoverageTargetSlice58B_targetConsistent]
theorem sourceCoverageBatch58_length :
    sourceCoverageBatch58.length = 500 := by
  rw [sourceCoverageBatch58_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice58A_length,
    sourceCoverageTargetSlice58B_length]

end SmallCusp
