import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch36_eq_targetSlices :
    sourceCoverageBatch36 = sourceCoverageTargetSlice36A ++
      sourceCoverageTargetSlice36B := by
  rfl

theorem sourceCoverageBatch36_targetConsistent :
    sourceCoverageBatch36.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch36_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice36A_targetConsistent,
    sourceCoverageTargetSlice36B_targetConsistent]
theorem sourceCoverageBatch36_length :
    sourceCoverageBatch36.length = 500 := by
  rw [sourceCoverageBatch36_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice36A_length,
    sourceCoverageTargetSlice36B_length]

end SmallCusp
