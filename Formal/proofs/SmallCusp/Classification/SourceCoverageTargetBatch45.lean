import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch45_eq_targetSlices :
    sourceCoverageBatch45 = sourceCoverageTargetSlice45A ++
      sourceCoverageTargetSlice45B := by
  rfl

theorem sourceCoverageBatch45_targetConsistent :
    sourceCoverageBatch45.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch45_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice45A_targetConsistent,
    sourceCoverageTargetSlice45B_targetConsistent]
theorem sourceCoverageBatch45_length :
    sourceCoverageBatch45.length = 500 := by
  rw [sourceCoverageBatch45_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice45A_length,
    sourceCoverageTargetSlice45B_length]

end SmallCusp
