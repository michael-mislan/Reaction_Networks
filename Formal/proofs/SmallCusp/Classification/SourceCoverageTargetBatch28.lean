import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch28_eq_targetSlices :
    sourceCoverageBatch28 = sourceCoverageTargetSlice28A ++
      sourceCoverageTargetSlice28B := by
  rfl

theorem sourceCoverageBatch28_targetConsistent :
    sourceCoverageBatch28.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch28_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice28A_targetConsistent,
    sourceCoverageTargetSlice28B_targetConsistent]
theorem sourceCoverageBatch28_length :
    sourceCoverageBatch28.length = 500 := by
  rw [sourceCoverageBatch28_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice28A_length,
    sourceCoverageTargetSlice28B_length]

end SmallCusp
