import proofs.SmallCusp.Classification.SourceCoverageTargetValidation07A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation07B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch07_eq_targetSlices :
    sourceCoverageBatch07 = sourceCoverageTargetSlice07A ++
      sourceCoverageTargetSlice07B := by
  rfl

theorem sourceCoverageBatch07_targetConsistent :
    sourceCoverageBatch07.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch07_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice07A_targetConsistent,
    sourceCoverageTargetSlice07B_targetConsistent]
theorem sourceCoverageBatch07_length :
    sourceCoverageBatch07.length = 500 := by
  rw [sourceCoverageBatch07_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice07A_length,
    sourceCoverageTargetSlice07B_length]

end SmallCusp
