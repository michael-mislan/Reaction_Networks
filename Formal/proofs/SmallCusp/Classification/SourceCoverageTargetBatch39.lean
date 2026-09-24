import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch39_eq_targetSlices :
    sourceCoverageBatch39 = sourceCoverageTargetSlice39A ++
      sourceCoverageTargetSlice39B := by
  rfl

theorem sourceCoverageBatch39_targetConsistent :
    sourceCoverageBatch39.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch39_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice39A_targetConsistent,
    sourceCoverageTargetSlice39B_targetConsistent]
theorem sourceCoverageBatch39_length :
    sourceCoverageBatch39.length = 500 := by
  rw [sourceCoverageBatch39_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice39A_length,
    sourceCoverageTargetSlice39B_length]

end SmallCusp
