import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch34_eq_targetSlices :
    sourceCoverageBatch34 = sourceCoverageTargetSlice34A ++
      sourceCoverageTargetSlice34B := by
  rfl

theorem sourceCoverageBatch34_targetConsistent :
    sourceCoverageBatch34.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch34_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice34A_targetConsistent,
    sourceCoverageTargetSlice34B_targetConsistent]
theorem sourceCoverageBatch34_length :
    sourceCoverageBatch34.length = 500 := by
  rw [sourceCoverageBatch34_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice34A_length,
    sourceCoverageTargetSlice34B_length]

end SmallCusp
