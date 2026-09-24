import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch59_eq_targetSlices :
    sourceCoverageBatch59 = sourceCoverageTargetSlice59A ++
      sourceCoverageTargetSlice59B := by
  rfl

theorem sourceCoverageBatch59_targetConsistent :
    sourceCoverageBatch59.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch59_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice59A_targetConsistent,
    sourceCoverageTargetSlice59B_targetConsistent]
theorem sourceCoverageBatch59_length :
    sourceCoverageBatch59.length = 500 := by
  rw [sourceCoverageBatch59_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice59A_length,
    sourceCoverageTargetSlice59B_length]

end SmallCusp
