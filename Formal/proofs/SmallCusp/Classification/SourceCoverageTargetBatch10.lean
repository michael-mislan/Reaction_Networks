import proofs.SmallCusp.Classification.SourceCoverageTargetValidation10A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation10B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch10_eq_targetSlices :
    sourceCoverageBatch10 = sourceCoverageTargetSlice10A ++
      sourceCoverageTargetSlice10B := by
  rfl

theorem sourceCoverageBatch10_targetConsistent :
    sourceCoverageBatch10.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch10_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice10A_targetConsistent,
    sourceCoverageTargetSlice10B_targetConsistent]
theorem sourceCoverageBatch10_length :
    sourceCoverageBatch10.length = 500 := by
  rw [sourceCoverageBatch10_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice10A_length,
    sourceCoverageTargetSlice10B_length]

end SmallCusp
