import proofs.SmallCusp.Classification.SourceCoverageTargetValidation06A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation06B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch06_eq_targetSlices :
    sourceCoverageBatch06 = sourceCoverageTargetSlice06A ++
      sourceCoverageTargetSlice06B := by
  rfl

theorem sourceCoverageBatch06_targetConsistent :
    sourceCoverageBatch06.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch06_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice06A_targetConsistent,
    sourceCoverageTargetSlice06B_targetConsistent]
theorem sourceCoverageBatch06_length :
    sourceCoverageBatch06.length = 500 := by
  rw [sourceCoverageBatch06_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice06A_length,
    sourceCoverageTargetSlice06B_length]

end SmallCusp
