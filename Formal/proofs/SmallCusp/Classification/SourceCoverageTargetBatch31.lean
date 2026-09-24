import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch31_eq_targetSlices :
    sourceCoverageBatch31 = sourceCoverageTargetSlice31A ++
      sourceCoverageTargetSlice31B := by
  rfl

theorem sourceCoverageBatch31_targetConsistent :
    sourceCoverageBatch31.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch31_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice31A_targetConsistent,
    sourceCoverageTargetSlice31B_targetConsistent]
theorem sourceCoverageBatch31_length :
    sourceCoverageBatch31.length = 500 := by
  rw [sourceCoverageBatch31_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice31A_length,
    sourceCoverageTargetSlice31B_length]

end SmallCusp
