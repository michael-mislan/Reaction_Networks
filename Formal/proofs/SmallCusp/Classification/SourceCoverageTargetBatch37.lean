import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch37_eq_targetSlices :
    sourceCoverageBatch37 = sourceCoverageTargetSlice37A ++
      sourceCoverageTargetSlice37B := by
  rfl

theorem sourceCoverageBatch37_targetConsistent :
    sourceCoverageBatch37.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch37_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice37A_targetConsistent,
    sourceCoverageTargetSlice37B_targetConsistent]
theorem sourceCoverageBatch37_length :
    sourceCoverageBatch37.length = 500 := by
  rw [sourceCoverageBatch37_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice37A_length,
    sourceCoverageTargetSlice37B_length]

end SmallCusp
