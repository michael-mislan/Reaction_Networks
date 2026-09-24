import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch30_eq_targetSlices :
    sourceCoverageBatch30 = sourceCoverageTargetSlice30A ++
      sourceCoverageTargetSlice30B := by
  rfl

theorem sourceCoverageBatch30_targetConsistent :
    sourceCoverageBatch30.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch30_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice30A_targetConsistent,
    sourceCoverageTargetSlice30B_targetConsistent]
theorem sourceCoverageBatch30_length :
    sourceCoverageBatch30.length = 500 := by
  rw [sourceCoverageBatch30_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice30A_length,
    sourceCoverageTargetSlice30B_length]

end SmallCusp
