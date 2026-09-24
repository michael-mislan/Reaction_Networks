import proofs.SmallCusp.Classification.SourceCoverageTargetValidation08A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation08B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch08_eq_targetSlices :
    sourceCoverageBatch08 = sourceCoverageTargetSlice08A ++
      sourceCoverageTargetSlice08B := by
  rfl

theorem sourceCoverageBatch08_targetConsistent :
    sourceCoverageBatch08.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch08_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice08A_targetConsistent,
    sourceCoverageTargetSlice08B_targetConsistent]
theorem sourceCoverageBatch08_length :
    sourceCoverageBatch08.length = 500 := by
  rw [sourceCoverageBatch08_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice08A_length,
    sourceCoverageTargetSlice08B_length]

end SmallCusp
