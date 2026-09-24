import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch47_eq_targetSlices :
    sourceCoverageBatch47 = sourceCoverageTargetSlice47A ++
      sourceCoverageTargetSlice47B := by
  rfl

theorem sourceCoverageBatch47_targetConsistent :
    sourceCoverageBatch47.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch47_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice47A_targetConsistent,
    sourceCoverageTargetSlice47B_targetConsistent]
theorem sourceCoverageBatch47_length :
    sourceCoverageBatch47.length = 500 := by
  rw [sourceCoverageBatch47_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice47A_length,
    sourceCoverageTargetSlice47B_length]

end SmallCusp
