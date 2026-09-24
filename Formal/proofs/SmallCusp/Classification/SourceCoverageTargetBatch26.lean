import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch26_eq_targetSlices :
    sourceCoverageBatch26 = sourceCoverageTargetSlice26A ++
      sourceCoverageTargetSlice26B := by
  rfl

theorem sourceCoverageBatch26_targetConsistent :
    sourceCoverageBatch26.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch26_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice26A_targetConsistent,
    sourceCoverageTargetSlice26B_targetConsistent]
theorem sourceCoverageBatch26_length :
    sourceCoverageBatch26.length = 500 := by
  rw [sourceCoverageBatch26_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice26A_length,
    sourceCoverageTargetSlice26B_length]

end SmallCusp
