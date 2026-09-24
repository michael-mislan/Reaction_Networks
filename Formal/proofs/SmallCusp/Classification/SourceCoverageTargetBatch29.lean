import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch29_eq_targetSlices :
    sourceCoverageBatch29 = sourceCoverageTargetSlice29A ++
      sourceCoverageTargetSlice29B := by
  rfl

theorem sourceCoverageBatch29_targetConsistent :
    sourceCoverageBatch29.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch29_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice29A_targetConsistent,
    sourceCoverageTargetSlice29B_targetConsistent]
theorem sourceCoverageBatch29_length :
    sourceCoverageBatch29.length = 500 := by
  rw [sourceCoverageBatch29_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice29A_length,
    sourceCoverageTargetSlice29B_length]

end SmallCusp
