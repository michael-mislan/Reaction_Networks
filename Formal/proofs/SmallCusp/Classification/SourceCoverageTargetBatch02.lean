import proofs.SmallCusp.Classification.SourceCoverageTargetValidation02A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation02B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch02_eq_targetSlices :
    sourceCoverageBatch02 = sourceCoverageTargetSlice02A ++
      sourceCoverageTargetSlice02B := by
  rfl

theorem sourceCoverageBatch02_targetConsistent :
    sourceCoverageBatch02.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch02_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice02A_targetConsistent,
    sourceCoverageTargetSlice02B_targetConsistent]
theorem sourceCoverageBatch02_length :
    sourceCoverageBatch02.length = 500 := by
  rw [sourceCoverageBatch02_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice02A_length,
    sourceCoverageTargetSlice02B_length]

end SmallCusp
