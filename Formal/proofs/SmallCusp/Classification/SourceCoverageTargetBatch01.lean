import proofs.SmallCusp.Classification.SourceCoverageTargetValidation01A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation01B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch01_eq_targetSlices :
    sourceCoverageBatch01 = sourceCoverageTargetSlice01A ++
      sourceCoverageTargetSlice01B := by
  rfl

theorem sourceCoverageBatch01_targetConsistent :
    sourceCoverageBatch01.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch01_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice01A_targetConsistent,
    sourceCoverageTargetSlice01B_targetConsistent]
theorem sourceCoverageBatch01_length :
    sourceCoverageBatch01.length = 500 := by
  rw [sourceCoverageBatch01_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice01A_length,
    sourceCoverageTargetSlice01B_length]

end SmallCusp
