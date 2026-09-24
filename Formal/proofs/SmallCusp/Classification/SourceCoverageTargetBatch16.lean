import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch16_eq_targetSlices :
    sourceCoverageBatch16 = sourceCoverageTargetSlice16A ++
      sourceCoverageTargetSlice16B := by
  rfl

theorem sourceCoverageBatch16_targetConsistent :
    sourceCoverageBatch16.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch16_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice16A_targetConsistent,
    sourceCoverageTargetSlice16B_targetConsistent]
theorem sourceCoverageBatch16_length :
    sourceCoverageBatch16.length = 500 := by
  rw [sourceCoverageBatch16_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice16A_length,
    sourceCoverageTargetSlice16B_length]

end SmallCusp
