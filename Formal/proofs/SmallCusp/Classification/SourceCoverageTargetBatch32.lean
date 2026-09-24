import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch32_eq_targetSlices :
    sourceCoverageBatch32 = sourceCoverageTargetSlice32A ++
      sourceCoverageTargetSlice32B := by
  rfl

theorem sourceCoverageBatch32_targetConsistent :
    sourceCoverageBatch32.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch32_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice32A_targetConsistent,
    sourceCoverageTargetSlice32B_targetConsistent]
theorem sourceCoverageBatch32_length :
    sourceCoverageBatch32.length = 500 := by
  rw [sourceCoverageBatch32_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice32A_length,
    sourceCoverageTargetSlice32B_length]

end SmallCusp
