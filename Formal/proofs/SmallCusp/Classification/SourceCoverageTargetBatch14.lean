import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch14_eq_targetSlices :
    sourceCoverageBatch14 = sourceCoverageTargetSlice14A ++
      sourceCoverageTargetSlice14B := by
  rfl

theorem sourceCoverageBatch14_targetConsistent :
    sourceCoverageBatch14.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch14_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice14A_targetConsistent,
    sourceCoverageTargetSlice14B_targetConsistent]
theorem sourceCoverageBatch14_length :
    sourceCoverageBatch14.length = 500 := by
  rw [sourceCoverageBatch14_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice14A_length,
    sourceCoverageTargetSlice14B_length]

end SmallCusp
