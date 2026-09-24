import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch44_eq_targetSlices :
    sourceCoverageBatch44 = sourceCoverageTargetSlice44A ++
      sourceCoverageTargetSlice44B := by
  rfl

theorem sourceCoverageBatch44_targetConsistent :
    sourceCoverageBatch44.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch44_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice44A_targetConsistent,
    sourceCoverageTargetSlice44B_targetConsistent]
theorem sourceCoverageBatch44_length :
    sourceCoverageBatch44.length = 500 := by
  rw [sourceCoverageBatch44_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice44A_length,
    sourceCoverageTargetSlice44B_length]

end SmallCusp
