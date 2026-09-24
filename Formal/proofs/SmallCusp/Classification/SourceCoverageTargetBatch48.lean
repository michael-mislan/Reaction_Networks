import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch48_eq_targetSlices :
    sourceCoverageBatch48 = sourceCoverageTargetSlice48A ++
      sourceCoverageTargetSlice48B := by
  rfl

theorem sourceCoverageBatch48_targetConsistent :
    sourceCoverageBatch48.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch48_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice48A_targetConsistent,
    sourceCoverageTargetSlice48B_targetConsistent]
theorem sourceCoverageBatch48_length :
    sourceCoverageBatch48.length = 500 := by
  rw [sourceCoverageBatch48_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice48A_length,
    sourceCoverageTargetSlice48B_length]

end SmallCusp
