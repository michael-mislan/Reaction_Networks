import proofs.SmallCusp.Classification.SourceCoverageTargetValidation09A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation09B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch09_eq_targetSlices :
    sourceCoverageBatch09 = sourceCoverageTargetSlice09A ++
      sourceCoverageTargetSlice09B := by
  rfl

theorem sourceCoverageBatch09_targetConsistent :
    sourceCoverageBatch09.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch09_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice09A_targetConsistent,
    sourceCoverageTargetSlice09B_targetConsistent]
theorem sourceCoverageBatch09_length :
    sourceCoverageBatch09.length = 500 := by
  rw [sourceCoverageBatch09_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice09A_length,
    sourceCoverageTargetSlice09B_length]

end SmallCusp
