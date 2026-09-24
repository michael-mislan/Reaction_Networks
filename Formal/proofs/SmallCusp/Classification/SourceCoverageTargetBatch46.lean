import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch46_eq_targetSlices :
    sourceCoverageBatch46 = sourceCoverageTargetSlice46A ++
      sourceCoverageTargetSlice46B := by
  rfl

theorem sourceCoverageBatch46_targetConsistent :
    sourceCoverageBatch46.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch46_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice46A_targetConsistent,
    sourceCoverageTargetSlice46B_targetConsistent]
theorem sourceCoverageBatch46_length :
    sourceCoverageBatch46.length = 500 := by
  rw [sourceCoverageBatch46_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice46A_length,
    sourceCoverageTargetSlice46B_length]

end SmallCusp
