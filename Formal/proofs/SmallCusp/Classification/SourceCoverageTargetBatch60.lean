import proofs.SmallCusp.Classification.SourceCoverageTargetValidation60A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation60B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch60_eq_targetSlices :
    sourceCoverageBatch60 = sourceCoverageTargetSlice60A ++
      sourceCoverageTargetSlice60B := by
  rfl

theorem sourceCoverageBatch60_targetConsistent :
    sourceCoverageBatch60.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch60_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice60A_targetConsistent,
    sourceCoverageTargetSlice60B_targetConsistent]
theorem sourceCoverageBatch60_length :
    sourceCoverageBatch60.length = 51 := by
  rw [sourceCoverageBatch60_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice60A_length,
    sourceCoverageTargetSlice60B_length]

end SmallCusp
