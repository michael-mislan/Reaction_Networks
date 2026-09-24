import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch49_eq_targetSlices :
    sourceCoverageBatch49 = sourceCoverageTargetSlice49A ++
      sourceCoverageTargetSlice49B := by
  rfl

theorem sourceCoverageBatch49_targetConsistent :
    sourceCoverageBatch49.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch49_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice49A_targetConsistent,
    sourceCoverageTargetSlice49B_targetConsistent]
theorem sourceCoverageBatch49_length :
    sourceCoverageBatch49.length = 500 := by
  rw [sourceCoverageBatch49_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice49A_length,
    sourceCoverageTargetSlice49B_length]

end SmallCusp
