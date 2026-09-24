import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch52_eq_targetSlices :
    sourceCoverageBatch52 = sourceCoverageTargetSlice52A ++
      sourceCoverageTargetSlice52B := by
  rfl

theorem sourceCoverageBatch52_targetConsistent :
    sourceCoverageBatch52.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch52_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice52A_targetConsistent,
    sourceCoverageTargetSlice52B_targetConsistent]
theorem sourceCoverageBatch52_length :
    sourceCoverageBatch52.length = 500 := by
  rw [sourceCoverageBatch52_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice52A_length,
    sourceCoverageTargetSlice52B_length]

end SmallCusp
