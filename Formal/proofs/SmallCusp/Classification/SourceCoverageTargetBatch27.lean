import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch27_eq_targetSlices :
    sourceCoverageBatch27 = sourceCoverageTargetSlice27A ++
      sourceCoverageTargetSlice27B := by
  rfl

theorem sourceCoverageBatch27_targetConsistent :
    sourceCoverageBatch27.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch27_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice27A_targetConsistent,
    sourceCoverageTargetSlice27B_targetConsistent]
theorem sourceCoverageBatch27_length :
    sourceCoverageBatch27.length = 500 := by
  rw [sourceCoverageBatch27_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice27A_length,
    sourceCoverageTargetSlice27B_length]

end SmallCusp
