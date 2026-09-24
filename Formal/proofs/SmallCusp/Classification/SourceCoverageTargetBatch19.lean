import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch19_eq_targetSlices :
    sourceCoverageBatch19 = sourceCoverageTargetSlice19A ++
      sourceCoverageTargetSlice19B := by
  rfl

theorem sourceCoverageBatch19_targetConsistent :
    sourceCoverageBatch19.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch19_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice19A_targetConsistent,
    sourceCoverageTargetSlice19B_targetConsistent]
theorem sourceCoverageBatch19_length :
    sourceCoverageBatch19.length = 500 := by
  rw [sourceCoverageBatch19_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice19A_length,
    sourceCoverageTargetSlice19B_length]

end SmallCusp
