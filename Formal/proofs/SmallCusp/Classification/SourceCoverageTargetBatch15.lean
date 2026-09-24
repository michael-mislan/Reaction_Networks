import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch15_eq_targetSlices :
    sourceCoverageBatch15 = sourceCoverageTargetSlice15A ++
      sourceCoverageTargetSlice15B := by
  rfl

theorem sourceCoverageBatch15_targetConsistent :
    sourceCoverageBatch15.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch15_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice15A_targetConsistent,
    sourceCoverageTargetSlice15B_targetConsistent]
theorem sourceCoverageBatch15_length :
    sourceCoverageBatch15.length = 500 := by
  rw [sourceCoverageBatch15_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice15A_length,
    sourceCoverageTargetSlice15B_length]

end SmallCusp
