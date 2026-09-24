import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch24_eq_targetSlices :
    sourceCoverageBatch24 = sourceCoverageTargetSlice24A ++
      sourceCoverageTargetSlice24B := by
  rfl

theorem sourceCoverageBatch24_targetConsistent :
    sourceCoverageBatch24.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch24_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice24A_targetConsistent,
    sourceCoverageTargetSlice24B_targetConsistent]
theorem sourceCoverageBatch24_length :
    sourceCoverageBatch24.length = 500 := by
  rw [sourceCoverageBatch24_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice24A_length,
    sourceCoverageTargetSlice24B_length]

end SmallCusp
