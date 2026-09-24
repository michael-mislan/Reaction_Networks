import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch21_eq_targetSlices :
    sourceCoverageBatch21 = sourceCoverageTargetSlice21A ++
      sourceCoverageTargetSlice21B := by
  rfl

theorem sourceCoverageBatch21_targetConsistent :
    sourceCoverageBatch21.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch21_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice21A_targetConsistent,
    sourceCoverageTargetSlice21B_targetConsistent]
theorem sourceCoverageBatch21_length :
    sourceCoverageBatch21.length = 500 := by
  rw [sourceCoverageBatch21_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice21A_length,
    sourceCoverageTargetSlice21B_length]

end SmallCusp
