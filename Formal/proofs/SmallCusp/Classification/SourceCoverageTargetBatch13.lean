import proofs.SmallCusp.Classification.SourceCoverageTargetValidation13A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation13B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch13_eq_targetSlices :
    sourceCoverageBatch13 = sourceCoverageTargetSlice13A ++
      sourceCoverageTargetSlice13B := by
  rfl

theorem sourceCoverageBatch13_targetConsistent :
    sourceCoverageBatch13.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch13_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice13A_targetConsistent,
    sourceCoverageTargetSlice13B_targetConsistent]
theorem sourceCoverageBatch13_length :
    sourceCoverageBatch13.length = 500 := by
  rw [sourceCoverageBatch13_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice13A_length,
    sourceCoverageTargetSlice13B_length]

end SmallCusp
