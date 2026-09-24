import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch23_eq_targetSlices :
    sourceCoverageBatch23 = sourceCoverageTargetSlice23A ++
      sourceCoverageTargetSlice23B := by
  rfl

theorem sourceCoverageBatch23_targetConsistent :
    sourceCoverageBatch23.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch23_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice23A_targetConsistent,
    sourceCoverageTargetSlice23B_targetConsistent]
theorem sourceCoverageBatch23_length :
    sourceCoverageBatch23.length = 500 := by
  rw [sourceCoverageBatch23_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice23A_length,
    sourceCoverageTargetSlice23B_length]

end SmallCusp
