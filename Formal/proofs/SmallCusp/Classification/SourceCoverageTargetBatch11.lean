import proofs.SmallCusp.Classification.SourceCoverageTargetValidation11A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation11B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch11_eq_targetSlices :
    sourceCoverageBatch11 = sourceCoverageTargetSlice11A ++
      sourceCoverageTargetSlice11B := by
  rfl

theorem sourceCoverageBatch11_targetConsistent :
    sourceCoverageBatch11.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch11_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice11A_targetConsistent,
    sourceCoverageTargetSlice11B_targetConsistent]
theorem sourceCoverageBatch11_length :
    sourceCoverageBatch11.length = 500 := by
  rw [sourceCoverageBatch11_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice11A_length,
    sourceCoverageTargetSlice11B_length]

end SmallCusp
