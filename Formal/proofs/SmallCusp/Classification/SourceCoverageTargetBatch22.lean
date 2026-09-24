import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch22_eq_targetSlices :
    sourceCoverageBatch22 = sourceCoverageTargetSlice22A ++
      sourceCoverageTargetSlice22B := by
  rfl

theorem sourceCoverageBatch22_targetConsistent :
    sourceCoverageBatch22.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch22_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice22A_targetConsistent,
    sourceCoverageTargetSlice22B_targetConsistent]
theorem sourceCoverageBatch22_length :
    sourceCoverageBatch22.length = 500 := by
  rw [sourceCoverageBatch22_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice22A_length,
    sourceCoverageTargetSlice22B_length]

end SmallCusp
