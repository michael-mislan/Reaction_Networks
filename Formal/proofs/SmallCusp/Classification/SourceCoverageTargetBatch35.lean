import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch35_eq_targetSlices :
    sourceCoverageBatch35 = sourceCoverageTargetSlice35A ++
      sourceCoverageTargetSlice35B := by
  rfl

theorem sourceCoverageBatch35_targetConsistent :
    sourceCoverageBatch35.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch35_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice35A_targetConsistent,
    sourceCoverageTargetSlice35B_targetConsistent]
theorem sourceCoverageBatch35_length :
    sourceCoverageBatch35.length = 500 := by
  rw [sourceCoverageBatch35_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice35A_length,
    sourceCoverageTargetSlice35B_length]

end SmallCusp
