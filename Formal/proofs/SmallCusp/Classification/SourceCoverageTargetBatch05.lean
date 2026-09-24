import proofs.SmallCusp.Classification.SourceCoverageTargetValidation05A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation05B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch05_eq_targetSlices :
    sourceCoverageBatch05 = sourceCoverageTargetSlice05A ++
      sourceCoverageTargetSlice05B := by
  rfl

theorem sourceCoverageBatch05_targetConsistent :
    sourceCoverageBatch05.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch05_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice05A_targetConsistent,
    sourceCoverageTargetSlice05B_targetConsistent]
theorem sourceCoverageBatch05_length :
    sourceCoverageBatch05.length = 500 := by
  rw [sourceCoverageBatch05_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice05A_length,
    sourceCoverageTargetSlice05B_length]

end SmallCusp
